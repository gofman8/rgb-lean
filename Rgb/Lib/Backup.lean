import Rgb.Lib.Db
import Rgb.Lib.Keys

/-!
# rgb-lib backups

`backup`, `backup_info` and `restore_backup` (`wallet/backup.rs`).

A backup file is a zip archive of two files: `backup.pub_data`, the public data
(scrypt parameters, salt, nonce prefix, version) as JSON, and `backup.enc`, the
encrypted zip of the wallet directory. The key is scrypt of the password with the
salt. The cipher is XChaCha20-Poly1305 over chunks of 239 plaintext bytes; chunk
`i` is sealed with a 24-byte nonce made of the 19-byte nonce prefix, `i` as a
big-endian `u32` and a last-chunk flag. The model keeps the chunks and nonces
exactly and makes the cipher symbolic: a sealed chunk opens only with the key and
nonce it was sealed with, so a wrong password fails with `wrongPassword`.

The file system is a map from absolute paths to nodes. Of the wallet database the
model keeps the `backup_info` row, written as text in the database file.
-/

namespace Rgb.Lib.Backup

/-! ## Constants and names -/

/-- Plaintext bytes of a full chunk (`BACKUP_BUFFER_LEN_ENCRYPT`). -/
def chunkPlain : Nat := 239
/-- Bytes of the Poly1305 tag of each chunk. -/
def tagLength : Nat := 16
/-- Sealed bytes of a full chunk (`BACKUP_BUFFER_LEN_DECRYPT`). -/
def chunkSealed : Nat := chunkPlain + tagLength
/-- Characters of the random alphanumeric salt. -/
def saltLength : Nat := 24
/-- Highest chunk position (`u32::MAX`). -/
def maxPosition : Nat := 4294967295

/-- Encrypted wallet archive inside a backup. -/
def encFile : String := "backup.enc"
/-- Public data inside a backup. -/
def pubDataFile : String := "backup.pub_data"
/-- Decrypted wallet archive in the temporary directory. -/
def zipFile : String := "backup.zip"
/-- Wallet database file (`rgb_lib_db`). -/
def dbFile : String := "rgb_lib_db"
/-- Temporary directory the model uses where rgb-lib makes a random one. -/
def tempDir : String := ".tmp"
/-- Text of the `io` error for a missing file (`ErrorKind::NotFound`). -/
def notFound : String := "No such file or directory (os error 2)"
/-- Model text of the `internal` error for public data that is not JSON (serde's text). -/
def notJson : String := "backup.pub_data is not valid JSON"
/-- Model text of the `internal` error for a nonce shorter than 19 bytes (rgb-lib panics). -/
def shortNonce : String := "backup nonce shorter than 19 bytes"

/-! ## Key derivation -/

/-- scrypt parameters (`ScryptParams`); the defaults are the only ones rgb-lib uses. -/
structure ScryptParams where
  logN : Nat := scryptLogN
  r : Nat := scryptR
  p : Nat := scryptP
  len : Nat := backupKeyLength
  deriving DecidableEq, Repr, Inhabited

/-- `Params::new_with_output_len`: `len` in 10..64, `r` and `p` positive, `log_n` below
64, `r * 128 * 2^log_n` within 64 bits and `r * p` below 2^30. -/
def ScryptParams.check (sp : ScryptParams) : Result Unit :=
  if 10 ≤ sp.len ∧ sp.len ≤ 64 ∧ 0 < sp.r ∧ 0 < sp.p ∧ sp.logN < 64 ∧
      sp.r * 128 * 2 ^ sp.logN < 2 ^ 64 ∧ sp.r * sp.p < 2 ^ 30 then .ok ()
  else .error (.internal "invalid params invalid scrypt parameters")

/-- Public data of a backup (`BackupPubData`). -/
structure PubData where
  scryptParams : ScryptParams := {}
  salt : String
  nonce : String
  version : Nat := backupVersion
  deriving DecidableEq, Repr, Inhabited

/-- Content of `backup.pub_data`: JSON of the public data, or text that is not. -/
inductive PubDataText where
  | json (d : PubData)
  | other (text : String)
  deriving DecidableEq, Repr, Inhabited

/-- Key of a password (`get_cypher_secrets`): scrypt with the salt, symbolic. The salt is
taken as well-formed, as rgb-lib writes it. -/
def deriveKey (password : String) (d : PubData) : Result Digest := do
  d.scryptParams.check
  let sp := d.scryptParams
  return Digest.of "scrypt" [encode password, encode d.salt, encode sp.logN, encode sp.r,
    encode sp.p, encode sp.len]

/-- Nonce prefix: the first 19 bytes of the nonce text (`BackupPubData::nonce`). -/
def PubData.noncePrefix? (d : PubData) : Option Bytes :=
  let b := Bytes.ofString d.nonce
  if b.length < backupNonceLength then none else some (b.take backupNonceLength)

/-! ## Chunked encryption -/

/-- Big-endian bytes of `n` in `width` bytes. -/
def be (n width : Nat) : Bytes := (Bytes.le n width).reverse

/-- Nonce of a chunk (`stream_be32_nonce`): the prefix, the position as a big-endian
`u32` and the last-chunk flag. -/
def chunkNonce (pfx : Bytes) (position : Nat) (last : Bool) : Bytes :=
  pfx ++ be position 4 ++ [if last then 1 else 0]

/-- A chunk sealed with XChaCha20-Poly1305 (symbolic): the key and nonce it was sealed
with, and its plaintext. -/
structure SealedChunk where
  key : Digest
  nonce : Bytes
  plain : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- Sealed length: the plaintext and the tag. -/
def SealedChunk.length (c : SealedChunk) : Nat := c.plain.length + tagLength

/-- The plaintext, only for the key and nonce the chunk was sealed with. -/
def SealedChunk.open? (c : SealedChunk) (key : Digest) (nonce : Bytes) : Option Bytes :=
  if c.key == key && c.nonce == nonce then some c.plain else none

/-- Chunks of the plaintext; the last one is shorter, and empty for a multiple of 239. -/
def chunks (plain : Bytes) : List Bytes := go (plain.length / chunkPlain + 1) plain
where
  go : Nat → Bytes → List Bytes
    | 0, b => [b]
    | fuel + 1, b =>
      if b.length < chunkPlain then [b] else b.take chunkPlain :: go fuel (b.drop chunkPlain)

/-- Encrypt (`encrypt_file`): chunk `i` sealed at position `i`, the last one flagged. -/
def encrypt (key : Digest) (pfx : Bytes) (plain : Bytes) : Result (List SealedChunk) :=
  let cs := chunks plain
  if cs.length > maxPosition + 1 then .error (.internal "backup file too large")
  else .ok (cs.zipIdx.map fun (c, i) => ⟨key, chunkNonce pfx i (i + 1 == cs.length), c⟩)

/-- Decrypt (`decrypt_file`), reading 255-byte blocks: a full block is a non-last chunk, a
shorter one the last. A stream cut at a block boundary ends without any last chunk
checked, and data after a short block is ignored. -/
def decrypt (key : Digest) (pfx : Bytes) (stream : List SealedChunk) : Result Bytes :=
  go 0 stream
where
  go (pos : Nat) : List SealedChunk → Result Bytes
    | [] => .ok []
    | c :: rest =>
      if c.length == chunkSealed then
        if pos == maxPosition then .error (.internal "backup file too large") else
        match c.open? key (chunkNonce pfx pos false) with
        | none => .error .wrongPassword
        | some b => (go (pos + 1) rest).map (b ++ ·)
      else
        match c.open? key (chunkNonce pfx pos true) with
        | none => .error .wrongPassword
        | some b => .ok b

/-! ## Archives -/

/-- An entry of a zip archive: a directory (its name ends in `/`) or a file. -/
structure Entry where
  name : String
  /-- File content; `none` for a directory. -/
  content : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- One line of the archive text the model encrypts. -/
def Entry.render (e : Entry) : String :=
  match e.content with
  | none => "D " ++ Hex.ofBytes (Bytes.ofString e.name)
  | some c => "F " ++ Hex.ofBytes (Bytes.ofString e.name) ++ " " ++ Hex.ofBytes (Bytes.ofString c)

/-- Bytes of a zip archive (the model's text form). -/
def zipBytes (es : List Entry) : Bytes :=
  Bytes.ofString ("ZIP\n" ++ "\n".intercalate (es.map (·.render)))

private def textOfHex? (h : String) : Option String :=
  (Hex.toBytes? h).bind fun b => String.fromUTF8? ⟨b.toArray⟩

/-- An entry of one line of archive text. -/
def Entry.parse? (l : String) : Option Entry :=
  match l.splitOn " " with
  | ["D", n] => (textOfHex? n).map fun name => { name }
  | ["F", n, c] => do
    let name ← textOfHex? n
    let content ← textOfHex? c
    return { name, content := some content }
  | _ => none

/-- Entries of zip archive bytes; `none` when the bytes are not an archive. -/
def unzipBytes? (b : Bytes) : Option (List Entry) := do
  let text ← String.fromUTF8? ⟨b.toArray⟩
  match (text.splitOn "\n").filter (· ≠ "") with
  | "ZIP" :: lines => lines.mapM Entry.parse?
  | _ => none

/-- Path an entry extracts to (`enclosed_name`), with `/` and `\` as separators; `none`
(the entry is skipped) for a name holding NUL or climbing above the target. -/
def enclosedName? (name : String) : Option String :=
  if name.contains (Char.ofNat 0) then none else
  let parts := (name.toList.splitOnP fun c => c == '/' || c == '\\').map String.ofList
  let step (acc : Option (List String)) (p : String) : Option (List String) := acc.bind fun st =>
    if p == "" || p == "." then some st
    else if p == ".." then (if st.isEmpty then none else some st.dropLast)
    else some (st ++ [p])
  (parts.foldl step (some [])).map ("/".intercalate ·)

/-! ## Model file system -/

/-- A node of the model file system. -/
inductive Node where
  | dir
  | file (content : String)
  /-- A backup file: a zip of `backup.enc` and `backup.pub_data`, either may miss. -/
  | backup (enc : Option (List SealedChunk)) (pubData : Option PubDataText)
  deriving DecidableEq, Repr, Inhabited

/-- Nodes by absolute path, written without a trailing `/`. -/
structure Fs where
  nodes : OrdMap String Node := {}
  deriving DecidableEq, Repr, Inhabited

/-- A path without its trailing `/` (the root stays `/`). -/
def norm (p : String) : String :=
  let cs := p.toList
  if cs.length > 1 && cs.getLast? == some '/' then String.ofList cs.dropLast else p

/-- `dir` joined with `name` (`Path::join`). -/
def join (dir name : String) : String := if dir == "/" then "/" ++ name else dir ++ "/" ++ name

/-- Parent of a path (`Path::parent`): `none` for the root and the empty path. -/
def parent? (p : String) : Option String :=
  let cs := (norm p).toList
  if cs.isEmpty || cs == ['/'] then none else
  match (cs.reverse.dropWhile (· ≠ '/')).reverse with
  | [] => some ""
  | ['/'] => some "/"
  | d => some (String.ofList d.dropLast)

/-- Last component of a path. -/
def baseName (p : String) : String := (((norm p).splitOn "/").getLast?).getD ""

namespace Fs

/-- The node at a path. -/
def get? (fs : Fs) (p : String) : Option Node := fs.nodes.find? (norm p)
/-- Whether a path exists (`Path::exists`). -/
def exists_ (fs : Fs) (p : String) : Bool := fs.nodes.contains (norm p)

/-- Create a directory and its missing ancestors (`create_dir_all`). -/
def mkdirAll (fs : Fs) (p : String) : Fs :=
  let rec up : Nat → String → List String
    | 0, _ => []
    | n + 1, q => q :: ((parent? q).filter (· ≠ "")).elim [] (up n)
  (up (p.length + 1) (norm p)).foldl
    (fun fs d => if fs.exists_ d then fs else ⟨fs.nodes.insert d .dir⟩) fs

/-- Write a node, creating the parent directories. -/
def write (fs : Fs) (p : String) (n : Node) : Fs :=
  let fs := match parent? p with
    | some d => if d == "" then fs else fs.mkdirAll d
    | none => fs
  ⟨fs.nodes.insert (norm p) n⟩

/-- Nodes strictly below a directory, by path. -/
def below (fs : Fs) (dir : String) : List (String × Node) :=
  let pre := if norm dir == "/" then "/" else norm dir ++ "/"
  fs.nodes.toList.filter fun (q, _) => q.startsWith pre

end Fs

/-! ## The `backup_info` row -/

/-- `backup_info()`: a backup is required when the row exists and the last operation is
later than the last backup. -/
def required : Option DbBackupInfo → Bool
  | none => false
  | some i => i.lastOperationTimestamp > i.lastBackupTimestamp

/-- `update_backup_info_with_op_idx`: a backup sets the backup time, any other change
the operation time; without an operation index the stored one stays. -/
def update (row : Option DbBackupInfo) (doingBackup : Bool) (now : Nat)
    (opIdx : Option Nat := none) : DbBackupInfo :=
  let r := row.getD {}
  let r := if doingBackup then { r with lastBackupTimestamp := now }
    else { r with lastOperationTimestamp := now }
  match opIdx with
  | some i => { r with lastProcessedOperationIdx := some i }
  | none => r

/-- The row as the model writes it in the database file. -/
def renderInfo (i : DbBackupInfo) : String :=
  let idx := match i.lastProcessedOperationIdx with
    | some n => toString n
    | none => "-"
  s!"backup_info {i.lastBackupTimestamp} {i.lastOperationTimestamp} {idx}"

/-- The row of database file text; `none` for a database without it. -/
def parseInfo? (s : String) : Option DbBackupInfo :=
  match s.splitOn " " with
  | ["backup_info", b, o, idx] => do
    let lastBackupTimestamp ← b.toNat?
    let lastOperationTimestamp ← o.toNat?
    let lastProcessedOperationIdx ← if idx == "-" then some none else idx.toNat?.map some
    return { lastBackupTimestamp, lastOperationTimestamp, lastProcessedOperationIdx }
  | _ => none

/-- The `backup_info` row of a wallet directory. -/
def readInfo (fs : Fs) (walletDir : String) : Option DbBackupInfo :=
  match fs.get? (join walletDir dbFile) with
  | some (.file t) => parseInfo? t
  | _ => none

/-- Write the `backup_info` row of a wallet directory. -/
def writeInfo (fs : Fs) (walletDir : String) (i : DbBackupInfo) : Fs :=
  fs.write (join walletDir dbFile) (.file (renderInfo i))

/-- `backup_info()` of a wallet directory. -/
def backupRequired (fs : Fs) (walletDir : String) : Bool := required (readInfo fs walletDir)

/-- Record a state change in a wallet directory (`update_backup_info(false)`). -/
def recordOperation (fs : Fs) (walletDir : String) (now : Nat) (opIdx : Option Nat := none) : Fs :=
  writeInfo fs walletDir (update (readInfo fs walletDir) false now opIdx)

/-! ## `backup` -/

/-- Entries of a wallet directory archive (`zip_dir` keeping the directory's name): the
directory first, then what is below it in path order. -/
def zipDir (fs : Fs) (walletDir : String) : List Entry :=
  let base := baseName walletDir
  let dirLen := (norm walletDir).length
  let rel (q : String) : String := base ++ String.ofList (q.toList.drop dirLen)
  let entry : String × Node → Option Entry
    | (q, .dir) => some { name := rel q ++ "/" }
    | (q, .file c) =>
      if baseName q == logFile then none else some { name := rel q, content := some c }
    | (_, .backup _ _) => none
  let kept := (fs.below walletDir).filter fun (q, _) =>
    !(((rel q).splitOn "/").contains rgbRuntimeDeletingDir)
  if base == rgbRuntimeDeletingDir then [] else { name := base ++ "/" } :: kept.filterMap entry

/-- `backup(backup_path, password)`. The backup time is set before the archive is made,
so the archive holds it; on error it is reset. `salt` and `nonce` stand for the random
alphanumeric characters rgb-lib draws. -/
def backup (fs : Fs) (walletDir backupPath password : String) (now : Nat) (salt nonce : String) :
    Result Fs := do
  let fs := writeInfo fs walletDir (update (readInfo fs walletDir) true now)
  if fs.exists_ backupPath then throw (.fileAlreadyExists backupPath)
  let some dir := parent? backupPath | throw (.io "provided file path has no parent")
  let fs := if dir == "" then fs else fs.mkdirAll dir
  let pub : PubData := { salt, nonce }
  let key ← deriveKey password pub
  let some pfx := pub.noncePrefix? | throw (.internal shortNonce)
  let stream ← encrypt key pfx (zipBytes (zipDir fs walletDir))
  return fs.write backupPath (.backup (some stream) (some (.json pub)))

/-! ## `restore_backup` -/

/-- `restore_backup(backup_path, password, target_dir)`. The target directory and its
`restore_<unix time>` log are made first and stay when a check fails; the wallet
directory is named by the first entry of the decrypted archive. -/
def restoreBackup (fs : Fs) (backupPath password targetDir : String) (nowSecs : Nat) :
    Fs × Result Unit :=
  let fs := fs.mkdirAll targetDir
  let fs := fs.write (join targetDir s!"restore_{nowSecs}") (.file "")
  match parent? backupPath with
  | none => (fs, .error (.io "provided file path has no parent"))
  | some dir =>
  let fs := if dir == "" then fs else fs.mkdirAll dir
  let checked : Result (List Entry) := do
    let some (.backup enc pubText) := fs.get? backupPath | throw (.invalidFilePath backupPath)
    let some pubText := pubText | throw (.io notFound)
    let .json pub := pubText | throw (.internal notJson)
    if pub.version != backupVersion then throw (.unsupportedBackupVersion (toString pub.version))
    let key ← deriveKey password pub
    let some pfx := pub.noncePrefix? | throw (.internal shortNonce)
    let some stream := enc | throw (.io notFound)
    let plain ← decrypt key pfx stream
    let some entries := unzipBytes? plain
      | throw (.invalidFilePath (join (join dir tempDir) zipFile))
    let name := ((entries.head?.map (·.name)).getD "").replace "/" ""
    let walletDir := join targetDir name
    if fs.exists_ walletDir then throw (.walletDirAlreadyExists walletDir)
    return entries
  match checked with
  | .error e => (fs, .error e)
  | .ok entries =>
    let unzip (fs : Fs) (e : Entry) : Fs :=
      match enclosedName? e.name with
      | none => fs
      | some rel =>
        match e.content with
        | none => fs.mkdirAll (join targetDir rel)
        | some c => fs.write (join targetDir rel) (.file c)
    (entries.foldl unzip fs, .ok ())

end Rgb.Lib.Backup
