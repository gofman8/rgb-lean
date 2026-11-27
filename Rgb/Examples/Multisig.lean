import Rgb.Lib.Multisig

/-!
# Keys, backups and a multisig group

Key derivation and mnemonics; backup encryption, `backup_info` and restore; then a
2-of-3 multisig group with a watch-only user, run through the hub: an issuance every
wallet processes in order, a send that needs two ACKs, operations discarded by NACKs,
the order rules, addresses, transfer decisions and a restored wallet.
-/

namespace Rgb.Examples.Multisig

open Rgb Rgb.Lib Rgb.Lib.Bip32 Rgb.Lib.Multisig

/-! ## Keys -/

-- coin types: colored 827166 on mainnet and 827167 elsewhere; vanilla 0 and 1
#guard [coinType .mainnet true, coinType .regtest true, coinType .signet true]
  == [827166, 827167, 827167]
#guard [coinType .mainnet false, coinType .testnet false, coinType .testnet4 false] == [0, 1, 1]
-- account paths m/{84|86}'/coin'/0'; a keychain adds an unhardened step
#guard pathSteps (accountPath .taproot (coinType .regtest true)) == "/86'/827167'/0'"
#guard pathSteps (accountPath .segwitV0 (coinType .mainnet false)) == "/84'/0'/0'"
#guard pathSteps (keychainPath .taproot (coinType .testnet false) 3) == "/86'/1'/0'/3"
-- witness versions parse ignoring case, and print as they parse
#guard WitnessVersion.parse "TapRoot" == .ok .taproot
#guard WitnessVersion.parse "segwitv0" == .ok .segwitV0
#guard WitnessVersion.parse "nonsense" == .error (.invalidWitnessVersion "nonsense")
#guard [WitnessVersion.segwitV0, .taproot].all fun wv => WitnessVersion.parse wv.name == .ok wv

def k1 : Keys := generateKeys .regtest .taproot 0x0123456789abcdef0123456789abcdef
def k2 : Keys := generateKeys .regtest .taproot 0xfedcba9876543210fedcba9876543210
def words1 : List String := Bip39.splitWords k1.mnemonic

-- generation makes a 12-word mnemonic, and restoring it gives the same keys
#guard words1.length == Bip39.generatedWords
#guard restoreKeys .regtest k1.mnemonic .taproot == .ok k1
#guard k1.xpub.startsWith "tpub" && k1.masterFingerprint.length == 8

/-- A phrase of `bits` bits of entropy. -/
def phrase (bits : Nat) : String := " ".intercalate (Bip39.ofEntropy 0xfeedfacecafe bits)

-- restore takes 12, 15, 18, 21 or 24 words
#guard [128, 160, 192, 224, 256].map (fun b => (Bip39.splitWords (phrase b)).length)
  == Bip39.wordCounts
#guard [128, 160, 192, 224, 256].all fun b => restoreKeys .regtest (phrase b) .taproot matches .ok _
-- any other word count is refused
#guard restoreKeys .regtest (phrase 128 ++ " w1") .taproot == .error (.invalidMnemonic
  "mnemonic has an invalid word count: 13. Word count must be 12, 15, 18, 21, or 24")
#guard restoreKeys .regtest "" .taproot == .error (.invalidMnemonic
  "mnemonic has an invalid word count: 0. Word count must be 12, 15, 18, 21, or 24")
-- a word outside the English list is refused with its position
#guard restoreKeys .regtest (" ".intercalate (words1.set 3 "w2048")) .taproot
  == .error (.invalidMnemonic "mnemonic contains an unknown word (word 3)")

/-- The words of `k1` with the last word's lowest bit flipped: a checksum bit. -/
def lastFlipped : String :=
  let i := (Bip39.find? (words1.getLastD "")).getD 0
  " ".intercalate (words1.set 11 (Bip39.word (if i % 2 == 0 then i + 1 else i - 1)))

-- the last word carries the checksum
#guard restoreKeys .regtest lastFlipped .taproot
  == .error (.invalidMnemonic "the mnemonic has an invalid checksum")

/-- The words of `k1` with extra whitespace. -/
def spaced : String := "  " ++ "\t ".intercalate words1 ++ " "

-- restore keeps the phrase as given; whitespace does not change the keys
#guard (restoreKeys .regtest spaced .taproot).map (·.mnemonic) == .ok spaced
#guard (restoreKeys .regtest spaced .taproot).map (·.accountXpubColored)
  == .ok k1.accountXpubColored

def k1w : Keys := (restoreKeys .regtest k1.mnemonic .segwitV0).toOption.getD default
def k1m : Keys := (restoreKeys .mainnet k1.mnemonic .taproot).toOption.getD default

-- another witness version: the same master key, other account keys
#guard k1w.xpub == k1.xpub && k1w.masterFingerprint == k1.masterFingerprint
#guard k1w.accountXpubColored != k1.accountXpubColored
  && k1w.accountXpubVanilla != k1.accountXpubVanilla
-- mainnet: the same fingerprint, `xpub` keys, and other account keys (other coin types)
#guard k1m.masterFingerprint == k1.masterFingerprint && k1m.xpub.startsWith "xpub"
#guard (Xpub.parse? k1m.accountXpubColored).map (·.key)
  != (Xpub.parse? k1.accountXpubColored).map (·.key)

/-! ### Key checks of `Wallet::new` -/

def ss1 : SinglesigKeys := .fromKeys k1
def wo1 : SinglesigKeys := .fromKeysNoMnemonic k1

/-- Whether the keys pass, and the wallet is watch-only. -/
def watchOnly? (k : SinglesigKeys) : Result Bool := (k.buildDescriptors .regtest).map (·.2)

#guard watchOnly? ss1 == .ok false
-- with a mnemonic the descriptors carry the private keys and the full origin path
#guard (ss1.buildDescriptors .regtest).map (·.1.colored.startsWith
  s!"tr([{k1.masterFingerprint}/86'/827167'/0'/0]tprv") == .ok true
#guard (ss1.buildDescriptors .regtest).map (·.1.vanilla.startsWith
  s!"tr([{k1.masterFingerprint}/86'/1'/0'/0]tprv") == .ok true
-- account xpubs that are not the mnemonic's
#guard watchOnly? { ss1 with accountXpubColored := k2.accountXpubColored }
  == .error .invalidBitcoinKeys
#guard watchOnly? { ss1 with accountXpubVanilla := k2.accountXpubVanilla }
  == .error .invalidBitcoinKeys
-- a fingerprint that is not the mnemonic's, or not a fingerprint
#guard watchOnly? { ss1 with masterFingerprint := k2.masterFingerprint }
  == .error .fingerprintMismatch
#guard watchOnly? { ss1 with masterFingerprint := "nothex!!" } == .error .invalidFingerprint
-- hex digits of either case
#guard watchOnly? { ss1 with masterFingerprint := k1.masterFingerprint.toUpper } == .ok false
-- an xpub that does not parse, checked before the mnemonic
#guard watchOnly? { ss1 with accountXpubColored := "invalid", mnemonic := some "w1" }
  == .error (.invalidPubkey "base58 encoding error")
#guard watchOnly? { ss1 with mnemonic := some "w1 w2" } == .error (.invalidMnemonic
  "mnemonic has an invalid word count: 2. Word count must be 12, 15, 18, 21, or 24")
-- an xpub of another network takes the wallet's network: there is no network check
#guard watchOnly?
    { ss1 with accountXpubColored := "x" ++ String.ofList (k1.accountXpubColored.toList.drop 1) }
  == .ok false
-- watch-only: the fingerprint must parse, and is not checked against the xpubs
#guard watchOnly? wo1 == .ok true
#guard watchOnly? { wo1 with masterFingerprint := k2.masterFingerprint } == .ok true
#guard watchOnly? { wo1 with masterFingerprint := "xyz" } == .error .invalidFingerprint
#guard (wo1.buildDescriptors .regtest).map (·.1.colored.startsWith
  s!"tr([{k1.masterFingerprint}/86'/827167'/0'/0]tpub") == .ok true

/-! ## Backups -/

def pfx : Bytes := Bytes.ofString "ABCDEFGHIJKLMNOPQRS"
def pub1 : Backup.PubData := { salt := "abcdefghijklmnopqrstuvwx", nonce := "ABCDEFGHIJKLMNOPQRS" }
def key1 : Digest := (Backup.deriveKey "pw" pub1).toOption.getD default
def key2 : Digest := (Backup.deriveKey "other" pub1).toOption.getD default
def plain : Bytes := List.replicate 300 7
def stream : List Backup.SealedChunk := (Backup.encrypt key1 pfx plain).toOption.getD []

-- chunks: 239 plaintext bytes, 255 sealed; the last chunk is shorter, empty for a multiple of 239
#guard Backup.chunkSealed == 255
#guard (Backup.chunks plain).map (·.length) == [239, 61]
#guard (Backup.chunks (List.replicate 478 7)).map (·.length) == [239, 239, 0]
-- the 24-byte nonce: the 19-byte prefix, the position as a big-endian u32, the last-chunk flag
#guard Backup.chunkNonce pfx 258 false == pfx ++ [0, 0, 1, 2, 0]
#guard pub1.noncePrefix? == some pfx
#guard ({ pub1 with nonce := "ABCDEFGHIJKLMNOPQRSTUV" }).noncePrefix? == some pfx
#guard stream.map (·.length) == [255, 77]
#guard stream.map (·.nonce) == [Backup.chunkNonce pfx 0 false, Backup.chunkNonce pfx 1 true]
-- the password's key decrypts; another password fails with wrongPassword
#guard Backup.decrypt key1 pfx stream == .ok plain
#guard Backup.decrypt key2 pfx stream == .error .wrongPassword
-- chunks out of order do not open
#guard Backup.decrypt key1 pfx stream.reverse == .error .wrongPassword
-- a stream cut at a chunk boundary decrypts without an error: no last chunk is checked
#guard Backup.decrypt key1 pfx (stream.take 1) == .ok (plain.take 239)
-- scrypt: the parameters rgb-lib uses are valid, others are refused
#guard ({} : Backup.ScryptParams) == ⟨17, 8, 1, 32⟩ && ({} : Backup.ScryptParams).check == .ok ()
#guard ({ r := 0 } : Backup.ScryptParams).check
  == .error (.internal "invalid params invalid scrypt parameters")
#guard ({ len := 65 } : Backup.ScryptParams).check
  == .error (.internal "invalid params invalid scrypt parameters")

def wdir : String := "/data/a0592f23"
def fs0 : Backup.Fs :=
  [("wallet_manifest.json", "{}"), ("log", "lines"), ("rgb.deleting/old", "old"),
    ("media_files/abcd", "img")].foldl (fun fs (p, c) => fs.write (Backup.join wdir p) (.file c)) {}
def fs1 : Backup.Fs := Backup.recordOperation fs0 wdir 100

-- a fresh wallet needs no backup; after an operation it does
#guard !Backup.backupRequired fs0 wdir && Backup.backupRequired fs1 wdir
-- the archive: the wallet directory first, without the log and the retired RGB store
#guard (Backup.zipDir fs1 wdir).map (·.name) == ["a0592f23/", "a0592f23/media_files/",
  "a0592f23/media_files/abcd", "a0592f23/rgb_lib_db", "a0592f23/wallet_manifest.json"]

def salt : String := "abcdefghijklmnopqrstuvwx"
def nonce : String := "ABCDEFGHIJKLMNOPQRS"
def fs2 : Backup.Fs := (Backup.backup fs1 wdir "/bak/w.rgb" "pw" 200 salt nonce).toOption.getD {}

-- the backup time is set before the archive is made: no backup is required
#guard Backup.readInfo fs2 wdir
  == some { lastBackupTimestamp := 200, lastOperationTimestamp := 100 }
#guard !Backup.backupRequired fs2 wdir
-- a backup onto an existing file, or to a path without a parent, is refused
#guard Backup.backup fs2 wdir "/bak/w.rgb" "pw" 300 salt nonce
  == .error (.fileAlreadyExists "/bak/w.rgb")
#guard Backup.backup fs1 wdir "" "pw" 300 salt nonce
  == .error (.io "provided file path has no parent")

def restored : Backup.Fs × Result Unit := Backup.restoreBackup fs2 "/bak/w.rgb" "pw" "/restore" 9

-- restore brings back the wallet directory and writes its log in the target
#guard restored.2 == .ok ()
#guard (restored.1.below "/restore").map (·.1) == ["/restore/a0592f23",
  "/restore/a0592f23/media_files", "/restore/a0592f23/media_files/abcd",
  "/restore/a0592f23/rgb_lib_db", "/restore/a0592f23/wallet_manifest.json", "/restore/restore_9"]
-- the restored wallet needs no backup until its next operation
#guard !Backup.backupRequired restored.1 "/restore/a0592f23"
#guard Backup.backupRequired (Backup.recordOperation restored.1 "/restore/a0592f23" 300)
  "/restore/a0592f23"

/-- `fs2` with the backup copied to `path`, changed by `f`. -/
def altered (path : String) (f : Backup.Node → Backup.Node) : Backup.Fs :=
  fs2.write path (f ((fs2.get? "/bak/w.rgb").getD .dir))

def version2 : Backup.Node → Backup.Node
  | .backup e (some (.json d)) => .backup e (some (.json { d with version := 2 }))
  | n => n

def cut : Backup.Node → Backup.Node
  | .backup (some s) p => .backup (some (s.take 1)) p
  | n => n

-- restore checks, in order: the backup file, its public data, the version, the password,
-- the decrypted archive, then the wallet directory
#guard (Backup.restoreBackup fs2 "/bak/none.rgb" "pw" "/restore" 9).2
  == .error (.invalidFilePath "/bak/none.rgb")
#guard (Backup.restoreBackup fs2 "/data/a0592f23/log" "pw" "/restore" 9).2
  == .error (.invalidFilePath "/data/a0592f23/log")
#guard (Backup.restoreBackup (altered "/bak/p.rgb" fun _ => .backup none none) "/bak/p.rgb" "pw"
  "/restore" 9).2 == .error (.io Backup.notFound)
#guard (Backup.restoreBackup (altered "/bak/v2.rgb" version2) "/bak/v2.rgb" "bad" "/restore" 9).2
  == .error (.unsupportedBackupVersion "2")
#guard (Backup.restoreBackup fs2 "/bak/w.rgb" "bad" "/data" 9).2 == .error .wrongPassword
#guard (Backup.restoreBackup (altered "/bak/cut.rgb" cut) "/bak/cut.rgb" "pw" "/restore" 9).2
  == .error (.invalidFilePath "/bak/.tmp/backup.zip")
#guard (Backup.restoreBackup fs2 "/bak/w.rgb" "pw" "/data" 9).2
  == .error (.walletDirAlreadyExists "/data/a0592f23")
-- the target directory and the log stay when a check fails
#guard (Backup.restoreBackup fs2 "/bak/none.rgb" "pw" "/r2" 9).1.exists_ "/r2/restore_9"
-- extraction: names that climb out of the target are skipped, absolute ones made relative
#guard [Backup.enclosedName? "../escaped", Backup.enclosedName? "safe/../../escaped_nested",
  Backup.enclosedName? "/absolute", Backup.enclosedName? "safe/./file"]
  == [none, none, some "absolute", some "safe/file"]

/-! ## Multisig keys -/

def kA : Keys := generateKeys .regtest .taproot 0xa1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1
def kB : Keys := generateKeys .regtest .taproot 0xb2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2
def kC : Keys := generateKeys .regtest .taproot 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
def kD : Keys := generateKeys .regtest .taproot 0xd4d4d4d4d4d4d4d4d4d4d4d4d4d4d4d4
def xA : String := kA.accountXpubColored
def xB : String := kB.accountXpubColored
def xC : String := kC.accountXpubColored

def mkeys : MultisigKeys := ⟨[.ofKeys kA, .ofKeys kB, .ofKeys kC], 2, 2⟩
def descs : WalletDescriptors := (mkeys.buildDescriptors .regtest).toOption.getD default
def sorted (l : List String) : List String := l.mergeSort fun a b => decide (a ≤ b)
def coloredKey (k : Keys) : String := multisigKey k.masterFingerprint 827167 k.accountXpubColored 0

-- a cosigner key: the origin always claims purpose 86, then the xpub and the keychain
#guard coloredKey kA == s!"[{kA.masterFingerprint}/86'/827167'/0']{xA}/0/*"
-- tr(NUMS/0/*, multi_a(threshold, keys sorted as strings))
#guard descs.colored == trMultiA numsTpubTestnet 2 (sorted ([kA, kB, kC].map coloredKey))
#guard descs.colored.startsWith
  "tr(tpubD6NzVbkrYhZ4WLczPJWReQycCJdd6YVWXubbVUFnJ5KgU5MDQrD998ZJLSmaB7GVcCnJSDWpr"
-- the cosigners' order does not matter
#guard (MultisigKeys.mk [.ofKeys kC, .ofKeys kA, .ofKeys kB] 2 2).buildDescriptors .regtest
  == .ok descs
-- the vanilla side has its own keychain and threshold
#guard ((MultisigKeys.mk [.ofKeys kA (some 5)] 1 1).buildDescriptors .regtest).map (·.vanilla)
  == .ok (trMultiA numsTpubTestnet 1 [multisigKey kA.masterFingerprint 1 kA.accountXpubVanilla 5])
-- mainnet groups use the mainnet NUMS key
def mainKeys (k : Keys) : Keys := (restoreKeys .mainnet k.mnemonic .taproot).toOption.getD default
#guard ((MultisigKeys.mk [.ofKeys (mainKeys kA)] 1 1).buildDescriptors .mainnet).map
  (·.colored.startsWith ("tr(" ++ numsXpubMainnet ++ "/0/*,multi_a(1,")) == .ok true
-- 1 ≤ threshold ≤ count ≤ 255; the colored threshold is checked first
#guard (MultisigKeys.mk [] 1 1).buildDescriptors .regtest == .error .noCosignersSupplied
#guard (MultisigKeys.mk (List.replicate 256 (.ofKeys kA)) 1 1).buildDescriptors .regtest
  == .error .tooManyCosigners
#guard (MultisigKeys.mk (List.replicate 255 (.ofKeys kA)) 255 1).buildDescriptors .regtest
  matches .ok _
#guard { mkeys with thresholdColored := 0 }.buildDescriptors .regtest
  == .error (.invalidMultisigThreshold 0 3)
#guard { mkeys with thresholdVanilla := 4 }.buildDescriptors .regtest
  == .error (.invalidMultisigThreshold 4 3)
#guard { mkeys with thresholdColored := 5, thresholdVanilla := 0 }.buildDescriptors .regtest
  == .error (.invalidMultisigThreshold 5 3)

/-- The group with cosigner B replaced. -/
def withB (c : Cosigner) : MultisigKeys := { mkeys with cosigners := [.ofKeys kA, c, .ofKeys kC] }

-- a cosigner's fingerprint, xpubs and their network are checked, colored key first
#guard (withB { Cosigner.ofKeys kB with masterFingerprint := "invalid" }).buildDescriptors .regtest
  == .error (.invalidCosigner "invalid master_fingerprint 'invalid'")
#guard (withB { Cosigner.ofKeys kB with accountXpubColored := "invalid" }).buildDescriptors .regtest
  == .error (.invalidCosigner "invalid colored xpub 'invalid'")
#guard (withB { Cosigner.ofKeys kB with accountXpubVanilla := "invalid" }).buildDescriptors .regtest
  == .error (.invalidCosigner "invalid vanilla xpub 'invalid'")
#guard (withB { Cosigner.ofKeys kB with accountXpubColored := (mainKeys kB).accountXpubColored }
  ).buildDescriptors .regtest == .error (.invalidCosigner
    s!"colored xpub '{(mainKeys kB).accountXpubColored}' is for the wrong network")
#guard (withB { Cosigner.ofKeys kB with accountXpubVanilla := (mainKeys kB).accountXpubVanilla }
  ).buildDescriptors .regtest == .error (.invalidCosigner
    s!"vanilla xpub '{(mainKeys kB).accountXpubVanilla}' is for the wrong network")
-- multisig wallets refuse address reuse
def wdata : WalletData :=
  { bitcoinNetwork := .regtest, maxAllocationsPerUtxo := 5, supportedSchemas := [.nia] }
#guard mkeys.checkNewWallet { wdata with addressReuseColoredAuto := true }
  == .error (.unsupportedAddressReuse "multisig wallets don't support it")
#guard (mkeys.checkNewWallet wdata).map (·.2.length) == .ok 8

-- cosigner strings: fingerprint, vanilla xpub, colored xpub, keychain
#guard (Cosigner.ofKeys kA).render
  == s!"{kA.masterFingerprint}:{kA.accountXpubVanilla}:{xA}:0"
#guard Cosigner.parse (Cosigner.ofKeys kA (some 2)).render == .ok (.ofKeys kA (some 2))
#guard Cosigner.parse (Cosigner.ofKeys kA).render == .ok (.ofKeys kA (some 0))
#guard Cosigner.parse "invalid"
  == .error (.invalidCosigner "expected 3 or 4 colon-separated parts, got 1")
#guard Cosigner.parse s!"abcd1234:{kA.accountXpubVanilla}:{xA}"
  == .error (.invalidCosigner "expected 3 or 4 colon-separated parts, got 3")
#guard Cosigner.parse s!"invalid:{kA.accountXpubVanilla}:{xA}:0"
  == .error (.invalidCosigner "invalid master_fingerprint 'invalid'")
#guard Cosigner.parse s!"abcd1234:invalid:{xA}:3"
  == .error (.invalidCosigner "invalid vanilla xpub 'invalid'")
#guard Cosigner.parse s!"abcd1234:{kA.accountXpubVanilla}:invalid:3"
  == .error (.invalidCosigner "invalid colored xpub 'invalid'")
#guard Cosigner.parse s!"abcd1234:{kA.accountXpubVanilla}:{xA}:256"
  == .error (.invalidCosigner "invalid vanilla_keychain value '256'")

/-! ## Operations and the hub's errors -/

#guard [OperationType.createUtxos, .issuance, .sendRgb, .sendBtc, .inflation, .blindReceive,
  .witnessReceive, .burn].map (·.code) == [1, 2, 3, 4, 5, 6, 7, 8]
-- issuances and receives are approved when posted; the others need votes
#guard [OperationType.issuance, .blindReceive, .witnessReceive].all (·.autoApproved)
#guard [OperationType.createUtxos, .sendBtc, .sendRgb, .inflation, .burn].all (!·.autoApproved)
-- bitcoin-only operations need the vanilla threshold, RGB operations the colored one
#guard (OperationType.sendBtc.threshold? 3 2, OperationType.burn.threshold? 3 2,
  OperationType.issuance.threshold? 3 2) == (some 2, some 3, none)
-- hub errors as rgb-lib reports them
#guard (HubError.cannotPost "x").toError == .multisigOperationInProgress
#guard (HubError.cannotRespond "x").toError
  == .multisigCannotRespondToOperation "Cannot respond to operation: x"
#guard (HubError.cannotMark "x").toError
  == .multisigCannotMarkOperationProcessed "Cannot mark operation as processed: x"
#guard HubError.transferStatusMismatch.toError == .multisigTransferStatusMismatch
#guard HubError.unauthorized.toError == .multisigHubService "Missing or invalid credentials"
#guard (HubError.mk "no name provided" "").toError == .multisigHubService "no name provided"

/-! ## A 2-of-3 group with a watch-only user -/

/-- Run a call as party `i` and keep the group. -/
def step (g : Group) (i : Nat) (f : Nat → WalletM α) : Group := (g.call i f).1
/-- The result of a call as party `i`. -/
def out (g : Group) (i : Nat) (f : Nat → WalletM α) : Result α := (g.call i f).2

/-- Cosigners A, B, C (parties 0, 1, 2) and a watch-only user (party 3). -/
def g0 : Group :=
  { hub := .ofKeys mkeys, parties := [{ token := some xA }, { token := some xB },
      { token := some xC }, { token := none }] }

/-- Every wallet of `g` online. -/
def allOnline (g : Group) : Group :=
  (List.range g.parties.length).foldl
    (fun g i => step g i fun _ => goOnline "https://hub.example") g

def g1 : Group := allOnline g0

#guard g1.parties.map (·.role) == [some .cosigner, some .cosigner, some .cosigner, some .watchOnly]
-- going online checks the hub URL, the token and the rgb-lib version
#guard out g0 0 (fun _ => goOnline "ftp://hub.example")
  == .error (.multisigHubService "URL must be valid and start with http:// or https://")
#guard out g0 0 (fun _ => goOnline "https://")
  == .error (.multisigHubService "URL must be valid and start with http:// or https://")
#guard out g0 0 (fun _ => goOnline "https://hub.example" "0.2") == .error (.multisigHubService
  "rgb-lib version mismatch: local version is 0.2 but hub requires 0.3")
#guard out { g0 with parties := [{ token := some kD.accountXpubColored }] } 0
  (fun _ => goOnline "https://hub.example")
  == .error (.multisigHubService "Missing or invalid credentials")
-- an offline wallet cannot sync
#guard out g0 0 syncWithHub == .error .offline

/-! ### An issuance: approved at once, processed by every wallet in order -/

def g2 : Group := step g1 0 (issueAsset "rgb:nia")
def issued : Option OperationInfo := some ⟨1, xA, .issuanceCompleted "rgb:nia"⟩

#guard out g1 0 (issueAsset "rgb:nia") == .ok "rgb:nia"
#guard (g2.hub.operation? 1).map (·.status) == some .approved
#guard (g2.party 0).lastProcessed == 1 && g2.hub.lastProcessed xA == 1
-- B, C and the watch-only user process it on their next sync
#guard [1, 2, 3].all fun i => out g2 i syncWithHub == .ok issued

def g3 : Group := [1, 2, 3].foldl (fun g i => step g i syncWithHub) g2

#guard g3.parties.all fun p => p.lastProcessed == 1 && p.assets == ["rgb:nia"]
-- then they are in sync
#guard out g3 1 syncWithHub == .ok none
-- every cosigner marked it on the hub
#guard [xA, xB, xC].all (g3.hub.lastProcessed · == 1)
#guard out g3 3 (fun _ => hubInfo)
  == .ok { rgbLibVersion := "0.3", lastOperationIdx := some 1, userRole := .watchOnly }

/-! ### A send: two ACKs needed -/

def sendData : BatchTransferData :=
  { transitions := [.transfer], entropy := 7, operationSecretKey := some "0a0b" }
def psbt2 : Psbt := { txid := "tx2" }
def g4 : Group := step g3 0 fun _ => sendInit ⟨psbt2, some sendData⟩

#guard out g3 0 (fun _ => sendInit ⟨psbt2, some sendData⟩) == .ok ⟨"psbt:tx2", 2⟩
#guard (g4.hub.operation? 2).map (·.status) == some .pending
-- the initiator does not count as an ACK
#guard (g4.hub.operation? 2).map (·.votes.all (·.2.ack.isNone)) == some true
-- one pending operation at a time: a second init is refused
#guard out g4 0 (fun _ => createUtxosInit ⟨"tx9", []⟩) == .error .multisigOperationInProgress
#guard out g4 1 (fun _ => sendBtcInit ⟨"tx9", []⟩) == .error .multisigOperationInProgress
-- a watch-only user cannot answer, initiate, take addresses or issue
#guard out g4 3 (respondToOperation 2 .nack) == .error .multisigUserNotCosigner
#guard out g4 3 (fun _ => createUtxosInit ⟨"tx9", []⟩) == .error .multisigUserNotCosigner
#guard out g4 3 getAddress == .error .multisigUserNotCosigner
#guard out g4 3 (issueAsset "rgb:x") == .error .multisigUserNotCosigner

def details2 : OperationDetails :=
  { fasciaPath := cachePath (FileContent.fascia "tx2").fileId, minConfirmations := 1, entropy := 7 }
def status2 (acked nacked : List String) (my : Option Bool) : MultisigVotingStatus :=
  ⟨sorted acked, sorted nacked, 2, my⟩

-- B syncs: the send is to review, with its PSBT and details
#guard out g4 1 syncWithHub
  == .ok (some ⟨2, xA, .toReview .sendRgb "psbt:tx2" (some details2) (status2 [] [] none)⟩)
-- an ACK needs a PSBT with a signature, of the operation's transaction
#guard out g4 1 (respondToOperation 2 (.ack "psbt:tx2"))
  == .error (.invalidPsbt "PSBT has no signatures")
#guard out g4 1 (respondToOperation 2 (.ack (Psbt.sign ⟨"tx8", []⟩ xB).render))
  == .error (.invalidPsbt "PSBT unrelated to operation")
#guard out g4 1 (respondToOperation 2 (.ack "cHNidP8B")) == .error (.invalidPsbt psbtParseError)
#guard out g4 1 (respondToOperation 9 .nack) == .error (.multisigOperationNotFound 9)

def ackB : Nat → WalletM OperationInfo := respondToOperation 2 (.ack (psbt2.sign xB).render)
def ackA : Nat → WalletM OperationInfo := respondToOperation 2 (.ack (psbt2.sign xA).render)
def g5 : Group := step g4 1 ackB

-- B's ACK is one of two: the send stays pending
#guard out g4 1 ackB == .ok ⟨2, xA, .pending .sendRgb (some details2) (status2 [xB] [] (some true))⟩
-- B's sync returns the pending send again; B's sync point stays
#guard out g5 1 syncWithHub
  == .ok (some ⟨2, xA, .pending .sendRgb (some details2) (status2 [xB] [] (some true))⟩)
#guard (step g5 1 syncWithHub |>.party 1).lastProcessed == 1
-- B cannot answer twice
#guard out g5 1 (respondToOperation 2 .nack)
  == .error (.multisigCannotRespondToOperation "already responded")

def g6 : Group := step g5 0 ackA
def done2 (my : Option Bool) : Operation :=
  .completed .sendRgb "tx2" (some details2) (status2 [xA, xB] [] my)

-- A's ACK reaches the threshold: the hub approves, A executes the send and marks it
#guard out g5 0 ackA == .ok ⟨2, xA, done2 (some true)⟩
#guard (g6.hub.operation? 2).map (·.status) == some .approved
#guard (g6.party 0).executed == [(2, "tx2")] && (g6.party 0).lastProcessed == 2
-- the hub lists B's PSBT twice and A's once: three PSBTs to combine
#guard (g6.hub.operation? 2).map (fun op =>
  ((g6.hub.view op none).files.filter (·.fileType == .responsePsbt)).length) == some 3
-- C's NACK after the approval is refused and changes nothing
#guard out g6 2 (respondToOperation 2 .nack)
  == .error (.multisigCannotRespondToOperation "not pending")
#guard (step g6 2 (respondToOperation 2 .nack)).hub == g6.hub
-- B, C and the watch-only user execute the send when they sync
#guard out g6 1 syncWithHub == .ok (some ⟨2, xA, done2 (some true)⟩)
#guard out g6 2 syncWithHub == .ok (some ⟨2, xA, done2 none⟩)
#guard out g6 3 syncWithHub == .ok (some ⟨2, xA, done2 none⟩)

def g7 : Group := [1, 2, 3].foldl (fun g i => step g i syncWithHub) g6

#guard g7.parties.all fun p => p.executed == [(2, "tx2")] && p.lastProcessed == 2
-- every wallet has the send as transfer 2, waiting for its recipient
#guard g7.parties.all (·.status? 2 == some .waitingCounterparty)
-- syncing empties the hub_ops cache; the answer that executed the send leaves it
#guard (g7.party 1).cache.isEmpty && !(g7.party 0).cache.isEmpty

/-! ### NACKs: two of three discard -/

def g8 : Group := step g7 0 fun _ => createUtxosInit ⟨"tx3", []⟩
def g9 : Group := step g8 1 (respondToOperation 3 .nack)
def g10 : Group := step g9 2 (respondToOperation 3 .nack)

#guard out g8 1 (respondToOperation 3 .nack)
  == .ok ⟨3, xA, .pending .createUtxos none (status2 [] [xB] (some false))⟩
-- the second NACK: the ACKs can no longer reach the threshold, the hub discards
#guard out g9 2 (respondToOperation 3 .nack)
  == .ok ⟨3, xA, .discarded .createUtxos none (status2 [] [xB, xC] (some false))⟩
#guard (g10.hub.operation? 3).map (·.status) == some .discarded
-- a cosigner that has not processed every operation cannot initiate
#guard out g10 0 (fun _ => sendBtcInit ⟨"tx9", []⟩) == .error .multisigOperationInProgress
#guard g10.hub.postOperation (.cosigner xA) .sendBtc [(.operationPsbt, .psbt ⟨"tx9", []⟩)] none
  matches .error ⟨"Cannot post new operation: initiator has unprocessed operations", _⟩
-- the initiator skips it when syncing: nothing is executed
#guard out g10 0 syncWithHub
  == .ok (some ⟨3, xA, .discarded .createUtxos none (status2 [] [xB, xC] none)⟩)

def g11 : Group := step g10 0 syncWithHub
def g12 : Group := step g11 0 fun _ => sendBtcInit ⟨"tx4", []⟩

#guard (g11.party 0).executed == [(2, "tx2")] && (g11.party 0).lastProcessed == 3
-- a cosigner answers only the next operation it has to process: B has not processed 3
#guard (g12.hub.operation? 4).map (·.status) == some .pending
#guard out g12 1 (respondToOperation 4 .nack) == .error (.multisigCannotRespondToOperation
  "Cannot respond to operation: operation is not the next one to be processed")

def g13 : Group := step g12 1 syncWithHub

-- once B processed 3 it can answer 4
#guard (g13.party 1).lastProcessed == 3
#guard out g13 1 (respondToOperation 4 .nack) matches .ok _

/-- Operation 4 discarded by B and C; every wallet in sync. -/
def g14 : Group :=
  [(1, 4), (2, 4)].foldl (fun g (i, idx) => step g i (respondToOperation idx .nack)) g13
  |> fun g => [0, 1, 3, 3].foldl (fun g i => step g i syncWithHub) g

#guard g14.parties.all (·.lastProcessed == 4) && g14.hub.lastOperationIdx == some 4
-- the hub refuses to mark a pending operation, or the same one twice, and an ACK without PSBT
#guard g4.hub.markProcessed (.cosigner xB) 2 matches .error
  ⟨"Cannot mark operation as processed: a pending operation cannot be marked as processed", _⟩
#guard g3.hub.markProcessed (.cosigner xB) 1 matches .error
  ⟨"Cannot mark operation as processed: already marked this operation as processed", _⟩
#guard g4.hub.respond (.cosigner xB) 2 true none matches .error
  ⟨"Invalid request: ACK requires PSBT file", _⟩

/-! ### A legacy operation blocks the sync -/

/-- The hub after A posts a send whose data lacks the operation key. -/
def legacyHub : Hub :=
  match g14.hub.postOperation (.cosigner xA) .sendRgb [(.fascia, .fascia "tx5"),
      (.operationData, .batchTransfer { transitions := [.transfer] }),
      (.operationPsbt, .psbt ⟨"tx5", []⟩)] (some "0a0b") with
  | .ok (_, h) => h
  | .error _ => g14.hub

def gL : Group := { g14 with hub := legacyHub }

#guard out gL 1 syncWithHub == .error (.multisigLegacyOperation 5)
-- it is not marked processed, so every sync stops at it
#guard out (step gL 1 syncWithHub) 1 syncWithHub == .error (.multisigLegacyOperation 5)
#guard (step gL 1 syncWithHub |>.party 1).lastProcessed == 4

/-! ### Addresses come from the hub -/

def gA1 : Group := step g14 0 getAddress
def gA2 : Group := step gA1 1 getAddress
def gA3 : Group := step gA2 1 getAddress

-- each cosigner gets a fresh vanilla index
#guard out g14 0 getAddress == .ok "vanilla/0"
#guard out gA1 1 getAddress == .ok "vanilla/1"
#guard (gA1.party 0).vanillaIndex == some 0 && (gA2.party 1).vanillaIndex == some 1
-- having revealed an address, a wallet reveals one index beyond the range it got
#guard out gA2 1 getAddress == .ok "vanilla/2"
#guard (gA3.party 1).vanillaIndex == some 3
-- syncing reveals up to the hub's last reserved index
#guard (step gA3 0 syncWithHub |>.party 0).vanillaIndex == some 2
-- a new address is a change to back up
#guard (gA1.party 0).backupInfo.map (·.lastOperationTimestamp) == some g14.now
#guard g1.hub.bumpAddressIndices (.cosigner xA) 0 true matches .error
  ⟨"Invalid count: must be greater than 0", _⟩

/-! ### Transfer decisions: the first one registered wins -/

def gT1 : Group := step g14 1 (refreshTransfer 2 true)

-- before any decision a watch-only user waits
#guard out g14 3 (refreshTransfer 2 true) == .ok .waitingCounterparty
-- B accepts the send first (its recipient ACKed) and goes on
#guard out g14 1 (refreshTransfer 2 true) == .ok .waitingConfirmations
#guard gT1.hub.transferStatus.lookup 2 == some ⟨xB, true, g14.now⟩
-- C can no longer fail it, and its transfer stays
#guard out gT1 2 (failTransfers 2) == .error .multisigTransferStatusMismatch
#guard (step gT1 2 (failTransfers 2) |>.party 2).status? 2 == some .waitingCounterparty
-- A and the watch-only user follow the acceptance
#guard out gT1 0 (refreshTransfer 2 true) == .ok .waitingConfirmations
#guard out gT1 3 (refreshTransfer 2 true) == .ok .waitingConfirmations

def req : ReceiveRequest :=
  { invoice := "rgb:inv", expirationTimestamp := 2000, transportEndpoints := ["rpcs://proxy"]
    seed := "0c0d" }
def gR : Group := step g14 2 (receive true req)
def gR2 : Group := [0, 1, 3].foldl (fun g i => step g i syncWithHub) gR
def gR3 : Group := step gR2 2 (failTransfers 3)

-- a receive without transport endpoints is refused (no out-of-band exchange)
#guard out g14 2 (receive true { req with transportEndpoints := [] })
  == .error .unsupportedTransportType
-- C's witness receive takes a colored address from the hub; it is approved at once
#guard out g14 2 (receive true req) matches .ok ⟨"rgb:inv", "wvout:colored/0", 2000, 3, _, some _⟩
-- every wallet imports it as transfer 3, with the same receive data
#guard out gR 1 syncWithHub
  matches .ok (some ⟨5, _, .witnessReceiveCompleted ⟨"rgb:inv", _, _, 3, _, _⟩⟩)
#guard gR2.parties.all (·.status? 3 == some .waitingCounterparty)
-- C fails it first: A and the watch-only user then fail it on refresh, ready or not
#guard (gR3.party 2).status? 3 == some .failed
#guard out gR3 0 (refreshTransfer 3 true) == .ok .failed
#guard out gR3 3 (refreshTransfer 3 false) == .ok .failed
-- B's acceptance would now be a mismatch: it must fail the transfer
#guard out gR3 1 (hubAcceptStatus 3) == .ok (some false)

/-! ### A restored wallet resumes at its backup's sync point -/

def dirB : String := "/data/msB"
def fsB : Backup.Fs :=
  let fs := (g7.party 1).walletFs dirB
  (Backup.backup fs dirB "/bak/msB.rgb" "pw" 5000 salt nonce).toOption.getD {}
def fsB2 : Backup.Fs := (Backup.restoreBackup fsB "/bak/msB.rgb" "pw" "/restore" 9).1
def restoredB : Party :=
  { token := some xB, role := some .cosigner, backupInfo := Backup.readInfo fsB2 "/restore/msB" }
def gB : Group := { g14 with parties := g14.parties ++ [restoredB] }

-- the backup holds sync point 2; B went on to 4 afterwards
#guard restoredB.lastProcessed == 2 && (g14.party 1).lastProcessed == 4
-- the restored wallet processes 3 again; marking it again on the hub is fine
#guard out gB 4 syncWithHub
  == .ok (some ⟨3, xA, .discarded .createUtxos none (status2 [] [xB, xC] (some false))⟩)
#guard (step gB 4 syncWithHub |>.party 4).lastProcessed == 3

/-! ### A threshold of 1 -/

def g1of3 : Group :=
  let hub := Hub.ofKeys { mkeys with thresholdColored := 1, thresholdVanilla := 1 }
  step (allOnline { g0 with hub }) 0 fun _ => createUtxosInit ⟨"tx1", []⟩

/-- An ACK of operation 1 signed by `x`. -/
def ack1 (x : String) : Nat → WalletM OperationInfo :=
  respondToOperation 1 (.ack (Psbt.sign ⟨"tx1", []⟩ x).render)

-- the initiator's ACK alone approves, but the hub lists its PSBT once and two are needed:
-- the approved operation cannot be executed
#guard out g1of3 0 (ack1 xA)
  == .error (.multisigUnexpectedData "insufficient PSBTs supplied")
#guard ((step g1of3 0 (ack1 xA)).hub.operation? 1).map (·.status) == some .approved
-- another cosigner's ACK is listed twice, enough to combine
#guard out (step g1of3 1 syncWithHub) 1 (ack1 xB)
  matches .ok ⟨1, _, .completed .createUtxos "tx1" none _⟩

end Rgb.Examples.Multisig
