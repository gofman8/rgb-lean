import Rgb.Lib.Objects
import Rgb.Lib.Error

/-!
# rgb-lib keys

BIP39 mnemonics, BIP32 account keys and master fingerprints (`keys.rs` and the
derivation helpers of the wallet), and the key checks `Wallet::new` makes before
it touches the data directory (`SinglesigKeys::build_descriptors`).

The model holds neither the 2048-word English list nor SHA-256, PBKDF2 or
secp256k1. Word `i` of the list is written `w<i>`. The mnemonic checksum, the
seed and the keys are symbolic values computed from the data they bind. A key is
written as its version prefix (`xpub`, `tpub`, `xprv`, `tprv`) and 16 hex digits
of a fingerprint of its seed and derivation path: distinct keys of a scenario do
not collide in practice, and the model claims no more than that.
-/

namespace Rgb.Lib

/-! ## Witness version -/

/-- Name rgb-lib prints (`Display` uses the `Debug` name). -/
def WitnessVersion.name : WitnessVersion → String
  | .segwitV0 => "SegWitV0"
  | .taproot => "Taproot"

/-- Parse a witness version, ignoring case (`FromStr`). -/
def WitnessVersion.parse (s : String) : Result WitnessVersion :=
  match s.toLower with
  | "segwitv0" => .ok .segwitV0
  | "taproot" => .ok .taproot
  | _ => .error (.invalidWitnessVersion s)

/-! ## BIP39 mnemonics -/

namespace Bip39

/-- Size of the English word list. -/
def listSize : Nat := 2048
/-- Word counts a mnemonic may have (128 to 256 bits of entropy, in steps of 32). -/
def wordCounts : List Nat := [12, 15, 18, 21, 24]
/-- Words of the mnemonic `generate_keys` makes. -/
def generatedWords : Nat := 12

/-- Word `i` of the English list, as the model writes it. -/
def word (i : Nat) : String := s!"w{i}"

/-- Index of a word in the English list (`Language::find_word`). -/
def find? (w : String) : Option Nat :=
  match w.toList with
  | 'w' :: ds => (String.ofList ds).toNat?.bind fun i =>
    if i < listSize && word i == w then some i else none
  | _ => none

/-- Words of a phrase (`split_whitespace`). -/
def splitWords (s : String) : List String :=
  ((s.toList.splitOnP Char.isWhitespace).filter (!·.isEmpty)).map String.ofList

/-- Checksum of `bits` bits of entropy: its first `bits / 32` bits. BIP39 takes them
from SHA-256; the model takes them from a symbolic digest. -/
def checksum (entropy bits : Nat) : Nat :=
  (Digest.of "bip39:checksum" [encode bits, encode entropy]).fingerprint.toNat % 2 ^ (bits / 32)

/-- Words of `bits` bits of `entropy`: the entropy then its checksum, 11 bits a word. -/
def ofEntropy (entropy bits : Nat) : List String :=
  let e := entropy % 2 ^ bits
  let all := e * 2 ^ (bits / 32) + checksum e bits
  let n := (bits + bits / 32) / 11
  (List.range n).map fun i => word ((all >>> (11 * (n - 1 - i))) % listSize)

/-- Why a phrase is not a mnemonic (`bip39::Error`). -/
inductive ParseError where
  | badWordCount (n : Nat)
  | unknownWord (position : Nat)
  | invalidChecksum
  deriving DecidableEq, Repr

/-- Text of the error, as `invalidMnemonic` carries it. -/
def ParseError.message : ParseError → String
  | .badWordCount n =>
    s!"mnemonic has an invalid word count: {n}. Word count must be 12, 15, 18, 21, or 24"
  | .unknownWord i => s!"mnemonic contains an unknown word (word {i})"
  | .invalidChecksum => "the mnemonic has an invalid checksum"

/-- Parse an English mnemonic (`Mnemonic::parse_in`) into its words. -/
def parse (s : String) : Except ParseError (List String) := do
  let ws := splitWords s
  let n := ws.length
  unless wordCounts.contains n do throw (.badWordCount n)
  let idxs ← ws.zipIdx.mapM fun (w, i) =>
    match find? w with
    | some x => pure x
    | none => throw (.unknownWord i)
  let all := idxs.foldl (fun acc x => acc * listSize + x) 0
  let cs := n / 3
  unless all % 2 ^ cs == checksum (all >>> cs) (cs * 32) do throw .invalidChecksum
  return ws

/-- Seed of the words with the empty passphrase (`Mnemonic::to_seed("")`). -/
def seed (words : List String) : Digest :=
  Digest.of "bip39:seed" [encode (" ".intercalate words), encode ""]

end Bip39

/-! ## BIP32 keys -/

namespace Bip32

/-- Network kind of extended keys: `xpub`/`xprv` on mainnet, `tpub`/`tprv` elsewhere. -/
inductive NetworkKind where
  | main
  | test
  deriving DecidableEq, Repr, Inhabited

/-- Network kind of a network (`NetworkKind::from`). -/
def NetworkKind.ofNetwork : BitcoinNetwork → NetworkKind
  | .mainnet => .main
  | _ => .test

/-- Version prefix of public keys. -/
def NetworkKind.pubPrefix : NetworkKind → String
  | .main => "xpub"
  | .test => "tpub"

/-- Version prefix of private keys. -/
def NetworkKind.prvPrefix : NetworkKind → String
  | .main => "xprv"
  | .test => "tprv"

/-- A derivation step. -/
inductive ChildNumber where
  | hardened (i : Nat)
  | normal (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A step as paths write it: hardened steps end in `'`. -/
def ChildNumber.toString : ChildNumber → String
  | .hardened i => s!"{i}'"
  | .normal i => s!"{i}"

/-- Steps of a path, each after a `/` (`/86'/1'/0'`). -/
def pathSteps (p : List ChildNumber) : String := String.join (p.map fun c => "/" ++ c.toString)

/-- Key of the master node of a seed (`Xpriv::new_master`, the same on every network). -/
def masterKey (seed : Digest) : UInt64 := (Digest.of "bip32:master" [encode seed]).fingerprint

/-- Key of a child node. -/
def childKey (k : UInt64) (c : ChildNumber) : UInt64 :=
  (Digest.of "bip32:child" [encode k, encode c.toString]).fingerprint

/-- Key at a path from the master node of a seed. -/
def deriveKey (seed : Digest) (path : List ChildNumber) : UInt64 :=
  path.foldl childKey (masterKey seed)

/-- Fingerprint of a key (the first 4 bytes of `hash160` of the public key). -/
def fingerprint (k : UInt64) : Nat :=
  (Digest.of "bip32:fingerprint" [encode k]).fingerprint.toNat % 2 ^ 32

/-- Fingerprint text: 8 lowercase hex digits. -/
def fingerprintString (fp : Nat) : String := Hex.ofNat fp 8

/-- Parse a fingerprint (`Fingerprint::from_str`): exactly 8 hex digits, either case. -/
def parseFingerprint? (s : String) : Option Nat :=
  if s.length == 8 then Hex.toNat? s else none

/-- An extended public key: network kind and key. -/
structure Xpub where
  kind : NetworkKind
  key : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- Key text: the version prefix and 16 lowercase hex digits. -/
def keyText (prefix_ : String) (k : UInt64) : String := prefix_ ++ Hex.ofNat k.toNat 16

/-- Xpub text (`Display`). -/
def Xpub.toString (x : Xpub) : String := keyText x.kind.pubPrefix x.key

/-- Parse an xpub (`Xpub::from_str`): `xpub` or `tpub` then 16 lowercase hex digits. -/
def Xpub.parse? (s : String) : Option Xpub :=
  let cs := s.toList
  let rest := cs.drop 4
  let kind? : Option NetworkKind :=
    match String.ofList (cs.take 4) with
    | "xpub" => some .main
    | "tpub" => some .test
    | _ => none
  kind?.bind fun kind =>
    if rest.length == 16 && rest.all Hex.isLowerDigit then
      (Hex.toNat? (String.ofList rest)).map fun k => ⟨kind, k.toUInt64⟩
    else none

/-- Text of the `invalidPubkey` error for a string that is not an xpub
(`bip32::Error::Base58`). -/
def xpubParseError : String := "base58 encoding error"

end Bip32

open Bip32

/-! ## Coin types, paths and keychains -/

/-- Coin type of a keychain (`get_coin_type`): colored 827166 on mainnet and 827167
elsewhere, vanilla 0 on mainnet and 1 elsewhere. -/
def coinType (network : BitcoinNetwork) (colored : Bool) : Nat :=
  match network, colored with
  | .mainnet, true => coinRgbMainnet
  | _, true => coinRgbTestnet
  | .mainnet, false => 0
  | _, false => 1

/-- Account path `m/purpose'/coin'/0'`, all steps hardened. -/
def accountPath (wv : WitnessVersion) (coin : Nat) : List ChildNumber :=
  [.hardened wv.purpose, .hardened coin, .hardened account]

/-- Path of a keychain: the account path then the unhardened keychain index. -/
def keychainPath (wv : WitnessVersion) (coin keychain : Nat) : List ChildNumber :=
  accountPath wv coin ++ [.normal keychain]

/-- BDK keychain kinds: the colored keychain is `External`, the vanilla one `Internal`. -/
inductive KeychainKind where
  | external
  | internal
  deriving DecidableEq, Repr, Inhabited

/-! ## Keys -/

/-- Keys `generate_keys` and `restore_keys` return (`Keys`). -/
structure Keys where
  /-- The mnemonic, as given to `restore_keys`. -/
  mnemonic : String
  /-- Master xpub. -/
  xpub : String
  accountXpubVanilla : String
  accountXpubColored : String
  masterFingerprint : String
  witnessVersion : WitnessVersion := .taproot
  deriving DecidableEq, Repr, Inhabited

/-- Account key of mnemonic words (`get_account_data`). -/
def accountXpub (network : BitcoinNetwork) (words : List String) (colored : Bool)
    (wv : WitnessVersion) : Xpub :=
  ⟨.ofNetwork network, deriveKey (Bip39.seed words) (accountPath wv (coinType network colored))⟩

/-- Keys of parsed mnemonic words; `mnemonic` is the text the words came from. -/
def Keys.ofWords (network : BitcoinNetwork) (mnemonic : String) (words : List String)
    (wv : WitnessVersion) : Keys :=
  let master := masterKey (Bip39.seed words)
  { mnemonic, witnessVersion := wv
    xpub := (Xpub.mk (.ofNetwork network) master).toString
    accountXpubVanilla := (accountXpub network words false wv).toString
    accountXpubColored := (accountXpub network words true wv).toString
    masterFingerprint := fingerprintString (fingerprint master) }

/-- `generate_keys`: keys of a new 12-word mnemonic made of 128 bits of `entropy`
(random in rgb-lib, an argument here). It cannot fail. -/
def generateKeys (network : BitcoinNetwork) (wv : WitnessVersion) (entropy : Nat) : Keys :=
  let words := Bip39.ofEntropy entropy 128
  Keys.ofWords network (" ".intercalate words) words wv

/-- `restore_keys`: keys of a mnemonic, which keeps the text as given; a phrase that
does not parse fails with `invalidMnemonic`. -/
def restoreKeys (network : BitcoinNetwork) (mnemonic : String) (wv : WitnessVersion) :
    Result Keys :=
  match Bip39.parse mnemonic with
  | .error e => .error (.invalidMnemonic e.message)
  | .ok words => .ok (Keys.ofWords network mnemonic words wv)

/-! ## Singlesig keys and descriptors -/

/-- Singlesig descriptor of a keychain:
`{wpkh|tr}([fp/purpose'/coin'/0'/keychain]KEY/*)`, where KEY is the account key
derived at the keychain index, private when the mnemonic is known. -/
def singlesigDescriptor (wv : WitnessVersion) (kind : NetworkKind) (fp coin keychain : Nat)
    (accountKey : UInt64) (priv : Bool) : String :=
  let origin := s!"[{fingerprintString fp}{pathSteps (keychainPath wv coin keychain)}]"
  let pre := if priv then kind.prvPrefix else kind.pubPrefix
  s!"{wv.descriptorFn}({origin}{keyText pre (childKey accountKey (.normal keychain))}/*)"

/-- Singlesig keys of `Keys` (`SinglesigKeys::from_keys`). -/
def SinglesigKeys.fromKeys (k : Keys) (vanillaKeychain : Option Nat := none) : SinglesigKeys :=
  { accountXpubVanilla := k.accountXpubVanilla, accountXpubColored := k.accountXpubColored
    vanillaKeychain := vanillaKeychain.getD keychainBtc, masterFingerprint := k.masterFingerprint
    mnemonic := some k.mnemonic, witnessVersion := k.witnessVersion }

/-- Watch-only singlesig keys of `Keys` (`SinglesigKeys::from_keys_no_mnemonic`). -/
def SinglesigKeys.fromKeysNoMnemonic (k : Keys) (vanillaKeychain : Option Nat := none) :
    SinglesigKeys :=
  { SinglesigKeys.fromKeys k vanillaKeychain with mnemonic := none }

/-- Key checks of `Wallet::new` (`SinglesigKeys::build_descriptors`); returns the
descriptors and whether the wallet is watch-only. A parsed xpub takes the wallet's
network kind, and a watch-only fingerprint is not checked against the xpubs. -/
def SinglesigKeys.buildDescriptors (k : SinglesigKeys) (network : BitcoinNetwork) :
    Result (WalletDescriptors × Bool) := do
  let kind := NetworkKind.ofNetwork network
  let some xc := Xpub.parse? k.accountXpubColored | throw (.invalidPubkey xpubParseError)
  let some xv := Xpub.parse? k.accountXpubVanilla | throw (.invalidPubkey xpubParseError)
  let coinC := coinType network true
  let coinV := coinType network false
  let wv := k.witnessVersion
  match k.mnemonic with
  | some m =>
    let words ← match Bip39.parse m with
      | .ok ws => pure ws
      | .error e => throw (.invalidMnemonic e.message)
    let seed := Bip39.seed words
    if deriveKey seed (accountPath wv coinC) != xc.key then throw .invalidBitcoinKeys
    if deriveKey seed (accountPath wv coinV) != xv.key then throw .invalidBitcoinKeys
    let some given := parseFingerprint? k.masterFingerprint | throw .invalidFingerprint
    let fp := fingerprint (masterKey seed)
    if fp != given then throw .fingerprintMismatch
    return ({ colored := singlesigDescriptor wv kind fp coinC keychainRgb xc.key true
              vanilla := singlesigDescriptor wv kind fp coinV k.vanillaKeychain xv.key true },
            false)
  | none =>
    let some fp := parseFingerprint? k.masterFingerprint | throw .invalidFingerprint
    return ({ colored := singlesigDescriptor wv kind fp coinC keychainRgb xc.key false
              vanilla := singlesigDescriptor wv kind fp coinV k.vanillaKeychain xv.key false },
            true)

end Rgb.Lib
