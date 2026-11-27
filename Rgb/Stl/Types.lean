import Rgb.Bitcoin.Tx

/-!
# Standard types

The strict types that the standard schemas put into global and owned state
(`rgb-ops` `stl`, `rgb-invoicing` `amount`/`data`). Each type states its bounds
as a `valid` check; strict decoding refuses a value that breaks them, so a
consignment carrying such a value fails validation.
-/

namespace Rgb

namespace Charset
def isAlpha (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isAlphaNum (c : Char) : Bool := isAlpha c || isDigit c
def isAlphaSmall (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
/-- ASCII printable: space (0x20) to tilde (0x7E). -/
def isAsciiPrintable (c : Char) : Bool := 0x20 ≤ c.toNat && c.toNat ≤ 0x7E
/-- Characters allowed after the first one in a media type name (`MimeChar`). -/
def isMimeChar (c : Char) : Bool :=
  isAlphaSmall c || isDigit c || "!#$&-^_.+".toList.contains c
end Charset

/-- `RString<First, Rest, MIN, MAX>`: first char class, rest char class, length bounds
in characters. -/
def rstringValid (first rest : Char → Bool) (min max : Nat) (s : String) : Bool :=
  let cs := s.toList
  min ≤ cs.length && cs.length ≤ max &&
    match cs with
    | [] => true
    | c :: tail => first c && tail.all rest

/-- UTF-8 length in bytes (Rust `String::len`). -/
def utf8Len (s : String) : Nat := s.utf8ByteSize

/-- Asset ticker: a letter, then letters or digits; 1 to 8 chars. Compared ignoring case. -/
structure Ticker where
  s : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def Ticker.valid (t : Ticker) : Bool := rstringValid Charset.isAlpha Charset.isAlphaNum 1 8 t.s
/-- Tickers are equal when their upper-case forms are equal. -/
def Ticker.sameAs (a b : Ticker) : Bool := a.s.toUpper == b.s.toUpper

/-- Unicode ticker of a BFA asset: 1 to 8 Unicode characters (counted as characters). -/
structure UnicodeTicker where
  s : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def UnicodeTicker.valid (t : UnicodeTicker) : Bool := 1 ≤ t.s.length && t.s.length ≤ 8

/-- Contract article (CFA): a letter, then letters or digits; 1 to 32 chars. -/
structure Article where
  s : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def Article.valid (a : Article) : Bool := rstringValid Charset.isAlpha Charset.isAlphaNum 1 32 a.s

/-- Asset name: ASCII printable, 1 to 40 chars. -/
structure Name where
  s : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def Name.valid (n : Name) : Bool :=
  rstringValid Charset.isAsciiPrintable Charset.isAsciiPrintable 1 40 n.s

/-- Free text details: any Unicode, 1 to 255 UTF-8 bytes (`NonEmptyString<U8>`). -/
structure Details where
  s : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def Details.valid (d : Details) : Bool := 1 ≤ utf8Len d.s && utf8Len d.s ≤ 255

/-- Decimal precision of an amount: 10^n atoms make one unit, n = 0..18. -/
inductive Precision where
  | indivisible | deci | centi | milli | deciMilli | centiMilli | micro | deciMicro
  | centiMicro | nano | deciNano | centiNano | pico | deciPico | centiPico | femto
  | deciFemto | centiFemto | atto
  deriving DecidableEq, Hashable, Repr, Inhabited

namespace Precision
def all : List Precision :=
  [indivisible, deci, centi, milli, deciMilli, centiMilli, micro, deciMicro, centiMicro, nano,
    deciNano, centiNano, pico, deciPico, centiPico, femto, deciFemto, centiFemto, atto]

/-- Number of decimal digits (the wire value). -/
def decimals (p : Precision) : Nat := (all.idxOf? p).getD 0

/-- The precision with `n` decimals, for `n ≤ 18`. -/
def ofNat? (n : Nat) : Option Precision := all[n]?

/-- Atoms in one unit. -/
def multiplier (p : Precision) : Nat := 10 ^ p.decimals
end Precision

/-- Ricardian contract text (`SmallString`: up to 65535 UTF-8 bytes). -/
structure RicardianContract where
  text : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def RicardianContract.valid (r : RicardianContract) : Bool := utf8Len r.text ≤ 65535

/-- Media type `type/subtype; charset=...`; each name: a lowercase letter, then
lowercase letters, digits or `!#$&-^_.+`; 1 to 64 chars. -/
structure MediaType where
  ty : String
  subtype : Option String
  charset : Option String
  deriving DecidableEq, Hashable, Repr, Inhabited

def MediaType.regNameValid (s : String) : Bool :=
  rstringValid Charset.isAlphaSmall Charset.isMimeChar 1 64 s

def MediaType.valid (m : MediaType) : Bool :=
  regNameValid m.ty && (m.subtype.map regNameValid).getD true && (m.charset.map regNameValid).getD true

/-- Off-chain file referenced by its 32-byte digest. -/
structure Attachment where
  ty : MediaType
  digest : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def Attachment.valid (a : Attachment) : Bool := a.ty.valid

/-- Contract terms: the Ricardian text and an optional attached file. -/
structure ContractTerms where
  text : RicardianContract
  media : Option Attachment
  deriving DecidableEq, Hashable, Repr, Inhabited

def ContractTerms.valid (t : ContractTerms) : Bool :=
  t.text.valid && (t.media.map Attachment.valid).getD true

/-- Media embedded in the contract (`SmallBlob` data). -/
structure EmbeddedMedia where
  ty : MediaType
  data : Bytes
  deriving DecidableEq, Hashable, Repr, Inhabited

def EmbeddedMedia.valid (m : EmbeddedMedia) : Bool := m.ty.valid && m.data.length ≤ 65535

/-- Proof that an output holds reserves backing the asset. -/
structure ProofOfReserves where
  utxo : Outpoint
  proof : Bytes
  deriving DecidableEq, Hashable, Repr, Inhabited

def ProofOfReserves.valid (p : ProofOfReserves) : Bool := p.proof.length ≤ 65535

/-- Asset spec of fungible contracts: ticker, name, details and precision. -/
structure AssetSpec where
  ticker : Ticker
  name : Name
  details : Option Details
  precision : Precision
  deriving DecidableEq, Hashable, Repr, Inhabited

def AssetSpec.valid (s : AssetSpec) : Bool :=
  s.ticker.valid && s.name.valid && (s.details.map Details.valid).getD true

/-- Contract spec of collectible contracts: article, name, details and precision. -/
structure ContractSpec where
  article : Option Article
  name : Name
  details : Option Details
  precision : Precision
  deriving DecidableEq, Hashable, Repr, Inhabited

def ContractSpec.valid (s : ContractSpec) : Bool :=
  (s.article.map Article.valid).getD true && s.name.valid && (s.details.map Details.valid).getD true

/-- Index of a token of a unique-asset contract. -/
structure TokenIndex where
  v : UInt32
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Data of one non-fungible token (UDA): up to 20 attachments keyed by `u8`. -/
structure TokenData where
  index : TokenIndex
  ticker : Option Ticker := none
  name : Option Name := none
  details : Option Details := none
  preview : Option EmbeddedMedia := none
  media : Option Attachment := none
  attachments : List (UInt8 × Attachment) := []
  reserves : Option ProofOfReserves := none
  deriving DecidableEq, Hashable, Repr, Inhabited

def TokenData.valid (t : TokenData) : Bool :=
  (t.ticker.map Ticker.valid).getD true && (t.name.map Name.valid).getD true &&
  (t.details.map Details.valid).getD true && (t.preview.map EmbeddedMedia.valid).getD true &&
  (t.media.map Attachment.valid).getD true && t.attachments.length ≤ 20 &&
  (t.attachments.map (·.1)).eraseDups.length == t.attachments.length &&
  t.attachments.all (·.2.valid) && (t.reserves.map ProofOfReserves.valid).getD true

/-- URL of a reject list: ASCII printable, 1 to 8000 chars. -/
structure RejectListUrl where
  s : String
  deriving DecidableEq, Hashable, Repr, Inhabited

def RejectListUrl.valid (u : RejectListUrl) : Bool :=
  rstringValid Charset.isAsciiPrintable Charset.isAsciiPrintable 1 8000 u.s

/-- 20-byte EVM account or contract address. -/
structure EvmAddress where
  bytes : Bytes
  deriving DecidableEq, Hashable, Repr, Inhabited

def EvmAddress.valid (a : EvmAddress) : Bool := a.bytes.length == 20

/-- A contract on an EVM chain, by EIP-155 chain id and address. -/
structure EvmContract where
  chainId : UInt64
  address : EvmAddress
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Where a bridged asset's bridge contract lives. -/
inductive BridgeLocation where
  | evm (c : EvmContract)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Where a reject list is published. -/
inductive RejectListLocation where
  | url (u : RejectListUrl)
  | evm (c : EvmContract)
  deriving DecidableEq, Hashable, Repr, Inhabited

def RejectListLocation.valid : RejectListLocation → Bool
  | .url u => u.valid
  | .evm c => c.address.valid

/-- Block number on the bridged chain. -/
structure BlockNumber where
  v : UInt64
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- 32-byte commitment to the reason for a burn. -/
structure BurnReason where
  bytes : Bytes
  deriving DecidableEq, Hashable, Repr, Inhabited

def BurnReason.valid (r : BurnReason) : Bool := r.bytes.length == 32

/-- Proofs attached to a burn. -/
structure BurnMeta where
  burnProofs : List ProofOfReserves
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Reserves attached to an issuance. -/
structure IssueMeta where
  reserves : List ProofOfReserves
  deriving DecidableEq, Hashable, Repr, Inhabited

end Rgb
