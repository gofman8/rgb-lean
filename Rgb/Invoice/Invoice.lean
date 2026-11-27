import Rgb.Invoice.Amount
import Rgb.Consensus.Operation
import Rgb.Lib.Error
import Rgb.Lib.Objects

/-!
# RGB invoices

An RGB invoice asks a payer to send state to a beneficiary. It is an `rgb:` URI
with four path segments (contract, schema, requested state, beneficiary) and
options as query parameters (`rgb-invoicing` `invoice`, `parse` and `builder`).
This module states the invoice data, its text form, the parser with each error
in the order the library checks for it, and the builder. Then it states
rgb-lib's invoice layer: the data rgb-lib reads from an invoice, the assignment
each schema accepts, recipient ids and transport endpoints.

Contract ids, schema ids, concealed seals and witness outputs are written in
Baid64 with a checksum, and an x-only key must be a point of secp256k1: the
model computes neither, so the parser and the printer take an `IdCodec` that
reads and writes these texts. The URI check (RFC 3986) is a check of the
characters of each part of the URI.
-/

namespace Rgb.Invoice

/-! ## Text helpers -/

/-- ASCII hex digit of either case. -/
def isHexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Value of a hex digit. -/
def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Lower-case hex digit of a value below 16. -/
def hexDigitChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Lower-case hex of bytes (`ToHex`). -/
def hexOf (bs : Bytes) : String :=
  String.join (bs.map fun b =>
    String.ofList [hexDigitChar (b.toNat / 16), hexDigitChar (b.toNat % 16)])

/-- Bytes of hex text of either case; `none` for an odd length or a non-hex character. -/
def ofHex? (s : String) : Option Bytes :=
  let cs := s.toList
  if cs.length % 2 != 0 || !cs.all isHexDigit then none
  else some ((chunksOf 2 cs).map fun p =>
    (16 * hexValue (p.headD '0') + hexValue (p.getLastD '0')).toUInt8)

/-- `s` for a transport with TLS. -/
def tlsSuffix (tls : Bool) : String := if tls then "s" else ""

/-! ## Transports -/

/-- Where the payer posts the consignment (`RgbTransport`). -/
inductive RgbTransport where
  | jsonRpc (tls : Bool) (host : String)
  | restHttp (tls : Bool) (host : String)
  | webSockets (tls : Bool) (host : String)
  | storm
  deriving DecidableEq, Repr, Inhabited

/-- Why transport text is refused (`TransportParseError`). -/
inductive TransportParseError where
  | invalidTransport (s : String)
  | invalidTransportHost (s : String)
  deriving DecidableEq, Repr

/-- Display text of the error. -/
def TransportParseError.message : TransportParseError → String
  | .invalidTransport s => s!"invalid transport {s}."
  | .invalidTransportHost s => s!"invalid transport host {s}."

namespace RgbTransport

/-- Text: `rpc[s]://host`, `http[s]://host`, `ws[s]://host` or `storm://_/`. -/
def display : RgbTransport → String
  | jsonRpc tls host => "rpc" ++ tlsSuffix tls ++ "://" ++ host
  | restHttp tls host => "http" ++ tlsSuffix tls ++ "://" ++ host
  | webSockets tls host => "ws" ++ tlsSuffix tls ++ "://" ++ host
  | storm => "storm://_/"

/-- Read a transport (`RgbTransport::from_str`): split at the first `://`; an empty host
is refused before the scheme is read; schemes are case-sensitive; the host is not checked,
and `storm` drops it. -/
def parse (s : String) : Except TransportParseError RgbTransport :=
  match splitOnce s "://" with
  | none => .error (.invalidTransport s)
  | some (ty, host) =>
    if host.isEmpty then .error (.invalidTransportHost host)
    else match ty with
      | "rpc" => .ok (jsonRpc false host)
      | "rpcs" => .ok (jsonRpc true host)
      | "http" => .ok (restHttp false host)
      | "https" => .ok (restHttp true host)
      | "ws" => .ok (webSockets false host)
      | "wss" => .ok (webSockets true host)
      | "storm" => .ok storm
      | _ => .error (.invalidTransport s)

end RgbTransport

/-! ## Chains and beneficiaries -/

/-- Address network of a chain (`KnownHrp`). -/
inductive KnownHrp where
  | mainnet
  | testnets
  | regtest
  deriving DecidableEq, Repr

/-- Data bound to a chain and network (`XChainNet<T>`, one variant per `ChainNet`; its
`with` is the constructor, `chain_network` and `into_inner` the fields). -/
structure XChainNet (α : Type) where
  chainNet : ChainNet
  inner : α
  deriving DecidableEq, Repr

namespace XChainNet
variable {α : Type}

/-- Layer 1 of the chain. -/
def layer1 (x : XChainNet α) : Layer1 := x.chainNet.layer1

/-- Liquid uses the Bitcoin address networks. -/
def addressNetwork (x : XChainNet α) : KnownHrp :=
  match x.chainNet with
  | .bitcoinMainnet | .liquidMainnet => .mainnet
  | .bitcoinRegtest => .regtest
  | _ => .testnets

end XChainNet

/-- A BIP 340 x-only public key, as its 32 bytes. -/
structure XOnlyKey where
  bytes : Bytes
  deriving DecidableEq, Repr, Inhabited

/-- What an output script pays to (`AddressPayload`). -/
inductive AddressPayload where
  /-- P2PKH: 20-byte key hash. -/
  | pkh (hash : Bytes)
  /-- P2SH: 20-byte script hash. -/
  | sh (hash : Bytes)
  /-- P2WPKH: 20-byte key hash. -/
  | wpkh (hash : Bytes)
  /-- P2WSH: 32-byte script hash. -/
  | wsh (hash : Bytes)
  /-- P2TR: 32-byte output key. -/
  | tr (outputKey : XOnlyKey)
  deriving DecidableEq, Repr, Inhabited

/-- An output of the payer's witness transaction that pays the beneficiary (`Pay2Vout`). -/
structure Pay2Vout where
  payload : AddressPayload
  deriving DecidableEq, Repr, Inhabited

/-- Why a 33-byte payload is not a `Pay2Vout` (`Pay2VoutError`). -/
inductive Pay2VoutError where
  | invalidAddressType (b : UInt8)
  | invalidTapkey
  deriving DecidableEq, Repr

/-- Display text of the error. -/
def Pay2VoutError.message : Pay2VoutError → String
  | .invalidAddressType b => s!"unexpected address type byte 0x{hexOf [b]}."
  | .invalidTapkey => "invalid taproot output key"

namespace Pay2Vout

/-- Address type byte: P2PKH 1, P2SH 2, P2WPKH 3, P2WSH 4, P2TR 5. -/
def typeByte : AddressPayload → UInt8
  | .pkh _ => 1 | .sh _ => 2 | .wpkh _ => 3 | .wsh _ => 4 | .tr _ => 5

/-- The 33-byte Baid64 payload: the type byte, then the hash or key, then zero bytes. -/
def toPayload (p : Pay2Vout) : Bytes :=
  let body := match p.payload with
    | .pkh h | .sh h | .wpkh h | .wsh h => h
    | .tr k => k.bytes
  ((typeByte p.payload :: body) ++ List.replicate 32 0).take 33

/-- Read a 33-byte payload (`TryFrom<[u8; 33]>`): a 20-byte hash takes bytes 1 to 20 and
the rest is ignored; P2WSH and P2TR take bytes 1 to 32; a P2TR key must pass `validKey`. -/
def ofPayload (validKey : Bytes → Bool) (data : Bytes) : Except Pay2VoutError Pay2Vout :=
  let h20 := (data.drop 1).take 20
  let h32 := (data.drop 1).take 32
  match (data.headD 0).toNat with
  | 1 => .ok ⟨.pkh h20⟩
  | 2 => .ok ⟨.sh h20⟩
  | 3 => .ok ⟨.wpkh h20⟩
  | 4 => .ok ⟨.wsh h32⟩
  | 5 => if validKey h32 then .ok ⟨.tr ⟨h32⟩⟩ else .error .invalidTapkey
  | _ => .error (.invalidAddressType (data.headD 0))

end Pay2Vout

/-- Who receives the state (`Beneficiary`). -/
inductive Beneficiary where
  /-- A concealed seal on an output the beneficiary already owns. -/
  | blindedSeal (s : SecretSeal)
  /-- An output of the witness transaction; the key is its taproot internal key. -/
  | witnessVout (p : Pay2Vout) (internalKey : Option XOnlyKey)
  deriving DecidableEq, Repr, Inhabited

/-! ## Codec of identifiers -/

/-- The texts the model does not compute: Baid64 identifiers (whose checksum is a hash)
and the secp256k1 check of x-only keys. -/
structure IdCodec where
  /-- `ContractId::from_str`: Baid64 text, with or without `rgb:`, dashes or checksum. -/
  contractId? : String → Option ContractId
  /-- `ContractId` display: `rgb:` and the dashed Baid64 text. -/
  showContractId : ContractId → String
  /-- `SchemaId::from_str`. -/
  schemaId? : String → Option SchemaId
  /-- `{:-#}` display of a schema id: the bare Baid64 text, no `rgb:sch:`, no mnemonic. -/
  showSchemaId : SchemaId → String
  /-- `SchemaId` display: `rgb:sch:`, the Baid64 text, `#` and the mnemonic. -/
  showSchemaIdFull : SchemaId → String
  /-- `SecretSeal::from_str`. -/
  secretSeal? : String → Option SecretSeal
  /-- `SecretSeal` display: `utxob:` and the dashed Baid64 text with its checksum. -/
  showSecretSeal : SecretSeal → String
  /-- `Pay2Vout::from_str`; the error is the display text of the `Baid64ParseError`. -/
  pay2vout? : String → Except String Pay2Vout
  /-- `Pay2Vout::to_baid64_string`: `wvout:` and the dashed Baid64 text with checksum. -/
  showPay2Vout : Pay2Vout → String
  /-- The 32 bytes are the x coordinate of a secp256k1 point. -/
  xOnlyValid : Bytes → Bool

/-! ## Invoice data -/

/-- The state an invoice asks for (`InvoiceState`). -/
inductive InvoiceState where
  | void
  | amount (a : Amount)
  | data (d : NonFungible)
  deriving DecidableEq, Repr, Inhabited

/-- `could not parse as amount, data, or attach: {s}.` (`InvoiceStateError`). -/
inductive InvoiceStateError where
  | parseError (s : String)
  deriving DecidableEq, Repr

namespace InvoiceState

/-- Text: empty for `void`, base32 for an amount, `fraction@index` for data. -/
def display : InvoiceState → String
  | void => ""
  | amount a => a.display
  | data d => d.display

/-- Read state text (`InvoiceState::from_str`): empty text is `void`, then an amount is
tried, then an allocation. Allocation text holds digits and `@`, which amount text lacks. -/
def parse (s : String) : Except InvoiceStateError InvoiceState :=
  if s.isEmpty then .ok void
  else match Amount.parse s with
    | .ok a => .ok (amount a)
    | .error _ => match NonFungible.parse s with
      | .ok d => .ok (data d)
      | .error _ => .error (.parseError s)

/-- Kind of owned state asked for (`From<InvoiceState> for StateType`). -/
def stateType : InvoiceState → StateType
  | void => .void
  | amount _ => .fungible
  | data _ => .structured

end InvoiceState

/-- Name of an owned state type (`FieldName`): a lower-case letter or `_`, then letters,
digits or `_`; 1 to 100 characters. -/
structure FieldName where
  s : String
  deriving DecidableEq, Repr, Inhabited

/-- The name fits its character classes and length. -/
def FieldName.valid (n : FieldName) : Bool :=
  rstringValid (fun c => Charset.isAlphaSmall c || c == '_')
    (fun c => Charset.isAlphaNum c || c == '_') 1 100 n.s

/-- An RGB invoice (`RgbInvoice`). -/
structure RgbInvoice where
  /-- Where to post the consignment. -/
  transports : List RgbTransport := []
  /-- Contract to pay from; `none`: any. -/
  contract : Option ContractId := none
  /-- Schema of the contract; `none`: any. -/
  schema : Option SchemaId := none
  /-- Name of the owned state type to pay. -/
  assignmentName : Option FieldName := none
  /-- State to pay; `none`: not stated. -/
  assignmentState : Option InvoiceState := none
  /-- Who receives, on which chain. -/
  beneficiary : XChainNet Beneficiary
  /-- Expiry as a UTC unix timestamp (an `i64`). -/
  expiry : Option Int := none
  /-- Receiver's public key (`pk`): lower-case hex of 32 bytes. -/
  publicKey : Option String := none
  /-- Consignment encryption the receiver asks for. -/
  encryption : Lib.Encryption := .required
  /-- Other query parameters in order (an `IndexMap`). -/
  unknownQuery : List (String × String) := []
  deriving DecidableEq, Repr

/-- Why invoice text is refused (`InvoiceParseError`). -/
inductive InvoiceParseError where
  /-- Not a URI with a scheme. -/
  | invalid
  /-- An authority, even an empty one, or an absolute path. -/
  | authority
  /-- Never returned by the parser: splitting the path always gives a first segment. -/
  | contractMissing
  | schemaMissing
  | assignmentStateMissing
  | beneficiaryMissing
  | invalidScheme (s : String)
  /-- Never returned by the parser. -/
  | noTransport
  | invalidContractId (s : String)
  | invalidSchemaId (s : String)
  | invalidAssignmentState (s : String)
  | invalidAssignmentName (s : String)
  /-- Holds the text of the integer parse error. -/
  | invalidExpiration (s : String)
  | invalidPublicKey (s : String)
  | invalidEncryption (s : String)
  /-- Never returned by the parser. -/
  | invalidNetwork (network : String)
  | invalidQueryParam (s : String)
  | beneficiary (s : String)
  /-- Never returned by the parser. -/
  | num (e : IntErrorKind)
  /-- Never returned by the parser. -/
  | data (s : String)
  deriving DecidableEq, Repr

/-- Display text of the error (rgb-lib's `InvalidInvoice` carries it). -/
def InvoiceParseError.message : InvoiceParseError → String
  | .invalid => "invalid invoice."
  | .authority => "RGB invoice must not contain any URI authority data, including empty one."
  | .contractMissing => "contract id is missing from the invoice."
  | .schemaMissing => "schema information is missing from the invoice."
  | .assignmentStateMissing => "assignment state is missing from the invoice."
  | .beneficiaryMissing => "beneficiary is missing from the invoice."
  | .invalidScheme s => s!"invalid invoice scheme {s}."
  | .noTransport => "no invoice transport has been provided."
  | .invalidContractId _ => "invalid contract ID."
  | .invalidSchemaId s => s!"invalid schema {s}."
  | .invalidAssignmentState s => s!"invalid assignment state {s}."
  | .invalidAssignmentName s => s!"invalid assignment name {s}."
  | .invalidExpiration s => s!"invalid expiration timestamp {s}."
  | .invalidPublicKey s => s!"invalid public key {s}."
  | .invalidEncryption s => s!"invalid encryption preference {s}."
  | .invalidNetwork n => s!"invalid network {n}"
  | .invalidQueryParam s => s!"invalid query parameter {s}."
  | .beneficiary s =>
    s!"can't recognize beneficiary \"{s}\": " ++
      "it should be either a bitcoin address or a blinded UTXO seal."
  | .num e => e.message
  | .data s => s!"can't recognize amount \"{s}\": it should be valid allocation data."

/-! ## Beneficiary text -/

namespace XChainNet

/-- Text of `XChainNet<Beneficiary>` (a recipient id): the chain prefix, `:`, then the
concealed seal, or the witness output with `+` and the internal key in lower-case hex. -/
def showBeneficiary (codec : IdCodec) (b : XChainNet Beneficiary) : String :=
  b.chainNet.prefix_ ++ ":" ++
    (match b.inner with
      | .blindedSeal s => codec.showSecretSeal s
      | .witnessVout p k => codec.showPay2Vout p ++ (k.map fun k => "+" ++ hexOf k.bytes).getD "")

/-- Read an x-only key (`XOnlyPublicKey::from_str`): 64 hex digits of either case, a
point of the curve. -/
def parseXOnly (codec : IdCodec) (s : String) : Option XOnlyKey := do
  if s.length != 64 then none
  let b ← ofHex? s
  if codec.xOnlyValid b then some ⟨b⟩ else none

/-- Read a beneficiary (`XChainNet<Beneficiary>::from_str`): split at the first `:`; the
chain prefix ignores the case of ASCII letters; a concealed seal is tried first, then a
witness output with an optional `+` and internal key. -/
def parseBeneficiary (codec : IdCodec) (s : String) :
    Except InvoiceParseError (XChainNet Beneficiary) :=
  match splitOnce s ":" with
  | none => .error (.beneficiary "missing beneficiary HRI")
  | some (cn, rest) =>
    match ChainNet.ofPrefix? cn with
    | none => .error (.beneficiary s!"invalid chain-network pair {cn.toLower}.")
    | some net =>
      match codec.secretSeal? rest with
      | some ss => .ok ⟨net, .blindedSeal ss⟩
      | none =>
        let (p, key) := match splitOnce rest "+" with
          | some (p, k) => (p, some k)
          | none => (rest, none)
        match codec.pay2vout? p, key with
        | .error e, _ => .error (.beneficiary e)
        | .ok p, none => .ok ⟨net, .witnessVout p none⟩
        | .ok p, some k =>
          if k.isEmpty then .error (.beneficiary "missing internal pk")
          else match parseXOnly codec k with
            | some k => .ok ⟨net, .witnessVout p (some k)⟩
            | none => .error (.beneficiary "invalid internal pk")

end XChainNet

/-! ## URI check -/

namespace Uri

/-- RFC 3986 `unreserved`. -/
def isUnreserved (c : Char) : Bool := c.isAlphanum || "-._~".contains c

/-- RFC 3986 `sub-delims`. -/
def isSubDelim (c : Char) : Bool := "!$&'()*+,;=".contains c

/-- `pchar` without `%HH`: unreserved, sub-delims, `:` and `@`. -/
def isPchar (c : Char) : Bool := isUnreserved c || isSubDelim c || c == ':' || c == '@'

/-- Path characters: `pchar` and `/`. -/
def isPathChar (c : Char) : Bool := isPchar c || c == '/'

/-- Query and fragment characters: `pchar`, `/` and `?`. -/
def isQueryChar (c : Char) : Bool := isPchar c || c == '/' || c == '?'

/-- Authority characters: those of userinfo, host and port. -/
def isAuthorityChar (c : Char) : Bool := isPchar c || c == '[' || c == ']'

/-- Scheme characters after the first letter. -/
def isSchemeChar (c : Char) : Bool := c.isAlphanum || "+-.".contains c

/-- Every character is allowed, or starts a `%HH` escape. -/
def validRun (allowed : Char → Bool) : List Char → Bool
  | [] => true
  | '%' :: a :: b :: rest => isHexDigit a && isHexDigit b && validRun allowed rest
  | '%' :: _ => false
  | c :: rest => allowed c && validRun allowed rest

/-- Split at the first `c`. -/
def splitAtFirst (c : Char) (l : List Char) : List Char × Option (List Char) :=
  match l.idxOf? c with
  | some i => (l.take i, some (l.drop (i + 1)))
  | none => (l, none)

/-- The parts of a URI the invoice parser reads (`fluent_uri::Uri`). -/
structure Parts where
  scheme : String
  authority : Option String
  path : String
  query : Option String
  deriving DecidableEq, Repr

/-- Read a URI with a scheme (`Uri::parse`): each part holds only its characters and `%HH`
escapes; `#` starts the fragment and the first `?` before it the query; after `//` the
authority runs to the next `/`, its host and port grammar unchecked. -/
def parse (s : String) : Option Parts := do
  let cs := s.toList
  let scheme := cs.takeWhile isSchemeChar
  let first ← scheme.head?
  if !first.isAlpha then none
  let hier ← match cs.drop scheme.length with
    | ':' :: hier => some hier
    | _ => none
  let (beforeFragment, fragment) := splitAtFirst '#' hier
  let (hierPart, query) := splitAtFirst '?' beforeFragment
  if !(fragment.map (validRun isQueryChar)).getD true then none
  if !(query.map (validRun isQueryChar)).getD true then none
  let (authority, path) := match hierPart with
    | '/' :: '/' :: rest => (some (rest.takeWhile (· != '/')), rest.dropWhile (· != '/'))
    | _ => (none, hierPart)
  if !(authority.map (validRun isAuthorityChar)).getD true then none
  if !validRun isPathChar path then none
  return ⟨String.ofList scheme, authority.map String.ofList, String.ofList path,
    query.map String.ofList⟩

end Uri

/-! ## Query parameters -/

/-- Path segment of an omitted contract, schema or state (`OMITTED`). -/
def omitted : String := "~"
/-- Query key of the assignment name (`ASSIGNMENT`). -/
def keyAssignmentName : String := "assignment_name"
/-- Query key of the expiry (`EXPIRY`). -/
def keyExpiry : String := "expiry"
/-- Query key of the receiver's public key (`PUBKEY`). -/
def keyPubkey : String := "pk"
/-- Query key of the encryption preference (`ENCRYPTION`). -/
def keyEncryption : String := "enc"
/-- Query key of the transports (`ENDPOINTS`). -/
def keyEndpoints : String := "endpoints"

/-- Insert into an insertion-ordered map (`IndexMap::insert`): a present key keeps its
place and takes the new value. -/
def insertParam (m : List (String × String)) (k v : String) : List (String × String) :=
  if m.any (·.1 == k) then m.map fun p => if p.1 == k then (k, v) else p else m ++ [(k, v)]

/-- Take a key out and keep the order of the rest (`IndexMap::shift_remove`). -/
def shiftRemove (m : List (String × String)) (k : String) :
    Option String × List (String × String) :=
  ((m.find? (·.1 == k)).map (·.2), m.filter (·.1 != k))

/-- Length of a UTF-8 sequence by its first byte (`utf8_char_width`); 0: not a first byte. -/
def utf8Width (b : Nat) : Nat :=
  if b < 0x80 then 1 else if b < 0xC2 then 0 else if b < 0xE0 then 2
  else if b < 0xF0 then 3 else if b < 0xF5 then 4 else 0

/-- The UTF-8 sequence that starts with byte `b`, followed by `rest`: its character and
length, or why it is bad (`none`: the input ends inside it; `some n`: `n` bad bytes). -/
def utf8Step (b : Nat) (rest : List Nat) : Except (Option Nat) (Char × Nat) :=
  let cont (x : Nat) : Bool := 0x80 ≤ x && x ≤ 0xBF
  let second3 (x : Nat) : Bool :=
    (b == 0xE0 && 0xA0 ≤ x && x ≤ 0xBF) || (0xE1 ≤ b && b ≤ 0xEC && cont x) ||
      (b == 0xED && 0x80 ≤ x && x ≤ 0x9F) || (0xEE ≤ b && b ≤ 0xEF && cont x)
  let second4 (x : Nat) : Bool :=
    (b == 0xF0 && 0x90 ≤ x && x ≤ 0xBF) || (0xF1 ≤ b && b ≤ 0xF3 && cont x) ||
      (b == 0xF4 && 0x80 ≤ x && x ≤ 0x8F)
  match utf8Width b, rest with
  | 1, _ => .ok (Char.ofNat b, 1)
  | 2, n1 :: _ =>
    if cont n1 then .ok (Char.ofNat ((b % 32) * 64 + n1 % 64), 2) else .error (some 1)
  | 3, n1 :: r =>
    if !second3 n1 then .error (some 1)
    else match r with
      | [] => .error none
      | n2 :: _ =>
        if cont n2 then .ok (Char.ofNat ((b % 16) * 4096 + (n1 % 64) * 64 + n2 % 64), 3)
        else .error (some 2)
  | 4, n1 :: r =>
    if !second4 n1 then .error (some 1)
    else match r with
      | [] => .error none
      | n2 :: r' =>
        if !cont n2 then .error (some 2)
        else match r' with
          | [] => .error none
          | n3 :: _ =>
            if cont n3 then
              .ok (Char.ofNat ((b % 8) * 262144 + (n1 % 64) * 4096 + (n2 % 64) * 64 + n3 % 64), 4)
            else .error (some 3)
  | 2, [] | 3, [] | 4, [] => .error none
  | _, _ => .error (some 1)

/-- Decode UTF-8 as Rust's `String::from_utf8` does; the error is the display text of its
`Utf8Error`: where the first bad sequence starts and, unless the input ends inside it,
its length. -/
def utf8Decode (bs : List Nat) : Except String String :=
  go 0 bs []
where
  go (i : Nat) (bs : List Nat) (acc : List Char) : Except String String :=
    match bs with
    | [] => .ok (String.ofList acc.reverse)
    | b :: rest =>
      match utf8Step b rest with
      | .ok (c, k) => go (i + k) (rest.drop (k - 1)) (c :: acc)
      | .error none => .error s!"incomplete utf-8 byte sequence from index {i}"
      | .error (some n) => .error s!"invalid utf-8 sequence of {n} bytes from index {i}"
  termination_by bs.length

/-- Percent-decode query text (`EStr::decode`, then `into_string`): `%HH` gives a byte,
other characters their UTF-8 bytes, `+` stays `+`; the result must be UTF-8. -/
def percentDecode (s : String) : Except String String :=
  utf8Decode (go s.toList)
where
  go : List Char → List Nat
    | '%' :: a :: b :: rest =>
      if isHexDigit a && isHexDigit b then (16 * hexValue a + hexValue b) :: go rest
      else '%'.toNat :: go (a :: b :: rest)
    | c :: rest => (String.singleton c).toUTF8.toList.map (·.toNat) ++ go rest
    | [] => []

/-- Bytes encoded in query keys and values (`QUERY_ENCODE`): controls, space, `"`, `#`,
`<`, `>`, `[`, `]`, `&`, `=` and every non-ASCII byte; `%` is not encoded. -/
def queryEncoded (b : UInt8) : Bool :=
  b < 0x20 || b ≥ 0x7F || " \"#<>[]&=".toList.any (·.toNat == b.toNat)

/-- Percent-encode query text (`utf8_percent_encode` with `QUERY_ENCODE`, upper-case hex). -/
def percentEncode (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    if queryEncoded b then "%" ++ (hexOf [b]).toUpper else String.singleton (Char.ofNat b.toNat))

/-- Read the query (`map_query_params`): each `&` piece splits at its first `=` (an empty
query, `&&` and a trailing `&` have none); key, then value, are percent-decoded to UTF-8;
a repeated key keeps its first place and its last value. -/
def mapQueryParams (query : Option String) :
    Except InvoiceParseError (List (String × String)) :=
  match query with
  | none => .ok []
  | some q => (splitAll q '&').foldlM (fun m p => do
      let some (k, v) := splitOnce p "=" | throw (.invalidQueryParam p)
      let k ← (percentDecode k).mapError .invalidQueryParam
      let v ← (percentDecode v).mapError .invalidQueryParam
      return insertParam m k v) []

/-! ## Invoice text -/

namespace RgbInvoice

/-- Chain of the beneficiary. -/
def chainNetwork (i : RgbInvoice) : ChainNet := i.beneficiary.chainNet

/-- Address network of the beneficiary's chain. -/
def addressNetwork (i : RgbInvoice) : KnownHrp := i.beneficiary.addressNetwork

/-- Layer 1 of the beneficiary's chain. -/
def layer1 (i : RgbInvoice) : Layer1 := i.beneficiary.layer1

/-- The invoice has a query (`has_params`). -/
def hasParams (i : RgbInvoice) : Bool :=
  i.expiry.isSome || i.assignmentName.isSome || !i.transports.isEmpty || i.publicKey.isSome ||
    i.encryption != .required || !i.unknownQuery.isEmpty

/-- Query parameters in display order (`query_params`): `assignment_name`, `expiry`, `pk`,
`enc` (`0` unsupported, `1` optional, absent when required), `endpoints` (joined by `,`),
then the other parameters, where one with a known key replaces that key's value. -/
def queryParams (i : RgbInvoice) : List (String × String) :=
  let enc := match i.encryption with
    | .required => []
    | .unsupported => [(keyEncryption, "0")]
    | .optional => [(keyEncryption, "1")]
  let endpoints := if i.transports.isEmpty then []
    else [(keyEndpoints, String.intercalate "," (i.transports.map RgbTransport.display))]
  let known := (i.assignmentName.map fun n => (keyAssignmentName, n.s)).toList ++
    (i.expiry.map fun e => (keyExpiry, toString e)).toList ++
    (i.publicKey.map fun k => (keyPubkey, k)).toList ++ enc ++ endpoints
  i.unknownQuery.foldl (fun m p => insertParam m p.1 p.2) known

/-- Invoice text (`Display`): the contract id's own `rgb:` is the URI scheme; `void` gives
an empty segment, an omitted part `~`; keys and values are percent-encoded. The alternate
form (`{:#}`) drops the dashes of the contract, the schema and the beneficiary. -/
def display (codec : IdCodec) (i : RgbInvoice) (alternate : Bool := false) : String :=
  let dashless (s : String) : String :=
    if alternate then String.ofList (s.toList.filter (· != '-')) else s
  let contract := match i.contract with
    | some c => dashless (codec.showContractId c)
    | none => "rgb:" ++ omitted
  let schema := match i.schema with
    | some s => dashless (codec.showSchemaId s)
    | none => omitted
  let state := match i.assignmentState with
    | some st => st.display
    | none => omitted
  let query := String.intercalate "&"
    (i.queryParams.map fun p => percentEncode p.1 ++ "=" ++ percentEncode p.2)
  contract ++ "/" ++ schema ++ "/" ++ state ++ "/" ++
    dashless (XChainNet.showBeneficiary codec i.beneficiary) ++
    (if i.hasParams then "?" else "") ++ query

/-- Read an invoice (`RgbInvoice::from_str`); the first failing check, in the order below,
decides the error. Segments are not percent-decoded, those after the beneficiary and the
fragment are ignored, and no field is checked against another. -/
def parse (codec : IdCodec) (s : String) : Except InvoiceParseError RgbInvoice := do
  let some uri := Uri.parse s | throw .invalid
  if uri.scheme != "rgb" then throw (.invalidScheme uri.scheme)
  if uri.path.startsWith "/" || uri.authority.isSome then throw .authority
  let segments := splitAll uri.path '/'
  let some cs := segments[0]? | throw .contractMissing
  let contract ← match codec.contractId? cs with
    | some c => pure (some c)
    | none => if cs == omitted then pure none else throw (.invalidContractId cs)
  let some ss := segments[1]? | throw .schemaMissing
  let schema ← match codec.schemaId? ss with
    | some id => pure (some id)
    | none => if ss == omitted then pure none else throw (.invalidSchemaId ss)
  let some st := segments[2]? | throw .assignmentStateMissing
  let state ← match InvoiceState.parse st with
    | .ok x => pure (some x)
    | .error _ => if st == omitted then pure none else throw (.invalidAssignmentState st)
  let some bs := segments[3]? | throw .beneficiaryMissing
  let beneficiary ← XChainNet.parseBeneficiary codec bs
  let params ← mapQueryParams uri.query
  let (endpoints, params) := shiftRemove params keyEndpoints
  let transports ← match endpoints with
    | none => pure []
    | some e => (splitAll e ',').mapM fun t =>
      (RgbTransport.parse t).mapError fun err => .invalidQueryParam err.message
  let (name, params) := shiftRemove params keyAssignmentName
  let assignmentName ← match name with
    | none => pure none
    | some n =>
      if (FieldName.mk n).valid then pure (some ⟨n⟩) else throw (.invalidAssignmentName n)
  let (exp, params) := shiftRemove params keyExpiry
  let expiry ← match exp with
    | none => pure none
    | some e => match parseI64 e with
      | .ok t => pure (some t)
      | .error err => throw (.invalidExpiration err.message)
  let (pk, params) := shiftRemove params keyPubkey
  let publicKey ← match pk with
    | none => pure none
    | some k => match ofHex? k with
      | some b => if b.length == 32 then pure (some (hexOf b)) else throw (.invalidPublicKey k)
      | none => throw (.invalidPublicKey k)
  let (enc, params) := shiftRemove params keyEncryption
  let encryption ← match enc with
    | none => pure .required
    | some "0" => pure .unsupported
    | some "1" => pure .optional
    | some e => throw (.invalidEncryption e)
  return {
    transports := transports
    contract := contract
    schema := schema
    assignmentName := assignmentName
    assignmentState := state
    beneficiary := beneficiary
    expiry := expiry
    publicKey := publicKey
    encryption := encryption
    unknownQuery := params }

end RgbInvoice

/-! ## Builder -/

/-- Invoice builder (`RgbInvoiceBuilder`); setters overwrite, and no field is checked
against another. -/
structure RgbInvoiceBuilder where
  invoice : RgbInvoice
  deriving DecidableEq, Repr

namespace RgbInvoiceBuilder

/-- No transports, no contract, schema, state, name, expiry or key; encryption required. -/
def new (b : XChainNet Beneficiary) : RgbInvoiceBuilder := ⟨{ beneficiary := b }⟩

/-- Sets the contract. -/
def setContract (bl : RgbInvoiceBuilder) (c : ContractId) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with contract := some c }⟩

/-- `with`: a builder for one contract. -/
def withContract (c : ContractId) (b : XChainNet Beneficiary) : RgbInvoiceBuilder :=
  (new b).setContract c

/-- Sets the schema. -/
def setSchema (bl : RgbInvoiceBuilder) (s : SchemaId) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with schema := some s }⟩

/-- Sets the assignment name. -/
def setAssignmentName (bl : RgbInvoiceBuilder) (n : FieldName) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with assignmentName := some n }⟩

/-- Asks for void state. -/
def setVoid (bl : RgbInvoiceBuilder) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with assignmentState := some .void }⟩

/-- Asks for an amount in atoms. -/
def setAmountRaw (bl : RgbInvoiceBuilder) (a : Amount) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with assignmentState := some (.amount a) }⟩

/-- `set_amount`: the error returns the builder unchanged when `decimals ≥ 10^precision`;
`none` where the library panics because `integer * 10^precision + decimals` overflows. -/
def setAmount (bl : RgbInvoiceBuilder) (integer decimals : UInt64) (p : Precision) :
    Option (Except RgbInvoiceBuilder RgbInvoiceBuilder) :=
  match CoinAmount.withParts integer decimals p with
  | .error _ => some (.error bl)
  | .ok c => c.toAmountUnchecked.map fun a => .ok (bl.setAmountRaw a)

/-- Asks for an allocation. -/
def setAllocationRaw (bl : RgbInvoiceBuilder) (a : Allocation) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with assignmentState := some (.data (.fractionedToken a)) }⟩

/-- `set_allocation`: always succeeds. -/
def setAllocation (bl : RgbInvoiceBuilder) (index : UInt32) (fraction : UInt64) :
    Except RgbInvoiceBuilder RgbInvoiceBuilder :=
  .ok (bl.setAllocationRaw ⟨⟨index⟩, ⟨fraction⟩⟩)

/-- `set_amount_approx`: refuses `amount ≤ 0`; the whole part goes to `set_amount` and the
fraction is lost (its integer cast is always 0); NaN gives 0 and infinity the largest
`u64`, which panics at any precision but `indivisible`. -/
def setAmountApprox (bl : RgbInvoiceBuilder) (amount : Float) (p : Precision) :
    Option (Except RgbInvoiceBuilder RgbInvoiceBuilder) :=
  if amount ≤ 0.0 then some (.error bl)
  else bl.setAmount amount.floor.toUInt64 (amount - amount.floor).toUInt64 p

/-- Sets the expiry, a unix timestamp. -/
def setExpiryTimestamp (bl : RgbInvoiceBuilder) (expiry : Int) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with expiry := some expiry }⟩

/-- Sets the 32-byte key as lower-case hex. -/
def setPublicKey (bl : RgbInvoiceBuilder) (key : Bytes) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with publicKey := some (hexOf key) }⟩

/-- Sets the encryption preference. -/
def setEncryption (bl : RgbInvoiceBuilder) (e : Lib.Encryption) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with encryption := e }⟩

/-- Appends a transport; duplicates are kept. -/
def addTransportRaw (bl : RgbInvoiceBuilder) (t : RgbTransport) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with transports := bl.invoice.transports ++ [t] }⟩

/-- Appends a transport read from text; on an error the builder is returned unchanged. -/
def addTransport (bl : RgbInvoiceBuilder) (s : String) :
    Except (RgbInvoiceBuilder × TransportParseError) RgbInvoiceBuilder :=
  match RgbTransport.parse s with
  | .ok t => .ok (bl.addTransportRaw t)
  | .error e => .error (bl, e)

/-- Appends transports. -/
def addTransportsRaw (bl : RgbInvoiceBuilder) (ts : List RgbTransport) : RgbInvoiceBuilder :=
  ⟨{ bl.invoice with transports := bl.invoice.transports ++ ts }⟩

/-- All or nothing: the first text that is not a transport returns its error. -/
def addTransports (bl : RgbInvoiceBuilder) (l : List String) :
    Except (RgbInvoiceBuilder × TransportParseError) RgbInvoiceBuilder :=
  match l.mapM RgbTransport.parse with
  | .ok ts => .ok (bl.addTransportsRaw ts)
  | .error e => .error (bl, e)

/-- The invoice built. -/
def finish (bl : RgbInvoiceBuilder) : RgbInvoice := bl.invoice

end RgbInvoiceBuilder

end Rgb.Invoice

/-! ## rgb-lib's invoice layer -/

namespace Rgb.Lib

open Rgb.Invoice

/-- Display name of a layer 1 (`Layer1`, lower case). -/
def layer1Name : Layer1 → String
  | .bitcoin => "bitcoin"
  | .liquid => "liquid"

/-- rgb-lib's network of a chain net (`BitcoinNetwork::try_from(ChainNet)`). -/
def chainNetToNetwork (c : ChainNet) : Result BitcoinNetwork :=
  match c with
  | .bitcoinMainnet => .ok .mainnet
  | .bitcoinTestnet3 => .ok .testnet
  | .bitcoinTestnet4 => .ok .testnet4
  | .bitcoinSignet => .ok .signet
  | .bitcoinRegtest => .ok .regtest
  | .bitcoinSignetCustom => .ok .signetCustom
  | .liquidMainnet | .liquidTestnet => .error (.unsupportedLayer1 (layer1Name c.layer1))

/-- Asset schema of a schema id (`AssetSchema::try_from(SchemaId)`): the displayed id is
compared with the ids of rgb-lib's schemas. -/
def assetSchemaOf (codec : IdCodec) (id : SchemaId) : Result AssetSchema :=
  let s := codec.showSchemaIdFull id
  match AssetSchema.all.find? (·.schemaIdString == s) with
  | some a => .ok a
  | none => .error (.unknownRgbSchema s)

/-- The assignment an invoice asks for, from its schema, state and assignment name; the
first matching row wins, else the text of the `InvalidInvoice` error. -/
def invoiceAssignment (schema : Option AssetSchema) (state : Option InvoiceState)
    (name : Option String) : Except String Assignment :=
  match schema with
  | none => match state, name with
    | some (.amount v), some "assetOwner" => .ok (.fungible v.v)
    | some (.amount v), some "inflationAllowance" => .ok (.inflationRight v.v)
    | some (.amount _), _ => .ok .any
    | some (.data _), some "assetOwner" | some (.data _), none => .ok .nonFungible
    | none, none => .ok .any
    | _, _ => .error "unsupported assignment"
  | some .nia | some .cfa => match state, name with
    | some (.amount v), some "assetOwner" | some (.amount v), none => .ok (.fungible v.v)
    | none, some "assetOwner" | none, none => .ok (.fungible 0)
    | _, _ => .error "invalid assignment"
  | some .uda => match state, name with
    | some (.data _), some "assetOwner" | some (.data _), none
    | none, some "assetOwner" | none, none => .ok .nonFungible
    | _, _ => .error "invalid assignment"
  | some .ifa => match state, name with
    | some (.amount v), some "assetOwner" => .ok (.fungible v.v)
    | none, some "assetOwner" => .ok (.fungible 0)
    | some (.amount v), some "inflationAllowance" => .ok (.inflationRight v.v)
    | none, some "inflationAllowance" => .ok (.inflationRight 0)
    | some .void, some "linkRight" | none, some "linkRight" => .ok .linkRight
    | some (.amount _), none | none, none => .ok .any
    | _, _ => .error "invalid assignment"
  | some .bfa => match state, name with
    | some (.amount v), some "assetOwner" => .ok (.fungible v.v)
    | none, some "assetOwner" => .ok (.fungible 0)
    | some .void, some "linkRight" | none, some "linkRight" => .ok .linkRight
    | some .void, some "mintRight" | none, some "mintRight" => .ok .mintRight
    | some (.amount _), none | none, none => .ok .any
    | _, _ => .error "invalid assignment"

/-- What rgb-lib reads from an invoice (`InvoiceData`). -/
structure InvoiceData where
  recipientId : String
  assetSchema : Option AssetSchema
  assetId : Option String
  assignment : Assignment
  assignmentName : Option String
  network : BitcoinNetwork
  /-- The expiry cast from `i64` to `u64`: a negative expiry wraps. -/
  expirationTimestamp : Option Nat
  transportEndpoints : List String
  publicKey : Option String
  encryption : Encryption
  /-- The other query parameters (a `HashMap`: their order carries no meaning). -/
  unknownQueryParams : List (String × String)
  deriving DecidableEq, Repr

/-- An invoice text and what rgb-lib reads from it (`Invoice`). -/
structure Invoice where
  invoiceString : String
  invoiceData : InvoiceData
  deriving DecidableEq, Repr

/-- Read an invoice for the wallet (`Invoice::new`). Checks in order: the text
(`invalidInvoice` with the parse error's text), the schema (`unknownRgbSchema`), the
assignment (`invalidInvoice`), the layer 1 (`unsupportedLayer1`). -/
def Invoice.new (codec : IdCodec) (s : String) : Result Invoice := do
  let inv ← (RgbInvoice.parse codec s).mapError fun e => Error.invalidInvoice e.message
  let assetSchema ← match inv.schema with
    | none => pure none
    | some id => some <$> assetSchemaOf codec id
  let assignmentName := inv.assignmentName.map (·.s)
  let assignment ← (invoiceAssignment assetSchema inv.assignmentState assignmentName).mapError
    Error.invalidInvoice
  let network ← match inv.layer1 with
    | .bitcoin => chainNetToNetwork inv.chainNetwork
    | .liquid => throw (Error.unsupportedLayer1 (layer1Name .liquid))
  let data : InvoiceData :=
    { recipientId := XChainNet.showBeneficiary codec inv.beneficiary
      assetSchema := assetSchema
      assetId := inv.contract.map codec.showContractId
      assignment := assignment
      assignmentName := assignmentName
      network := network
      expirationTimestamp := inv.expiry.map fun t => (t % 2 ^ 64).toNat
      transportEndpoints := inv.transports.map RgbTransport.display
      publicKey := inv.publicKey
      encryption := inv.encryption
      unknownQueryParams := inv.unknownQuery }
  return ⟨s, data⟩

/-- A recipient id read on its own (`RecipientInfo`). -/
structure RecipientInfo where
  recipientId : String
  recipientType : RecipientType
  network : BitcoinNetwork
  deriving DecidableEq, Repr

/-- Read a recipient id (`RecipientInfo::new`): a beneficiary with its chain prefix
(`invalidRecipientId`), on a Bitcoin network (`unsupportedLayer1`). -/
def RecipientInfo.new (codec : IdCodec) (id : String) : Result RecipientInfo := do
  let b ← (XChainNet.parseBeneficiary codec id).mapError fun _ => Error.invalidRecipientId
  let ty := match b.inner with
    | .witnessVout _ _ => RecipientType.witness
    | .blindedSeal _ => RecipientType.blind
  let network ← chainNetToNetwork b.chainNet
  return ⟨id, ty, network⟩

/-- Read a transport endpoint (`TransportEndpoint::new`): a transport
(`invalidTransportEndpoint` with the parse error's text) of the JSON-RPC kind
(`unsupportedTransportType`); `rpc://host` gives `http://host`, `rpcs://` gives `https://`. -/
def TransportEndpoint.new (s : String) : Result TransportEndpoint :=
  match RgbTransport.parse s with
  | .error e => .error (.invalidTransportEndpoint e.message)
  | .ok (.jsonRpc tls host) => .ok ⟨"http" ++ tlsSuffix tls ++ "://" ++ host, .jsonRpc⟩
  | .ok _ => .error .unsupportedTransportType

end Rgb.Lib
