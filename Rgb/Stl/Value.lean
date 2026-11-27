import Rgb.Stl.Types

/-!
# Strict values

Structured state and metadata hold strict-encoded data of a semantic type that
the schema names by its `SemId`. The model represents a value as one of the
standard types, tagged with its semantic type; `conforms` is what strict
decoding checks: the right type and every bound of that type.
-/

namespace Rgb

/-- Semantic type ids of the standard types (`SemId`). -/
inductive SemId where
  | assetSpec
  | contractSpec
  | contractTerms
  | amount
  | details
  | name
  | ticker
  | unicodeTicker
  | precision
  | tokenData
  | tokenIndex
  /-- UDA owned state: a token index and the owned fraction. -/
  | allocation
  | rejectListUrl
  | rejectListLocation
  | bridgeLocation
  | evmContract
  | blockNumber
  | burnReason
  | burnMeta
  | issueMeta
  /-- An operation id stored as data (BFA mint and burn references). -/
  | opId
  /-- A 32-byte hash stored as data. -/
  | bytes32
  /-- A compressed secp256k1 public key (33 bytes). -/
  | pubkey
  /-- A 64-byte signature. -/
  | signature
  /-- Any other type, by name: values carry raw bytes. -/
  | other (name : String)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A value of a standard type. -/
inductive StrictValue where
  | assetSpec (v : AssetSpec)
  | contractSpec (v : ContractSpec)
  | contractTerms (v : ContractTerms)
  | amount (v : UInt64)
  | details (v : Details)
  | name (v : Name)
  | ticker (v : Ticker)
  | unicodeTicker (v : UnicodeTicker)
  | precision (v : Precision)
  | tokenData (v : TokenData)
  | tokenIndex (v : TokenIndex)
  | allocation (index : TokenIndex) (fraction : UInt64)
  | rejectListUrl (v : RejectListUrl)
  | rejectListLocation (v : RejectListLocation)
  | bridgeLocation (v : BridgeLocation)
  | evmContract (v : EvmContract)
  | blockNumber (v : BlockNumber)
  | burnReason (v : BurnReason)
  | burnMeta (v : BurnMeta)
  | issueMeta (v : IssueMeta)
  | opId (v : Digest)
  | bytes32 (v : Bytes)
  | pubkey (v : Bytes)
  | signature (v : Bytes)
  | raw (sem : String) (bytes : Bytes)
  deriving DecidableEq, Hashable, Repr, Inhabited

namespace StrictValue

/-- The semantic type of a value. -/
def semId : StrictValue → SemId
  | assetSpec _ => .assetSpec | contractSpec _ => .contractSpec
  | contractTerms _ => .contractTerms | amount _ => .amount | details _ => .details
  | name _ => .name | ticker _ => .ticker | unicodeTicker _ => .unicodeTicker
  | precision _ => .precision | tokenData _ => .tokenData | tokenIndex _ => .tokenIndex
  | allocation _ _ => .allocation | rejectListUrl _ => .rejectListUrl
  | rejectListLocation _ => .rejectListLocation | bridgeLocation _ => .bridgeLocation
  | evmContract _ => .evmContract | blockNumber _ => .blockNumber
  | burnReason _ => .burnReason | burnMeta _ => .burnMeta | issueMeta _ => .issueMeta
  | opId _ => .opId | bytes32 _ => .bytes32 | pubkey _ => .pubkey
  | signature _ => .signature | raw n _ => .other n

/-- Every bound of the value's type holds (what strict decoding enforces). -/
def wellFormed : StrictValue → Bool
  | assetSpec v => v.valid
  | contractSpec v => v.valid
  | contractTerms v => v.valid
  | details v => v.valid
  | name v => v.valid
  | ticker v => v.valid
  | unicodeTicker v => v.valid
  | tokenData v => v.valid
  | rejectListUrl v => v.valid
  | rejectListLocation v => v.valid
  | bridgeLocation (.evm c) => c.address.valid
  | evmContract c => c.address.valid
  | burnReason v => v.valid
  | burnMeta v => v.burnProofs.all ProofOfReserves.valid && v.burnProofs.length ≤ 65535
  | issueMeta v => v.reserves.all ProofOfReserves.valid && v.reserves.length ≤ 65535
  | bytes32 b => b.length == 32
  | pubkey b => b.length == 33
  | signature b => b.length == 64
  | raw _ b => b.length ≤ 65535
  | _ => true

/-- The value decodes as `sem`: the strict-type check of structured state. -/
def conforms (v : StrictValue) (sem : SemId) : Bool := v.semId == sem && v.wellFormed

def asAmount? : StrictValue → Option UInt64
  | amount v => some v
  | _ => none

instance : Encode StrictValue := ⟨fun v => encode (reprStr v)⟩

end StrictValue

end Rgb
