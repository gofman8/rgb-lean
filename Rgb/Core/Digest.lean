import Rgb.Core.Hex

/-!
# Commitments and identifiers

RGB names every object by a tagged hash of its strict encoding. The model keeps
the tag and a canonical encoding of the committed data in place of the 32-byte
hash, so two digests are equal exactly when their tags and data are equal. This
gives a collision-resistant hash by construction, without an axiom. The model
does not model hiding: a `SecretSeal` holds its seal's encoding, and no rule of
the model reads it back.
-/

namespace Rgb

/-- Canonical, self-delimiting text encoding of committed data. -/
class Encode (α : Type) where
  encode : α → String

export Encode (encode)

/-- Length-prefixed field: the building block that makes encodings injective. -/
def encField (s : String) : String := s!"{s.length}:{s}"

instance : Encode String := ⟨encField⟩
instance : Encode Nat := ⟨fun n => encField (toString n)⟩
instance : Encode Int := ⟨fun i => encField (toString i)⟩
instance : Encode Bool := ⟨fun b => if b then "T" else "F"⟩
instance : Encode UInt8 := ⟨fun n => encode n.toNat⟩
instance : Encode UInt16 := ⟨fun n => encode n.toNat⟩
instance : Encode UInt32 := ⟨fun n => encode n.toNat⟩
instance : Encode UInt64 := ⟨fun n => encode n.toNat⟩
instance : Encode Unit := ⟨fun _ => "U"⟩

instance [Encode α] : Encode (List α) :=
  ⟨fun l => encField (String.join (l.map encode))⟩

instance [Encode α] : Encode (Option α) :=
  ⟨fun | none => "N" | some a => "S" ++ encode a⟩

instance [Encode α] [Encode β] : Encode (α × β) :=
  ⟨fun (a, b) => encField (encode a ++ encode b)⟩

/-- A tagged commitment (the model of a 32-byte tagged hash). -/
structure Digest where
  tag : String
  data : String
  deriving DecidableEq, Ord, Hashable, Inhabited

namespace Digest

/-- Commit to the encoded `parts` under `tag`. -/
def of (tag : String) (parts : List String) : Digest := ⟨tag, String.join parts⟩

/-- FNV-1a over the tag and data: a short display name, never compared. -/
def fingerprint (d : Digest) : UInt64 :=
  (d.tag ++ "#" ++ d.data).foldl
    (fun h c => (h ^^^ c.toNat.toUInt64) * 1099511628211) 14695981039346656037

/-- Eight hex digits of the fingerprint. -/
def short (d : Digest) : String := Hex.ofNat d.fingerprint.toNat 8

instance : ToString Digest := ⟨short⟩
instance : Repr Digest := ⟨fun d _ => d.short⟩
instance : Encode Digest := ⟨fun d => encField (encode d.tag ++ encode d.data)⟩

end Digest

/-! Tags of the RGB commitment schemes (as in rgb-consensus). -/
namespace Tag
def operation : String := "urn:lnp-bp:rgb:operation#2024-02-03"
def bundle : String := "urn:lnp-bp:rgb:bundle#2024-02-03"
def schema : String := "urn:lnp-bp:rgb:schema#2024-02-03"
def secretSeal : String := "urn:lnp-bp:seals:secret#2024-02-03"
def disclose : String := "urn:lnp-bp:rgb:disclose#2024-02-16"
def merkleNode : String := "urn:ubideco:merkle:node#2024-01-31"
def mpcCommitment : String := "urn:ubideco:mpc:commitment#2024-01-31"
def strictHash : String := "urn:ubideco:strict-types:value-hash#2024-02-10"
/-- Bitcoin transaction id (double SHA-256 of the transaction). -/
def txid : String := "bitcoin:txid"
/-- Bitcoin block hash. -/
def blockHash : String := "bitcoin:block"
/-- Taproot output key tweak. -/
def tapTweak : String := "TapTweak"
/-- Taproot branch and leaf hashes. -/
def tapBranch : String := "TapBranch"
def tapLeaf : String := "TapLeaf"
end Tag

end Rgb
