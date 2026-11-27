import Rgb.Core.Digest

/-!
# Confined collections

RGB data types are strict-encoded with confined collections: every vector, map
and blob carries a minimum and a maximum length. The model keeps plain lists and
states each bound as a check, so a value that breaks a bound is representable
and the check that refuses it is explicit.
-/

namespace Rgb

/-! Maximum lengths of the strict-encoding size classes. -/
namespace Bound
/-- `Tiny*` collections. -/
def u8 : Nat := 255
/-- `Small*` collections and blobs, and `U16`-confined vectors. -/
def u16 : Nat := 65535
/-- `Medium*` collections and `u24` counters. -/
def u24 : Nat := 16777215
def u32 : Nat := 4294967295
def u64 : Nat := 18446744073709551615
end Bound

/-- A confinement bound was broken. -/
inductive ConfinementError where
  | undersize (what : String) (len min : Nat)
  | oversize (what : String) (len max : Nat)
  deriving DecidableEq, Repr

/-- Check `min ≤ len ≤ max` for the collection named `what`. -/
def checkLen (what : String) (len min max : Nat) : Except ConfinementError Unit :=
  if len < min then .error (.undersize what len min)
  else if len > max then .error (.oversize what len max)
  else .ok ()

/-- An ordered map kept as a list sorted by key with unique keys (a `BTreeMap`). -/
structure OrdMap (κ : Type) (ν : Type) where
  toList : List (κ × ν)
  deriving DecidableEq, Repr, Inhabited

namespace OrdMap
variable {κ ν : Type} [Ord κ]

def empty : OrdMap κ ν := ⟨[]⟩

instance : EmptyCollection (OrdMap κ ν) := ⟨empty⟩

private def insertList (k : κ) (v : ν) : List (κ × ν) → List (κ × ν)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    match compare k k' with
    | .lt => (k, v) :: (k', v') :: rest
    | .eq => (k, v) :: rest
    | .gt => (k', v') :: insertList k v rest

/-- Insert or replace the value of `k`. -/
def insert (m : OrdMap κ ν) (k : κ) (v : ν) : OrdMap κ ν := ⟨insertList k v m.toList⟩

def find? (m : OrdMap κ ν) (k : κ) : Option ν :=
  (m.toList.find? fun p => compare p.1 k == .eq).map (·.2)

def contains (m : OrdMap κ ν) (k : κ) : Bool := (m.find? k).isSome

def erase (m : OrdMap κ ν) (k : κ) : OrdMap κ ν :=
  ⟨m.toList.filter fun p => compare p.1 k != .eq⟩

def keys (m : OrdMap κ ν) : List κ := m.toList.map (·.1)
def values (m : OrdMap κ ν) : List ν := m.toList.map (·.2)
def size (m : OrdMap κ ν) : Nat := m.toList.length
def isEmpty (m : OrdMap κ ν) : Bool := m.toList.isEmpty

/-- Build from a list; a later entry replaces an earlier one with the same key. -/
def ofList (l : List (κ × ν)) : OrdMap κ ν := l.foldl (fun m (k, v) => m.insert k v) empty

/-- Update the value of `k` with `f` applied to its current value. -/
def alter (m : OrdMap κ ν) (k : κ) (f : Option ν → ν) : OrdMap κ ν := m.insert k (f (m.find? k))

def mapValues {μ : Type} (m : OrdMap κ ν) (f : ν → μ) : OrdMap κ μ :=
  ⟨m.toList.map fun (k, v) => (k, f v)⟩

def filter (m : OrdMap κ ν) (p : κ → ν → Bool) : OrdMap κ ν := ⟨m.toList.filter fun (k, v) => p k v⟩

def all (m : OrdMap κ ν) (p : κ → ν → Bool) : Bool := m.toList.all fun (k, v) => p k v
def any (m : OrdMap κ ν) (p : κ → ν → Bool) : Bool := m.toList.any fun (k, v) => p k v

instance [Encode κ] [Encode ν] : Encode (OrdMap κ ν) := ⟨fun m => encode m.toList⟩

end OrdMap

/-- An ordered set kept as a sorted list without duplicates (a `BTreeSet`). -/
structure OrdSet (α : Type) where
  toList : List α
  deriving DecidableEq, Repr, Inhabited

namespace OrdSet
variable {α : Type} [Ord α]

def empty : OrdSet α := ⟨[]⟩

instance : EmptyCollection (OrdSet α) := ⟨empty⟩

private def insertList (a : α) : List α → List α
  | [] => [a]
  | b :: rest =>
    match compare a b with
    | .lt => a :: b :: rest
    | .eq => b :: rest
    | .gt => b :: insertList a rest

def insert (s : OrdSet α) (a : α) : OrdSet α := ⟨insertList a s.toList⟩
def contains (s : OrdSet α) (a : α) : Bool := s.toList.any fun b => compare a b == .eq
def size (s : OrdSet α) : Nat := s.toList.length
def ofList (l : List α) : OrdSet α := l.foldl insert empty
def union (s t : OrdSet α) : OrdSet α := t.toList.foldl insert s
def isSubset (s t : OrdSet α) : Bool := s.toList.all t.contains

instance [Encode α] : Encode (OrdSet α) := ⟨fun s => encode s.toList⟩

end OrdSet

/-- Byte strings (`SmallBlob` and friends). -/
abbrev Bytes := List UInt8

/-- UTF-8 bytes of a string. -/
def Bytes.ofString (s : String) : Bytes := s.toUTF8.toList

end Rgb
