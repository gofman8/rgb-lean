import Rgb.Core.Collections

/-!
# Occurrences

How many items of a type an operation may carry (`Occurrences`). On the wire an
occurrence is a `(min, max)` pair of `u16`; decoding refuses `(0, 0)` and
`min > max`.
-/

namespace Rgb

inductive Occurrences where
  | once
  | noneOrOnce
  | noneOrMore
  | onceOrMore
  | noneOrUpTo (max : UInt16)
  | onceOrUpTo (max : UInt16)
  | exactly (n : UInt16)
  | range (min max : UInt16)
  deriving DecidableEq, Repr, Inhabited

/-- Expected from `min` to `max` items, found `found` (`OccurrencesMismatch`). -/
structure OccurrencesMismatch where
  min : Nat
  max : Nat
  found : Nat
  deriving DecidableEq, Repr

/-- Why a `(min, max)` pair is not an occurrence (`OccurrencesError`). -/
inductive OccurrencesError where
  | zero
  | minExceedsMax
  deriving DecidableEq, Repr

namespace Occurrences

def minValue : Occurrences → Nat
  | once => 1 | noneOrOnce => 0 | noneOrMore => 0 | onceOrMore => 1
  | noneOrUpTo _ => 0 | onceOrUpTo _ => 1 | exactly n => n.toNat | range a _ => a.toNat

def maxValue : Occurrences → Nat
  | once | noneOrOnce => 1
  | noneOrMore | onceOrMore => 65535
  | noneOrUpTo m | onceOrUpTo m => m.toNat
  | exactly n => n.toNat
  | range _ b => b.toNat

/-- Accept `count` items (`Occurrences::check`). -/
def check (o : Occurrences) (count : Nat) : Except OccurrencesMismatch Unit :=
  if o.minValue ≤ count && count ≤ o.maxValue then .ok ()
  else .error ⟨o.minValue, o.maxValue, count⟩

/-- Decode a `(min, max)` pair (`TryFrom<RangeInclusive<u16>>`). -/
def ofRange (min max : UInt16) : Except OccurrencesError Occurrences :=
  if min == 0 && max == 0 then .error .zero
  else if min > max then .error .minExceedsMax
  else .ok <|
    if min == 0 && max == 1 then noneOrOnce
    else if min == 1 && max == 1 then once
    else if min == 0 && max == 65535 then noneOrMore
    else if min == 1 && max == 65535 then onceOrMore
    else if min == 0 then noneOrUpTo max
    else if min == 1 then onceOrUpTo max
    else if min == max then exactly min
    else range min max

end Occurrences

end Rgb
