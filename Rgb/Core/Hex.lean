/-!
# Hex text

Hex as RGB and rgb-lib write and read it: lowercase digits out (`hex::encode`, `ToHex`),
digits of either case in (`hex::decode`, `FromHex`).
-/

namespace Rgb.Hex

/-- Lowercase hex digit of `n < 16`. -/
def digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Value of a hex digit, in either case. -/
def digitValue? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- An ASCII hex digit, in either case. -/
def isDigit (c : Char) : Bool := (digitValue? c).isSome

/-- A lowercase hex digit. -/
def isLowerDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The low `width` hex digits of `n`, lowercase and zero-padded. -/
def ofNat (n width : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i => digit ((n >>> (4 * i)) % 16))

/-- Two lowercase hex digits of a byte. -/
def ofByte (b : UInt8) : String := ofNat b.toNat 2

/-- Lowercase hex of bytes (`hex::encode`). -/
def ofBytes (b : List UInt8) : String := String.join (b.map ofByte)

/-- Value of a nonempty string of hex digits of either case. -/
def toNat? (s : String) : Option Nat :=
  if s.isEmpty then none else s.toList.foldlM (fun acc c => (digitValue? c).map (acc * 16 + ·)) 0

/-- Bytes of hex text of either case (`hex::decode`); none for an odd length or a character
that is not a hex digit. -/
def toBytes? (s : String) : Option (List UInt8) := go s.toList
where
  go : List Char → Option (List UInt8)
    | [] => some []
    | [_] => none
    | h :: l :: rest => do
      let hi ← digitValue? h
      let lo ← digitValue? l
      return (16 * hi + lo).toUInt8 :: (← go rest)

end Rgb.Hex
