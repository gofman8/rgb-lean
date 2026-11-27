import Rgb.Stl.Value

/-!
# Invoice amounts and allocations

The values an RGB invoice asks for (`rgb-invoicing` `amount` and `data`): a
fungible amount and its invoice text, a decimal coin amount with a precision,
and an allocation of a fraction of a unique token. Each parser returns the
error the library returns, from the first check that fails in the library's
order. Where the library panics, the function returns `none`.
-/

namespace Rgb.Invoice

/-! ## Text helpers -/

/-- Split at the first occurrence of a non-empty `sep` (Rust `str::split_once`). -/
def splitOnce (s sep : String) : Option (String × String) :=
  go [] s.toList
where
  go (acc : List Char) : List Char → Option (String × String)
    | [] => none
    | l@(c :: rest) =>
      if sep.toList.isPrefixOf l then
        some (String.ofList acc.reverse, String.ofList (l.drop sep.length))
      else go (c :: acc) rest

/-- Split at every `c` (Rust `str::split`): `n` separators give `n + 1` pieces. -/
def splitAll (s : String) (c : Char) : List String := (s.toList.splitOn c).map String.ofList

/-- Groups of `n` items from the left; the last group may be shorter. -/
def chunksOf {α : Type} (n : Nat) (l : List α) : List (List α) :=
  go l.length l
where
  go : Nat → List α → List (List α)
    | _, [] => []
    | 0, l => [l]
    | k + 1, l => l.take n :: go k (l.drop n)

/-! ## Integer text -/

/-- Why Rust's `str::parse` refuses an integer (`ParseIntError`). -/
inductive IntErrorKind where
  | empty
  | invalidDigit
  | posOverflow
  | negOverflow
  deriving DecidableEq, Repr, Inhabited

/-- Display text of the error. -/
def IntErrorKind.message : IntErrorKind → String
  | .empty => "cannot parse integer from empty string"
  | .invalidDigit => "invalid digit found in string"
  | .posOverflow => "number too large to fit in target type"
  | .negOverflow => "number too small to fit in target type"

/-- Rust `str::parse` into an integer type with range `[min, max]`: an optional `+`
(or `-` for a signed type), then decimal digits read from the left; the first
non-digit, or the first prefix out of range, decides the error. -/
def parseInteger (min max : Int) (s : String) : Except IntErrorKind Int :=
  match s.toList with
  | [] => .error .empty
  | ['+'] | ['-'] => .error .invalidDigit
  | '+' :: ds => digits 1 ds
  | '-' :: ds => if min < 0 then digits (-1) ds else digits 1 ('-' :: ds)
  | ds => digits 1 ds
where
  digits (sign : Int) (ds : List Char) : Except IntErrorKind Int :=
    ds.foldlM (fun acc c =>
      if c.isDigit then
        let v := acc * 10 + sign * ((c.toNat - '0'.toNat : Nat) : Int)
        if v > max then .error .posOverflow
        else if v < min then .error .negOverflow
        else .ok v
      else .error .invalidDigit) 0

/-- `str::parse::<u64>`. -/
def parseU64 (s : String) : Except IntErrorKind UInt64 :=
  (parseInteger 0 (2 ^ 64 - 1) s).map (·.toNat.toUInt64)

/-- `str::parse::<u32>`. -/
def parseU32 (s : String) : Except IntErrorKind UInt32 :=
  (parseInteger 0 (2 ^ 32 - 1) s).map (·.toNat.toUInt32)

/-- `str::parse::<i64>`. -/
def parseI64 (s : String) : Except IntErrorKind Int := parseInteger (-(2 ^ 63)) (2 ^ 63 - 1) s

/-! ## Invoice amount text -/

/-- Base32 alphabet of invoice amounts, without digits (`ENC_BASE32_NODIGIT`); the
position of a letter is its 5-bit value. -/
def amountAlphabet : List Char := "abcdefghkmnABCDEFGHKMNPQRSTVWXYZ".toList

/-- Why base32 text is refused (`fast32::DecodeError`). -/
inductive DecodeError where
  /-- A byte outside the alphabet, or a last character with non-zero unused bits. -/
  | invalidChar (char : Char) (index : Nat)
  /-- A text length no encoding gives, or more than 8 decoded bytes. -/
  | invalidLength (length : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Display text of the error. -/
def DecodeError.message : DecodeError → String
  | .invalidChar c i => s!"Invalid char of '{c}' at position {i}"
  | .invalidLength n => s!"Invalid length of {n}"

/-- Base32 text of bytes: 5-bit groups, most significant bit first, the last group
padded with zero bits, no `=` padding (`Alphabet32Nopad::encode`). -/
def base32Encode (bytes : Bytes) : String :=
  let n := (bytes.length * 8 + 4) / 5
  let v := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0 <<< (5 * n - 8 * bytes.length)
  String.ofList ((List.range n).map fun i =>
    amountAlphabet.getD ((v >>> (5 * (n - 1 - i))) % 32) 'a')

/-- Decode base32 text byte by byte, in fast32's order: the characters of whole
8-character blocks, then the length (a remainder of 1, 3 or 6 is refused), then the
other characters, then the unused low bits of the last character, which must be zero. -/
def base32Decode (s : String) : Except DecodeError Bytes := do
  let bs := s.toUTF8.toList
  let n := bs.length
  let full := n / 8 * 8
  let digit (b : UInt8) (i : Nat) : Except DecodeError Nat :=
    match amountAlphabet.idxOf? (Char.ofNat b.toNat) with
    | some d => .ok d
    | none => .error (.invalidChar (Char.ofNat b.toNat) i)
  let head ← (bs.take full).zipIdx.mapM fun (b, i) => digit b i
  if [1, 3, 6].contains (n % 8) then throw (.invalidLength n)
  let tail ← (bs.drop full).zipIdx.mapM fun (b, i) => digit b (full + i)
  let v := (head ++ tail).foldl (fun acc d => acc * 32 + d) 0
  let unused := 5 * n % 8
  if v % 2 ^ unused != 0 then
    throw (.invalidChar (Char.ofNat (bs.getLast?.getD 0).toNat) (n - 1))
  let k := 5 * n / 8
  return (List.range k).map fun i => ((v >>> unused >>> (8 * (k - 1 - i))) % 256).toUInt8

/-! ## Amounts -/

/-- A fungible amount in atoms (`Amount`, a `u64`). -/
structure Amount where
  v : UInt64
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

namespace Amount

/-- No atoms (`ZERO`). -/
def zero : Amount := ⟨0⟩

/-- The number of atoms. -/
def value (a : Amount) : UInt64 := a.v

/-- Invoice text: the little-endian bytes without trailing zero bytes (at least one byte
kept), in base32. -/
def display (a : Amount) : String :=
  let le := Bytes.le a.v.toNat 8
  base32Encode (le.take (max 1 (le.reverse.dropWhile (· == 0)).length))

/-- Read invoice text (`Amount::from_str`): base32 of at most 8 bytes, read as a
little-endian number; trailing zero bytes are accepted, so several texts give one amount. -/
def parse (s : String) : Except DecodeError Amount := do
  let bytes ← base32Decode s
  if bytes.length > 8 then throw (.invalidLength bytes.length)
  return ⟨(Bytes.leValue bytes).toUInt64⟩

/-- `amount * 10^decimals`, `none` on overflow (`with_precision_checked`,
`Precision::checked_convert`). `with_precision` computes the same product and panics on
overflow, as rgb-lib builds with overflow checks. -/
def withPrecisionChecked (amount : UInt64) (p : Precision) : Option Amount :=
  let v := amount.toNat * p.multiplier
  if v < 2 ^ 64 then some ⟨v.toUInt64⟩ else none

/-- `amount * 10^decimals`, capped at the largest `u64` (`Precision::saturating_convert`). -/
def withPrecisionSaturating (amount : UInt64) (p : Precision) : Amount :=
  ⟨(min (amount.toNat * p.multiplier) (2 ^ 64 - 1)).toUInt64⟩

/-- Whole units (`floor`). -/
def floor (a : Amount) (p : Precision) : UInt64 := (a.v.toNat / p.multiplier).toUInt64

/-- Atoms below one unit (`rem`). -/
def rem (a : Amount) (p : Precision) : UInt64 := (a.v.toNat % p.multiplier).toUInt64

/-- Whole units and the rest (`split`). -/
def split (a : Amount) (p : Precision) : UInt64 × UInt64 := (a.floor p, a.rem p)

/-- Whole units, one more when a rest remains (`ceil`). -/
def ceil (a : Amount) (p : Precision) : UInt64 := a.floor p + if a.rem p > 0 then 1 else 0

/-- Whole units rounded half up (`round`). -/
def round (a : Amount) (p : Precision) : UInt64 :=
  (a.v.toNat / p.multiplier + 2 * (a.rem p).toNat / p.multiplier).toUInt64

/-- Sum capped at the largest `u64`. -/
def saturatingAdd (a b : Amount) : Amount := ⟨(min (a.v.toNat + b.v.toNat) (2 ^ 64 - 1)).toUInt64⟩

/-- Difference, 0 when `b > a`. -/
def saturatingSub (a b : Amount) : Amount := ⟨(a.v.toNat - b.v.toNat).toUInt64⟩

/-- Sum, `none` on overflow. -/
def checkedAdd (a b : Amount) : Option Amount :=
  if a.v.toNat + b.v.toNat < 2 ^ 64 then some ⟨a.v + b.v⟩ else none

/-- Difference, `none` when `b > a`. -/
def checkedSub (a b : Amount) : Option Amount := if b.v ≤ a.v then some ⟨a.v - b.v⟩ else none

/-- Sum of amounts (`Sum`): saturating. -/
def sum (l : List Amount) : Amount := l.foldl saturatingAdd zero

end Amount

/-! ## Coin amounts -/

/-- `invalid precision`: a fraction with more digits than the precision allows. -/
inductive PrecisionError where
  | invalidPrecision
  deriving DecidableEq, Repr

/-- A decimal amount: whole units, the fraction in atoms, and the precision (`CoinAmount`). -/
structure CoinAmount where
  /-- Whole units. -/
  int : UInt64
  /-- Atoms below one unit; `with` keeps it below `10^decimals`. -/
  fract : UInt64
  precision : Precision
  deriving DecidableEq, Repr, Inhabited

/-- Why `CoinAmount::from_str` refuses a text (`AmountParseError`). -/
inductive AmountParseError where
  | invalidInt (e : IntErrorKind)
  | invalidFract (e : IntErrorKind)
  | invalidPrecision (e : IntErrorKind)
  /-- The precision does not fit a byte. -/
  | precisionOverflow
  /-- The precision fits a byte but exceeds 18. -/
  | unknownPrecision (decimals : Nat)
  deriving DecidableEq, Repr

/-- Display text of the error. -/
def AmountParseError.message : AmountParseError → String
  | .invalidInt e => s!"invalid amount integer part - {e.message}"
  | .invalidFract e => s!"invalid amount fractional part - {e.message}"
  | .invalidPrecision e => s!"invalid amount precision - {e.message}"
  | .precisionOverflow | .unknownPrecision _ => "invalid amount precision exceeding 18"

namespace CoinAmount

/-- Split an amount at the precision (`new`). -/
def new (a : Amount) (p : Precision) : CoinAmount := ⟨a.floor p, a.rem p, p⟩

/-- `with`: the fraction must be below `10^decimals`; the integer part is not checked. -/
def withParts (int fract : UInt64) (p : Precision) : Except PrecisionError CoinAmount :=
  if fract.toNat ≥ p.multiplier then .error .invalidPrecision else .ok ⟨int, fract, p⟩

/-- `int * 10^decimals + fract` (`to_amount_unchecked`); `none` where the library panics
on overflow. -/
def toAmountUnchecked (c : CoinAmount) : Option Amount :=
  let v := c.int.toNat * c.precision.multiplier + c.fract.toNat
  if v < 2 ^ 64 then some ⟨v.toUInt64⟩ else none

/-- The fraction as `decimals` digits with leading zeros; `none` when it has more digits
(the library panics with "float precision overflow"). -/
def fractionDigits (c : CoinAmount) : Option String :=
  let f := toString c.fract.toNat
  let d := c.precision.decimals
  if f.length > d then none else some (String.ofList (List.replicate (d - f.length) '0') ++ f)

/-- Digits in groups of three from the right, joined with `fill`. -/
def group3 (fill : Char) (s : String) : String :=
  String.intercalate (String.singleton fill)
    ((chunksOf 3 s.toList.reverse).map fun g => String.ofList g.reverse).reverse

/-- Display: the integer; when the fraction is not zero, `.` and its digits without
trailing zeros; then `~` and the number of decimals. -/
def display (c : CoinAmount) : Option String := do
  let trimmed (f : String) : String := String.ofList (f.toList.reverse.dropWhile (· == '0')).reverse
  let fract ← if c.fract > 0 then c.fractionDigits.map fun f => "." ++ trimmed f else some ""
  return s!"{c.int.toNat}{fract}~{c.precision.decimals}"

/-- Alternate display (`{:#}`): the integer and the full-width fraction in groups of
three, always with `.`, without `~`. The fill must be a space or `_`; any other fill, and
a fraction wider than the precision (every indivisible amount), panics. -/
def displayAlternate (c : CoinAmount) (fill : Char := ' ') : Option String := do
  if fill != ' ' && fill != '_' then none
  let f ← c.fractionDigits
  return group3 fill (toString c.int.toNat) ++ "." ++ group3 fill f

/-- Read a text (`CoinAmount::from_str`) without its spaces and `_`: no `.` means fraction
`0`, no `~` means as many decimals as fraction bytes. The display of a whole amount
(`10~8`) does not read back, and the fraction is not checked against the precision. -/
def parse (s : String) : Except AmountParseError CoinAmount := do
  let s := String.ofList (s.toList.filter fun c => c != ' ' && c != '_')
  let (int, remain) := (splitOnce s ".").getD (s, "0")
  let (fract, prec) := (splitOnce remain "~").getD (remain, "")
  let decimals ← if prec.isEmpty then pure fract.utf8ByteSize
    else (parseU64 prec).map (·.toNat) |>.mapError .invalidPrecision
  let int ← (parseU64 int).mapError .invalidInt
  let fract ← (parseU64 fract).mapError .invalidFract
  if decimals > 255 then throw .precisionOverflow
  match Precision.ofNat? decimals with
  | some p => return ⟨int, fract, p⟩
  | none => throw (.unknownPrecision decimals)

end CoinAmount

/-! ## Allocations of unique tokens -/

/-- Owned fraction of a unique token (`OwnedFraction`, a `u64`). -/
structure OwnedFraction where
  v : UInt64
  deriving DecidableEq, Ord, Hashable, Repr, Inhabited

namespace OwnedFraction

/-- No fraction (`ZERO`). -/
def zero : OwnedFraction := ⟨0⟩

/-- The fraction as a number. -/
def value (f : OwnedFraction) : UInt64 := f.v

/-- Sum capped at the largest `u64`. -/
def saturatingAdd (a b : OwnedFraction) : OwnedFraction :=
  ⟨(min (a.v.toNat + b.v.toNat) (2 ^ 64 - 1)).toUInt64⟩

/-- Difference, 0 when `b > a`. -/
def saturatingSub (a b : OwnedFraction) : OwnedFraction := ⟨(a.v.toNat - b.v.toNat).toUInt64⟩

/-- Sum, `none` on overflow. -/
def checkedAdd (a b : OwnedFraction) : Option OwnedFraction :=
  if a.v.toNat + b.v.toNat < 2 ^ 64 then some ⟨a.v + b.v⟩ else none

/-- Difference, `none` when `b > a`. -/
def checkedSub (a b : OwnedFraction) : Option OwnedFraction :=
  if b.v ≤ a.v then some ⟨a.v - b.v⟩ else none

end OwnedFraction

/-- A fraction of the token with an index (`Allocation`). -/
structure Allocation where
  index : TokenIndex
  fraction : OwnedFraction
  deriving DecidableEq, Repr, Inhabited

/-- Why allocation text is refused (`AllocationParseError`). -/
inductive AllocationParseError where
  | invalidIndex (s : String)
  /-- The fraction text, lower-cased. -/
  | invalidFraction (s : String)
  | wrongFormat
  deriving DecidableEq, Repr

/-- Display text of the error. -/
def AllocationParseError.message : AllocationParseError → String
  | .invalidIndex s => s!"invalid token index {s}."
  | .invalidFraction s => s!"invalid fraction {s}."
  | .wrongFormat => "allocation must have format <fraction>@<token_index>."

namespace Allocation

/-- Text `fraction@index`. -/
def display (a : Allocation) : String := s!"{a.fraction.v.toNat}@{a.index.v.toNat}"

/-- Read `fraction@index` (`Allocation::from_str`): split at the first `@`; the index
(a `u32`) is checked before the fraction (a `u64`). The lower-casing of the fraction text
in the error covers ASCII letters only. -/
def parse (s : String) : Except AllocationParseError Allocation :=
  match splitOnce s "@" with
  | none => .error .wrongFormat
  | some (fraction, index) =>
    match parseU32 index, parseU64 fraction with
    | .error _, _ => .error (.invalidIndex index)
    | .ok _, .error _ => .error (.invalidFraction fraction.toLower)
    | .ok i, .ok f => .ok ⟨⟨i⟩, ⟨f⟩⟩

/-- Structured state holding the allocation (`From<Allocation> for RevealedData`). -/
def toStrictValue (a : Allocation) : StrictValue := .allocation a.index a.fraction.v

/-- Allocation of structured state (`From<RevealedData> for Allocation`); `none` where
the library panics on other data. -/
def ofStrictValue? : StrictValue → Option Allocation
  | .allocation i f => some ⟨i, ⟨f⟩⟩
  | _ => none

end Allocation

/-- Non-fungible state of an invoice (`NonFungible`). -/
inductive NonFungible where
  | fractionedToken (a : Allocation)
  deriving DecidableEq, Repr, Inhabited

namespace NonFungible

/-- The text of the allocation. -/
def display : NonFungible → String
  | .fractionedToken a => a.display

/-- Read allocation text (`NonFungible::from_str`). -/
def parse (s : String) : Except AllocationParseError NonFungible :=
  (Allocation.parse s).map .fractionedToken

end NonFungible

end Rgb.Invoice
