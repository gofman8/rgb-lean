import Rgb.Invoice.Invoice
import Rgb.Schemas.Standard

/-!
# Invoice scenarios

Invoice amounts, coin amounts and allocations; invoices printed and read back
with a codec that knows the identifiers of rgb-invoicing's own tests and the
schema ids of rgb-lib; each parse error, and which error wins when an invoice
has several faults; the assignment rgb-lib reads for each schema; recipient ids
and transport endpoints.
-/

namespace Rgb.Examples.InvoiceScenario

open Rgb Rgb.Invoice Rgb.Lib

/-! ## A codec for the scenario identifiers -/

/-- Text without dashes. -/
def dashless (s : String) : String := String.ofList (s.toList.filter (· != '-'))

/-- Split at the last `c`. -/
def rsplitOnce (s : String) (c : Char) : Option (String × String) :=
  let parts := splitAll s c
  if parts.length < 2 then none
  else some (String.intercalate (String.singleton c) parts.dropLast, parts.getLastD "")

/-- Read an identifier as `from_baid64_str` does, with the table in place of the decoding
and the checksum: an `hri:` prefix (split at the last `:`) must name `hri`, a `#` suffix
(a mnemonic) is dropped, dashes are ignored. -/
def baidLookup {α : Type} (hri : String) (table : List (String × α)) (s : String) :
    Option α := do
  let body ← match rsplitOnce s ':' with
    | some (h, rest) => if h == hri then some rest else none
    | none => some s
  let body := ((splitOnce body "#").map (·.1)).getD body
  (table.find? fun e => dashless e.1 == dashless body).map (·.2)

/-- Text of an identifier in the table. -/
def baidShow {α : Type} [BEq α] (table : List (String × α)) (a : α) : String :=
  ((table.find? (·.2 == a)).map (·.1)).getD "unknown"

/-- Contract of rgb-invoicing's NIA test. -/
def cidNia : ContractId := ⟨Digest.of Tag.operation ["nia genesis"]⟩
/-- Contract of rgb-invoicing's UDA test. -/
def cidUda : ContractId := ⟨Digest.of Tag.operation ["uda genesis"]⟩
/-- Contract of rgb-invoicing's tests with query parameters. -/
def cidOther : ContractId := ⟨Digest.of Tag.operation ["other genesis"]⟩

/-- Contract ids of rgb-invoicing's tests. -/
def contracts : List (String × ContractId) :=
  [ ("eIbQx5Am-XRDjj01-RM~5eo7-rv2nluD-OnBJRAy-S9~Yfts", cidNia)
  , ("tx8NOyGe-NkPZex~-U0J_1om-CfrOeoO-7di9xZb-vT3nxyo", cidUda)
  , ("3NoxsLum-cRPebTV-gTZY8qY-KS20lx7-OqgtBls-t7muan4", cidOther) ]

/-- Schema of rgb-invoicing's tests; rgb-lib does not know it. -/
def testSchema : SchemaId := ⟨Digest.of Tag.schema ["test schema"]⟩
/-- Schema of rgb-invoicing's test without an allocation. -/
def otherSchema : SchemaId := ⟨Digest.of Tag.schema ["other schema"]⟩

/-- Bare text, mnemonic and id: rgb-lib's five schemas, then two of rgb-invoicing's tests. -/
def schemas : List (String × String × SchemaId) :=
  [ ("RWhwUfTMpuP2Zfx1~j4nswCANGeJrYOqDcKelaMV4zU", "remote-digital-pegasus", Schemas.nia.schemaId)
  , ("~6rjymf3GTE840lb5JoXm2aFwE8eWCk3mCjOf_mUztE", "spider-montana-fantasy", Schemas.uda.schemaId)
  , ("JgqK5hJX9YBT4osCV7VcW_iLTcA5csUCnLzvaKTTrNY", "mars-house-friend", Schemas.cfa.schemaId)
  , ("A2n9kPNWtXUqwQJyXfY8yGHKyEPZgvrNYYYPGhXawOk", "graph-salute-retro", Schemas.ifa.schemaId)
  , ("3I0xZVEQnQxYVk7vDnh5uNtQyUfsmThw6dX9n_Gvb5o", "mama-swing-album", Schemas.bfa.schemaId)
  , ("XvmU3d4_nQQ8S7oagbXi07x5vjMm7P~ERukQNX6SC4M", "ladder-ecology-civil", testSchema)
  , ("V8ujLLtH2k2QSmaDpZI3o06ACIm2UNT0TZl11FiqRuY", "cherry-distant-bingo", otherSchema) ]

/-- Bare text and id of each schema. -/
def schemaTexts : List (String × SchemaId) := schemas.map fun (t, _, sid) => (t, sid)

/-- Bob's concealed seal. -/
def bobSeal : SecretSeal := ⟨Digest.of Tag.secretSeal ["bob"]⟩

/-- The concealed seal of rgb-invoicing's tests. -/
def seals : List (String × SecretSeal) :=
  [("4vm1CX2Z-K8hMo59-e7dgGBS-Jka7mYn-Xe~yP85-yUiHHxr-aVlYa", bobSeal)]

/-- P2WPKH output of rgb-invoicing's witness-vout test. -/
def bobVout : Pay2Vout := ⟨.wpkh ((ofHex? "c709ed6c37348cc00e8dd3ce9fb9683ec24c15a6").getD [])⟩

/-- The witness output of rgb-invoicing's tests. -/
def vouts : List (String × Pay2Vout) :=
  [("A8cJ7Ww3-NIzADo3-Tzp_5aD-7CTBWmA-AAAAAAA-AAAAAAA-ALSQkcw", bobVout)]

/-- `Pay2Vout::from_str` with the errors `from_baid64_str` gives first. -/
def readVout (s : String) : Except String Pay2Vout :=
  if (rsplitOnce s ':').any (·.1 != "wvout") then
    .error s!"invalid human-readable prefix in {s} (wvout is expected)."
  else match baidLookup "wvout" vouts s with
    | some p => .ok p
    | none => .error s!"invalid length of identifier {s}."

/-- Field size of secp256k1. -/
def secpP : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- `b ^ e % m` by repeated squaring, for `e < 2^256`. -/
def powMod (b e m : Nat) : Nat := go 256 (b % m) e 1
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, acc => acc
    | k + 1, b, e, acc =>
      if e == 0 then acc else go k (b * b % m) (e / 2) (if e % 2 == 1 then acc * b % m else acc)

/-- The x coordinate of a secp256k1 point: `x < p` and `x³ + 7` is a square mod `p`. -/
def onCurve (bytes : Bytes) : Bool :=
  let x := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0
  bytes.length == 32 && x < secpP && powMod ((x ^ 3 + 7) % secpP) ((secpP - 1) / 2) secpP == 1

/-- Codec of the scenarios: lookups in the tables above, and the real curve check. -/
def codec : IdCodec where
  contractId? := baidLookup "rgb" contracts
  showContractId c := "rgb:" ++ baidShow contracts c
  schemaId? := baidLookup "rgb:sch" schemaTexts
  showSchemaId sid := baidShow schemaTexts sid
  showSchemaIdFull sid :=
    match schemas.find? (·.2.2 == sid) with
    | some (t, m, _) => "rgb:sch:" ++ t ++ "#" ++ m
    | none => "unknown"
  secretSeal? := baidLookup "utxob" seals
  showSecretSeal s := "utxob:" ++ baidShow seals s
  pay2vout? := readVout
  showPay2Vout p := "wvout:" ++ baidShow vouts p
  xOnlyValid := onCurve

/-- Read an invoice with the scenario codec. -/
def parse (s : String) : Except InvoiceParseError RgbInvoice := RgbInvoice.parse codec s

/-- Read, then print. -/
def roundTrip (s : String) : Except InvoiceParseError String := (parse s).map (·.display codec)

/-! ## Texts of the scenarios -/

def cNia : String := "eIbQx5Am-XRDjj01-RM~5eo7-rv2nluD-OnBJRAy-S9~Yfts"
def cOther : String := "3NoxsLum-cRPebTV-gTZY8qY-KS20lx7-OqgtBls-t7muan4"
def sTest : String := "XvmU3d4_nQQ8S7oagbXi07x5vjMm7P~ERukQNX6SC4M"
def sealText : String := "4vm1CX2Z-K8hMo59-e7dgGBS-Jka7mYn-Xe~yP85-yUiHHxr-aVlYa"
def voutText : String := "A8cJ7Ww3-NIzADo3-Tzp_5aD-7CTBWmA-AAAAAAA-AAAAAAA-ALSQkcw"
def bob : String := s!"bc:utxob:{sealText}"
def bobW : String := s!"bc:wvout:{voutText}"
/-- Internal key of rgb-invoicing's witness-vout test. -/
def ipk : String := "750f58bcca0fdb11891e7979d829b8c56e0963dba08c44f54a256cf7dbc09caf"
/-- Public key of rgb-invoicing's `pk` test. -/
def pkHex : String := "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
/-- The invoice most cases extend: 100 atoms to Bob's concealed seal on mainnet. -/
def base : String := s!"rgb:{cOther}/{sTest}/BF/{bob}"
/-- `base` with a query. -/
def withQuery (q : String) : String := base ++ "?" ++ q

/-! ## Invoice amount text -/

-- the amounts of rgb-invoicing's tests: 0, 100 and 200 atoms
#guard (Amount.mk 0).display == "aa"
#guard (Amount.mk 100).display == "BF"
#guard (Amount.mk 200).display == "Sa"
-- one byte gives two characters, eight bytes thirteen
#guard (Amount.mk 256).display == "aaaF"
#guard (Amount.mk 18446744073709551615).display == "ZZZZZZZZZZZZY"
-- every display reads back
#guard ([0, 1, 100, 255, 256, 65536, 123456789, 18446744073709551615] : List UInt64).all
  fun v => Amount.parse (Amount.mk v).display == .ok ⟨v⟩
-- trailing zero bytes are accepted, so several texts give one amount; empty text is 0
#guard Amount.parse "BFaa" == .ok ⟨100⟩
#guard Amount.parse "" == .ok ⟨0⟩
-- case matters: `bF` is another amount
#guard Amount.parse "bF" == .ok ⟨12⟩
-- a length of 1, 3 or 6 (modulo 8) is refused before the characters are read
#guard Amount.parse "1" == .error (.invalidLength 1)
#guard Amount.parse "abc" == .error (.invalidLength 3)
-- the alphabet has no digits and no `j`
#guard Amount.parse "B1" == .error (.invalidChar '1' 1)
#guard Amount.parse "Bj" == .error (.invalidChar 'j' 1)
-- the characters of whole 8-character blocks are read before the length is checked
#guard Amount.parse "abcdefg1h" == .error (.invalidChar '1' 7)
-- the unused low bits of the last character must be zero
#guard Amount.parse "BG" == .error (.invalidChar 'G' 1)
-- at most 8 bytes
#guard Amount.parse "aaaaaaaaaaaaaaa" == .error (.invalidLength 9)
-- text is read byte by byte: `é` is two bytes, and its first byte reads as `Ã`
#guard Amount.parse "aé" == .error (.invalidLength 3)
#guard Amount.parse "aaé" == .error (.invalidChar 'Ã' 2)
#guard (DecodeError.invalidChar '1' 7).message == "Invalid char of '1' at position 7"

-- whole units and the rest; rounding is half up
#guard (Amount.mk 1234567).split .centi == (12345, 67)
#guard (Amount.mk 1250).round .centi == 13
#guard (Amount.mk 1249).round .centi == 12
#guard (Amount.mk 1201).ceil .centi == 13
#guard (Amount.mk 1200).ceil .centi == 12
-- with a precision: checked, saturating
#guard Amount.withPrecisionChecked 1844674407370955161 .deci == some ⟨18446744073709551610⟩
#guard Amount.withPrecisionChecked 1844674407370955162 .deci == none
#guard Amount.withPrecisionSaturating 1844674407370955162 .deci == ⟨18446744073709551615⟩
-- a sum saturates
#guard Amount.sum [⟨18446744073709551615⟩, ⟨1⟩] == ⟨18446744073709551615⟩
#guard (Amount.mk 1).checkedSub ⟨2⟩ == none
#guard (Amount.mk 1).saturatingSub ⟨2⟩ == ⟨0⟩

/-! ## Coin amounts -/

-- the displays of rgb-invoicing's tests, at 8 decimals
#guard (CoinAmount.new ⟨1000043608195⟩ .centiMicro).display == some "10000.43608195~8"
#guard (CoinAmount.new ⟨1000043608195⟩ .centiMicro).displayAlternate == some "10 000.43 608 195"
#guard (CoinAmount.new ⟨1000008195⟩ .centiMicro).display == some "10.00008195~8"
#guard (CoinAmount.new ⟨1000008195⟩ .centiMicro).displayAlternate == some "10.00 008 195"
#guard (CoinAmount.new ⟨1000000500⟩ .centiMicro).display == some "10.000005~8"
#guard (CoinAmount.new ⟨1000000500⟩ .centiMicro).displayAlternate '_' == some "10.00_000_500"
#guard (CoinAmount.new ⟨1000000000⟩ .centiMicro).display == some "10~8"
#guard (CoinAmount.new ⟨1000000000⟩ .centiMicro).displayAlternate '_' == some "10.00_000_000"
-- another fill character panics
#guard (CoinAmount.new ⟨1⟩ .centi).displayAlternate '.' == none
-- the display of a whole amount does not read back
#guard CoinAmount.parse "10~8" == .error (.invalidInt .invalidDigit)
-- without `.` the fraction is `0`, one character wide: one decimal
#guard CoinAmount.parse "10" == .ok ⟨10, 0, .deci⟩
-- the fraction is in atoms of the stated precision: `10.5~8` is 10.00000005
#guard CoinAmount.parse "10.5~8" == .ok ⟨10, 5, .centiMicro⟩
#guard (CoinAmount.mk 10 5 .centiMicro).display == some "10.00000005~8"
-- while 10.5 at 8 decimals displays as `10.5~8`
#guard (CoinAmount.new ⟨1050000000⟩ .centiMicro).display == some "10.5~8"
-- spaces and `_` are dropped; without `~` the precision is the width of the fraction
#guard CoinAmount.parse "1 000_000.50" == .ok ⟨1000000, 50, .centi⟩
-- the precision is read first, then the integer, then the fraction
#guard CoinAmount.parse "x.y~z" == .error (.invalidPrecision .invalidDigit)
#guard CoinAmount.parse "x.y~2" == .error (.invalidInt .invalidDigit)
#guard CoinAmount.parse "1.y~2" == .error (.invalidFract .invalidDigit)
#guard CoinAmount.parse "1." == .error (.invalidFract .empty)
#guard CoinAmount.parse "18446744073709551616" == .error (.invalidInt .posOverflow)
-- a precision above 255, then one above 18
#guard CoinAmount.parse "1.5~256" == .error .precisionOverflow
#guard CoinAmount.parse "1.5~19" == .error (.unknownPrecision 19)
#guard (CoinAmount.parse "1.5~19").mapError (·.message)
  == .error "invalid amount precision exceeding 18"
#guard (CoinAmount.parse "x").mapError (·.message)
  == .error "invalid amount integer part - invalid digit found in string"
-- the parser does not enforce `with`, and such a value has no display
#guard CoinAmount.parse "1.123~2" == .ok ⟨1, 123, .centi⟩
#guard CoinAmount.withParts 1 123 .centi == .error .invalidPrecision
#guard (CoinAmount.mk 1 123 .centi).display == none
-- an indivisible amount displays, but has no alternate display
#guard (CoinAmount.new ⟨5⟩ .indivisible).display == some "5~0"
#guard (CoinAmount.new ⟨5⟩ .indivisible).displayAlternate == none
-- back to atoms, the product or the sum may overflow
#guard (CoinAmount.mk 1844674407370955161 5 .deci).toAmountUnchecked
  == some ⟨18446744073709551615⟩
#guard (CoinAmount.mk 1844674407370955161 6 .deci).toAmountUnchecked == none

/-! ## Allocations -/

#guard Allocation.parse "1@0" == .ok ⟨⟨0⟩, ⟨1⟩⟩
#guard (Allocation.mk ⟨0⟩ ⟨1⟩).display == "1@0"
#guard Allocation.parse "10" == .error .wrongFormat
-- the index is read before the fraction
#guard Allocation.parse "x@y" == .error (.invalidIndex "y")
-- the fraction text in the error is lower-cased
#guard Allocation.parse "X@1" == .error (.invalidFraction "x")
-- an index is a `u32`; Rust integer text may start with `+`
#guard Allocation.parse "1@4294967296" == .error (.invalidIndex "4294967296")
#guard Allocation.parse "+1@+2" == .ok ⟨⟨2⟩, ⟨1⟩⟩
-- split at the first `@`
#guard Allocation.parse "1@2@3" == .error (.invalidIndex "2@3")
#guard (Allocation.parse "1@x").mapError (·.message) == .error "invalid token index x."
-- an allocation is the structured state of a UDA token
#guard Allocation.ofStrictValue? (Allocation.mk ⟨3⟩ ⟨7⟩).toStrictValue == some ⟨⟨3⟩, ⟨7⟩⟩
#guard Allocation.ofStrictValue? (.amount 5) == none
#guard (OwnedFraction.mk 18446744073709551615).checkedAdd ⟨1⟩ == none
#guard (OwnedFraction.mk 18446744073709551615).saturatingAdd ⟨1⟩ == ⟨18446744073709551615⟩

/-! ## Invoice state -/

-- empty text is void; an amount is tried before an allocation
#guard InvoiceState.parse "" == .ok .void
#guard InvoiceState.parse "BF" == .ok (.amount ⟨100⟩)
#guard InvoiceState.parse "1@0" == .ok (.data (.fractionedToken ⟨⟨0⟩, ⟨1⟩⟩))
#guard InvoiceState.parse "~" == .error (.parseError "~")
#guard (InvoiceState.parse "BF").map (·.stateType) == .ok .fungible

/-! ## Invoices that read back unchanged -/

/-- rgb-invoicing's test invoices; each displays as the text it was read from. -/
def canonical : List String :=
  [ s!"rgb:{cNia}/{sTest}/BF/{bob}"
  , s!"rgb:tx8NOyGe-NkPZex~-U0J_1om-CfrOeoO-7di9xZb-vT3nxyo/{sTest}/1@0/{bob}"
  , s!"rgb:{cNia}/{sTest}/Sa/{bobW}"
  , s!"rgb:{cNia}/{sTest}/Sa/{bobW}+{ipk}"
  , s!"rgb:{cNia}/{sTest}/~/{bob}"
  , s!"rgb:{cNia}/V8ujLLtH2k2QSmaDpZI3o06ACIm2UNT0TZl11FiqRuY/~/{bob}"
  , s!"rgb:~/{sTest}/~/{bob}"
  , s!"rgb:~/~/~/{bob}"
  , s!"rgb:{cNia}/~/~/{bob}"
  , base
  , withQuery "assignment_name=assetOwner"
  , withQuery "expiry=1682086371"
  , withQuery s!"pk={pkHex}"
  , withQuery "enc=0"
  , withQuery "enc=1"
  , withQuery "unknown=new"
  , withQuery "unknown=new&another=new"
  , withQuery "expiry=1682086371&unknown=new"
  , withQuery ":@-%20%23=?/.%26%3D"
  , withQuery "endpoints=rpc://host.example.com"
  , withQuery "endpoints=rpcs://user:pass@host-1.ex-ample.com:1234"
  , withQuery "endpoints=rpcs://%5B2001:db8::1%5D:1234"
  , withQuery "endpoints=https://host.example.com"
  , withQuery "endpoints=wss://host.example.com"
  , withQuery "endpoints=storm://_/"
  , withQuery ("endpoints=rpcs://host1.example.com,http://host2.example.com," ++
      "ws://host3.example.com") ]

#guard canonical.all fun s => roundTrip s == .ok s

-- what the first one holds
#guard parse s!"rgb:{cNia}/{sTest}/BF/{bob}" == .ok {
    contract := some cidNia
    schema := some testSchema
    assignmentState := some (.amount ⟨100⟩)
    beneficiary := ⟨.bitcoinMainnet, .blindedSeal bobSeal⟩ }
-- the alternate display drops the dashes, and that text reads back
#guard (parse s!"rgb:{cNia}/{sTest}/BF/{bob}").map (·.display codec true)
  == .ok (dashless s!"rgb:{cNia}/{sTest}/BF/{bob}")
#guard roundTrip (dashless s!"rgb:{cNia}/{sTest}/BF/{bob}") == .ok s!"rgb:{cNia}/{sTest}/BF/{bob}"
-- the witness output and its internal key
#guard (parse s!"rgb:~/~/~/{bobW}+{ipk}").map (·.beneficiary)
  == .ok ⟨.bitcoinMainnet, .witnessVout bobVout (some ⟨(ofHex? ipk).getD []⟩)⟩
-- transports, and query text percent-decoded
#guard (parse (withQuery "endpoints=rpcs://user:pass@host-1.ex-ample.com:1234")).map
  (·.transports) == .ok [.jsonRpc true "user:pass@host-1.ex-ample.com:1234"]
#guard (parse (withQuery "endpoints=rpcs://%5B2001:db8::1%5D:1234")).map (·.transports)
  == .ok [.jsonRpc true "[2001:db8::1]:1234"]
#guard (parse (withQuery ":@-%20%23=?/.%26%3D")).map (·.unknownQuery) == .ok [(":@- #", "?/.&=")]

/-! ## What reading and printing normalise -/

-- the key to lower case, the amount to its shortest text, the chain prefix to lower case
#guard roundTrip (withQuery s!"pk={pkHex.toUpper}") == .ok (withQuery s!"pk={pkHex}")
#guard roundTrip s!"rgb:{cOther}/{sTest}/BFaa/{bob}" == .ok base
#guard roundTrip s!"rgb:{cOther}/{sTest}/BF/BC:utxob:{sealText}" == .ok base
#guard roundTrip s!"rgb:~/~/~/{bobW}+{ipk.toUpper}" == .ok s!"rgb:~/~/~/{bobW}+{ipk}"
-- the contract id may come with `rgb:` (the invoice then starts `rgb:rgb:`) or without dashes
#guard roundTrip s!"rgb:rgb:{cOther}/{sTest}/BF/{bob}" == .ok base
#guard roundTrip s!"rgb:{dashless cOther}/{sTest}/BF/{bob}" == .ok base
-- the schema id may come with `rgb:sch:`
#guard roundTrip s!"rgb:{cOther}/rgb:sch:{sTest}/BF/{bob}" == .ok base
-- a seal without its `utxob:` prefix and dashes gets them back
#guard roundTrip s!"rgb:{cOther}/{sTest}/BF/bc:{dashless sealText}" == .ok base
-- segments after the beneficiary, and the fragment, are dropped
#guard roundTrip (base ++ "/more/segments#fragment") == .ok base
-- a repeated key keeps its first place and its last value
#guard roundTrip (withQuery "b=1&a=2&b=3") == .ok (withQuery "b=3&a=2")
-- an escape that is not needed is decoded; `+` is not a space
#guard roundTrip (withQuery "a=%41+b") == .ok (withQuery "a=A+b")
-- storm drops its host; empty values are kept
#guard roundTrip (withQuery "endpoints=storm://host") == .ok (withQuery "endpoints=storm://_/")
#guard roundTrip (withQuery "a=") == .ok (withQuery "a=")
-- UTF-8 text is decoded and encoded again
#guard (parse (withQuery "a=%C3%A9")).map (·.unknownQuery) == .ok [("a", "é")]
#guard roundTrip (withQuery "a=%C3%A9") == .ok (withQuery "a=%C3%A9")

/-! ## Where printing, then reading, differs -/

-- `%` is not encoded: a value holding `%` prints a bad escape
#guard (parse (withQuery "a=%25")).map (·.display codec) == .ok (withQuery "a=%")
#guard roundTrip (withQuery "a=%") == .error .invalid
-- `|` is not encoded either, and is not a URI character
#guard (parse (withQuery "a=%7C")).map (·.display codec) == .ok (withQuery "a=|")
#guard parse (withQuery "a=|") == .error .invalid
/-- An invoice whose transport host holds `,`: it reads back as two transports. -/
def commaHost : RgbInvoice :=
  (RgbInvoiceBuilder.new ⟨.bitcoinMainnet, .blindedSeal bobSeal⟩
    |>.addTransportRaw (.jsonRpc false "a,rpc://b")).finish
-- a transport host holding `,` reads back as two transports
#guard (parse (commaHost.display codec)).map (·.transports)
  == .ok [.jsonRpc false "a", .jsonRpc false "b"]

/-! ## Each parse error, in the order of the checks -/

-- 1. not a URI: no scheme, a bad scheme, a space, non-ASCII, a bad escape, a `]`
#guard parse s!"{cNia}/~/{bob}" == .error .invalid
#guard parse s!"1rgb:~/~/~/{bob}" == .error .invalid
#guard parse "rgb:~/~/~/bc:utxob:a b" == .error .invalid
#guard parse "rgb:~/~/~/é" == .error .invalid
#guard parse "rgb:~/~/~/x%2" == .error .invalid
#guard parse "rgb:~/~/~/x]" == .error .invalid
#guard parse (withQuery "endpoints=rpc://ho]t") == .error .invalid
-- 2. the scheme is `rgb`, in lower case
#guard parse s!"bad:2WBcas9-yjzEvGufY-9GEgnyMj7-beMNMWA8r-sPHtV1nPU-TMsGMQX/~/{bob}"
  == .error (.invalidScheme "bad")
#guard parse s!"RGB:~/~/~/{bob}" == .error (.invalidScheme "RGB")
-- 3. no authority, not even an empty one, and no absolute path
#guard parse s!"rgb://~/~/~/{bob}" == .error .authority
#guard parse "rgb://" == .error .authority
#guard parse s!"rgb:/~/~/~/{bob}" == .error .authority
-- 4. a path always has a first segment: an empty path is an invalid contract id
#guard parse "rgb:" == .error (.invalidContractId "")
-- 5. the contract id, or `~`; segments are not percent-decoded
#guard parse s!"rgb:invalid/{sTest}/{bob}" == .error (.invalidContractId "invalid")
#guard parse s!"rgb:%7E/~/~/{bob}" == .error (.invalidContractId "%7E")
-- 6. a schema segment
#guard parse "rgb:~" == .error .schemaMissing
-- 7. the schema id, or `~`
#guard parse s!"rgb:~/bad/~/{bob}" == .error (.invalidSchemaId "bad")
#guard parse "rgb:~/" == .error (.invalidSchemaId "")
-- 8. a state segment
#guard parse "rgb:~/~" == .error .assignmentStateMissing
-- 9. the state, or `~`
#guard parse s!"rgb:~/~/1@x/{bob}" == .error (.invalidAssignmentState "1@x")
-- 10. a beneficiary segment; an empty state segment is `void`
#guard parse "rgb:~/~/~" == .error .beneficiaryMissing
#guard parse "rgb:~/~/" == .error .beneficiaryMissing
-- 11. the beneficiary: a chain prefix, then a seal or a witness output and its key
#guard parse s!"rgb:~/~/BF/{ipk}" == .error (.beneficiary "missing beneficiary HRI")
#guard parse s!"rgb:~/~/BF/:+{ipk}" == .error (.beneficiary "invalid chain-network pair .")
#guard parse s!"rgb:~/~/BF/XX:utxob:{sealText}"
  == .error (.beneficiary "invalid chain-network pair xx.")
#guard parse s!"rgb:~/~/BF/bc:wvout:+{ipk}"
  == .error (.beneficiary "invalid length of identifier wvout:.")
#guard parse s!"rgb:~/~/BF/{bobW}+" == .error (.beneficiary "missing internal pk")
#guard parse s!"rgb:~/~/BF/{bobW}+750f58bcca0fdb11891e7979"
  == .error (.beneficiary "invalid internal pk")
-- an internal key must be a curve point: x = 5 is not one
#guard parse s!"rgb:~/~/BF/{bobW}+{"".pushn '0' 63}5" == .error (.beneficiary "invalid internal pk")
-- 12. each query piece has `=`: an empty query, `&&` and a trailing `&` are refused
#guard parse (withQuery "") == .error (.invalidQueryParam "")
#guard parse (withQuery "expiry") == .error (.invalidQueryParam "expiry")
#guard parse (withQuery "a=1&&b=2") == .error (.invalidQueryParam "")
#guard parse (withQuery "a=1&") == .error (.invalidQueryParam "")
-- 13. keys and values decode to UTF-8, the key first
#guard parse (withQuery "a=%FF")
  == .error (.invalidQueryParam "invalid utf-8 sequence of 1 bytes from index 0")
#guard parse (withQuery "a=%C3")
  == .error (.invalidQueryParam "incomplete utf-8 byte sequence from index 0")
#guard parse (withQuery "a=%E2%82x")
  == .error (.invalidQueryParam "invalid utf-8 sequence of 2 bytes from index 0")
#guard parse (withQuery "a=x%ED%A0%80")
  == .error (.invalidQueryParam "invalid utf-8 sequence of 1 bytes from index 1")
#guard parse (withQuery "%C3=%FF")
  == .error (.invalidQueryParam "incomplete utf-8 byte sequence from index 0")
-- 14. `endpoints`: each transport between `,`, empty ones included
#guard parse (withQuery "endpoints=") == .error (.invalidQueryParam "invalid transport .")
#guard parse (withQuery "endpoints=bad") == .error (.invalidQueryParam "invalid transport bad.")
#guard parse (withQuery "endpoints=rpca://host.example.com")
  == .error (.invalidQueryParam "invalid transport rpca://host.example.com.")
#guard parse (withQuery "endpoints=rpc://")
  == .error (.invalidQueryParam "invalid transport host .")
#guard parse (withQuery "endpoints=rpc/host.example.com")
  == .error (.invalidQueryParam "invalid transport rpc/host.example.com.")
#guard parse (withQuery "endpoints=rpc://a,") == .error (.invalidQueryParam "invalid transport .")
-- 15. `assignment_name`: a field name
#guard parse (withQuery "assignment_name=") == .error (.invalidAssignmentName "")
#guard parse (withQuery "assignment_name=AssetOwner")
  == .error (.invalidAssignmentName "AssetOwner")
#guard (parse (withQuery "assignment_name=_x9")).map (·.assignmentName) == .ok (some ⟨"_x9"⟩)
-- 16. `expiry`: an `i64`, with an optional sign
#guard parse (withQuery "expiry=six")
  == .error (.invalidExpiration "invalid digit found in string")
#guard parse (withQuery "expiry=")
  == .error (.invalidExpiration "cannot parse integer from empty string")
#guard parse (withQuery "expiry=9223372036854775808")
  == .error (.invalidExpiration "number too large to fit in target type")
#guard (parse (withQuery "expiry=-0042")).map (·.expiry) == .ok (some (-42))
-- 17. `pk`: 32 bytes of hex, either case
#guard parse (withQuery "pk=bad") == .error (.invalidPublicKey "bad")
#guard parse (withQuery "pk=d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f70751")
  == .error (.invalidPublicKey "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f70751")
-- 18. `enc`: exactly `0` or `1`
#guard parse (withQuery "enc=2") == .error (.invalidEncryption "2")
#guard parse (withQuery "enc=00") == .error (.invalidEncryption "00")
-- 19. accepted: the other parameters stay, in order
#guard (parse (withQuery "enc=1&x=1&expiry=5&y=2")).map (fun i => (i.encryption, i.expiry,
  i.unknownQuery)) == .ok (.optional, some 5, [("x", "1"), ("y", "2")])
-- the texts rgb-lib reports
#guard InvoiceParseError.authority.message
  == "RGB invoice must not contain any URI authority data, including empty one."
#guard (InvoiceParseError.invalidContractId "x").message == "invalid contract ID."
#guard (InvoiceParseError.beneficiary "missing internal pk").message
  == "can't recognize beneficiary \"missing internal pk\": it should be either a bitcoin " ++
    "address or a blinded UTXO seal."

/-! ## Which error wins -/

-- the URI before the scheme, the scheme before the authority
#guard parse "bad:a b" == .error .invalid
#guard parse "http://x" == .error (.invalidScheme "http")
-- the authority before the segments
#guard parse "rgb://x/bad/bad" == .error .authority
-- contract, schema, state and beneficiary, in path order
#guard parse "rgb:bad/bad/bad/bad" == .error (.invalidContractId "bad")
#guard parse "rgb:~/bad/bad/bad" == .error (.invalidSchemaId "bad")
#guard parse "rgb:~/~/bad/bad" == .error (.invalidAssignmentState "bad")
-- the beneficiary before the query
#guard parse "rgb:~/~/~/bad?expiry" == .error (.beneficiary "missing beneficiary HRI")
-- every query piece before any parameter
#guard parse (withQuery "endpoints=bad&x") == .error (.invalidQueryParam "x")
-- then the parameters in a fixed order, wherever they stand in the query
#guard parse (withQuery "assignment_name=1&endpoints=bad")
  == .error (.invalidQueryParam "invalid transport bad.")
#guard parse (withQuery "expiry=x&assignment_name=1") == .error (.invalidAssignmentName "1")
#guard parse (withQuery "pk=x&expiry=x")
  == .error (.invalidExpiration "invalid digit found in string")
#guard parse (withQuery "enc=2&pk=x") == .error (.invalidPublicKey "x")

/-! ## Transports -/

#guard RgbTransport.parse "" == .error (.invalidTransport "")
#guard RgbTransport.parse "bad" == .error (.invalidTransport "bad")
#guard RgbTransport.parse "rpca://host.example.com"
  == .error (.invalidTransport "rpca://host.example.com")
#guard RgbTransport.parse "rpc://" == .error (.invalidTransportHost "")
#guard RgbTransport.parse "rpc/host.example.com"
  == .error (.invalidTransport "rpc/host.example.com")
-- the host is checked before the scheme; schemes are case-sensitive
#guard RgbTransport.parse "nope://" == .error (.invalidTransportHost "")
#guard RgbTransport.parse "RPC://h" == .error (.invalidTransport "RPC://h")
-- split at the first `://`; the host is not checked
#guard RgbTransport.parse "ws://a://b" == .ok (.webSockets false "a://b")
#guard (RgbTransport.parse "storm://anything").map (·.display) == .ok "storm://_/"

/-! ## The builder -/

/-- Bob's concealed seal on mainnet. -/
def bobBeneficiary : XChainNet Beneficiary := ⟨.bitcoinMainnet, .blindedSeal bobSeal⟩

/-- A builder of `base`. -/
def built : RgbInvoiceBuilder :=
  RgbInvoiceBuilder.withContract cidOther bobBeneficiary |>.setSchema testSchema
    |>.setAmountRaw ⟨100⟩

-- the builder makes the invoice that the text reads as
#guard built.finish.display codec == base
#guard parse base == .ok built.finish

/-- The requested state after a builder call. -/
def stateAfter (r : Option (Except RgbInvoiceBuilder RgbInvoiceBuilder)) :
    Option (Except RgbInvoiceBuilder (Option InvoiceState)) :=
  r.map (·.map (·.invoice.assignmentState))

-- `set_amount`: whole units and decimals at a precision
#guard stateAfter (built.setAmount 10 5 .centiMicro) == some (.ok (some (.amount ⟨1000000005⟩)))
-- decimals of `10^precision` or more return the builder unchanged; an overflow panics
#guard built.setAmount 1 100 .centi == some (.error built)
#guard built.setAmount 18446744073709551615 0 .deci == none
-- `set_amount_approx` drops the fraction and refuses amounts that are not positive
#guard stateAfter (built.setAmountApprox 1.75 .centi) == some (.ok (some (.amount ⟨100⟩)))
#guard built.setAmountApprox 0.0 .centi == some (.error built)
#guard built.setAmountApprox (-1.0) .centi == some (.error built)
-- NaN gives 0; infinity gives the largest `u64`, which overflows at any precision but 0
#guard stateAfter (built.setAmountApprox (0.0 / 0.0) .centi) == some (.ok (some (.amount ⟨0⟩)))
#guard built.setAmountApprox (1.0 / 0.0) .centi == none
#guard stateAfter (built.setAmountApprox (1.0 / 0.0) .indivisible)
  == some (.ok (some (.amount ⟨18446744073709551615⟩)))
#guard (built.setAllocation 0 1).map (·.invoice.assignmentState)
  == .ok (some (.data (.fractionedToken ⟨⟨0⟩, ⟨1⟩⟩)))
-- transports: all or nothing; duplicates are kept
#guard built.addTransports ["rpc://a", "bad", "rpc://b"] == .error (built, .invalidTransport "bad")
#guard ((built.addTransport "rpc://a").bind (·.addTransport "rpc://a")).map (·.invoice.transports)
  == .ok [.jsonRpc false "a", .jsonRpc false "a"]

/-- An invoice with every query parameter, set in another order than the display's. -/
def full : RgbInvoice :=
  { (RgbInvoiceBuilder.new bobBeneficiary
      |>.setEncryption .optional
      |>.setPublicKey ((ofHex? pkHex).getD [])
      |>.addTransportRaw (.jsonRpc true "proxy.example.com")
      |>.setExpiryTimestamp 1682086371
      |>.setAssignmentName ⟨"assetOwner"⟩
      |>.setVoid).finish with unknownQuery := [("x", "1")] }

-- the display order of the parameters is fixed
#guard full.display codec ==
  s!"rgb:~/~//{bob}?assignment_name=assetOwner&expiry=1682086371&pk={pkHex}&enc=1" ++
    "&endpoints=rpcs://proxy.example.com&x=1"
#guard parse (full.display codec) == .ok full
/-- `full` with another parameter named `expiry`. -/
def fullExpiry7 : RgbInvoice := { full with unknownQuery := [("expiry", "7")] }
-- another parameter with a known key takes that key's place
#guard fullExpiry7.queryParams.map (·.1) == ["assignment_name", "expiry", "pk", "enc", "endpoints"]
#guard fullExpiry7.queryParams.lookup "expiry" == some "7"

/-! ## Witness output payloads -/

/-- Output key of rgb-invoicing's P2TR payload test. -/
def tapKey : Bytes :=
  (ofHex? "85a642598bfe2e42a378cbb53bf14abe77f81aefedf73b667b4285af7cf1c8a3").getD []

-- 33 bytes: the type, a 20-byte hash and zero bytes, which reading ignores
#guard (Pay2Vout.toPayload bobVout).length == 33
#guard Pay2Vout.ofPayload onCurve (Pay2Vout.toPayload bobVout) == .ok bobVout
#guard Pay2Vout.ofPayload onCurve ((Pay2Vout.toPayload bobVout).take 21 ++ List.replicate 12 7)
  == .ok bobVout
-- the type byte, and a taproot output key on the curve
#guard Pay2Vout.ofPayload onCurve (6 :: List.replicate 32 0) == .error (.invalidAddressType 6)
#guard (Pay2VoutError.invalidAddressType 6).message == "unexpected address type byte 0x06."
#guard Pay2Vout.ofPayload onCurve (5 :: List.replicate 32 0) == .error .invalidTapkey
#guard Pay2Vout.ofPayload onCurve (5 :: tapKey) == .ok ⟨.tr ⟨tapKey⟩⟩
-- address networks of the chains
#guard ChainNet.all.map (fun c => (XChainNet.mk c ()).addressNetwork)
  == [.mainnet, .testnets, .testnets, .testnets, .regtest, .mainnet, .testnets, .testnets]

/-! ## What rgb-lib reads from an invoice -/

/-- Bare ids of rgb-lib's schemas. -/
def sNia : String := "RWhwUfTMpuP2Zfx1~j4nswCANGeJrYOqDcKelaMV4zU"
def sUda : String := "~6rjymf3GTE840lb5JoXm2aFwE8eWCk3mCjOf_mUztE"
def sCfa : String := "JgqK5hJX9YBT4osCV7VcW_iLTcA5csUCnLzvaKTTrNY"
def sIfa : String := "A2n9kPNWtXUqwQJyXfY8yGHKyEPZgvrNYYYPGhXawOk"
def sBfa : String := "3I0xZVEQnQxYVk7vDnh5uNtQyUfsmThw6dX9n_Gvb5o"

-- the codec displays rgb-lib's schema ids
#guard AssetSchema.all.all fun a =>
  (schemas.find? fun e => "rgb:sch:" ++ e.1 ++ "#" ++ e.2.1 == a.schemaIdString).isSome

/-- The assignment rgb-lib reads from a schema, a state and an assignment name (empty: none). -/
def assignmentOf (schema state name : String) : Result Assignment :=
  let q := if name.isEmpty then "" else "?assignment_name=" ++ name
  (Invoice.new codec s!"rgb:~/{schema}/{state}/{bob}{q}").map (·.invoiceData.assignment)

/-- The refusal of an assignment the schema does not hold. -/
def refused : Result Assignment := .error (.invalidInvoice "invalid assignment")

-- no schema: the state and the name decide
#guard assignmentOf "~" "BF" "assetOwner" == .ok (.fungible 100)
#guard assignmentOf "~" "BF" "inflationAllowance" == .ok (.inflationRight 100)
#guard assignmentOf "~" "BF" "" == .ok .any
#guard assignmentOf "~" "BF" "linkRight" == .ok .any
#guard assignmentOf "~" "1@0" "" == .ok .nonFungible
#guard assignmentOf "~" "1@0" "assetOwner" == .ok .nonFungible
#guard assignmentOf "~" "~" "" == .ok .any
#guard assignmentOf "~" "~" "assetOwner" == .error (.invalidInvoice "unsupported assignment")
#guard assignmentOf "~" "" "" == .error (.invalidInvoice "unsupported assignment")
#guard assignmentOf "~" "1@0" "linkRight" == .error (.invalidInvoice "unsupported assignment")
-- NIA and CFA: an amount of the asset, 0 when the state is omitted
#guard assignmentOf sNia "BF" "" == .ok (.fungible 100)
#guard assignmentOf sNia "BF" "assetOwner" == .ok (.fungible 100)
#guard assignmentOf sNia "~" "" == .ok (.fungible 0)
#guard assignmentOf sCfa "~" "assetOwner" == .ok (.fungible 0)
#guard assignmentOf sNia "1@0" "" == refused
#guard assignmentOf sCfa "BF" "inflationAllowance" == refused
#guard assignmentOf sNia "" "" == refused
-- UDA: the token
#guard assignmentOf sUda "1@0" "" == .ok .nonFungible
#guard assignmentOf sUda "~" "assetOwner" == .ok .nonFungible
#guard assignmentOf sUda "BF" "" == refused
#guard assignmentOf sUda "" "" == refused
-- IFA: the asset, the inflation right or the link right; without a name, any assignment
#guard assignmentOf sIfa "BF" "assetOwner" == .ok (.fungible 100)
#guard assignmentOf sIfa "~" "assetOwner" == .ok (.fungible 0)
#guard assignmentOf sIfa "BF" "inflationAllowance" == .ok (.inflationRight 100)
#guard assignmentOf sIfa "~" "inflationAllowance" == .ok (.inflationRight 0)
#guard assignmentOf sIfa "" "linkRight" == .ok .linkRight
#guard assignmentOf sIfa "~" "linkRight" == .ok .linkRight
#guard assignmentOf sIfa "BF" "" == .ok .any
#guard assignmentOf sIfa "~" "" == .ok .any
#guard assignmentOf sIfa "BF" "linkRight" == refused
#guard assignmentOf sIfa "" "" == refused
#guard assignmentOf sIfa "~" "mintRight" == refused
-- BFA: the asset, the link right or the mint right; without a name, any assignment
#guard assignmentOf sBfa "BF" "assetOwner" == .ok (.fungible 100)
#guard assignmentOf sBfa "~" "assetOwner" == .ok (.fungible 0)
#guard assignmentOf sBfa "" "linkRight" == .ok .linkRight
#guard assignmentOf sBfa "~" "mintRight" == .ok .mintRight
#guard assignmentOf sBfa "" "mintRight" == .ok .mintRight
#guard assignmentOf sBfa "BF" "" == .ok .any
#guard assignmentOf sBfa "~" "" == .ok .any
#guard assignmentOf sBfa "BF" "inflationAllowance" == refused
#guard assignmentOf sBfa "BF" "mintRight" == refused

/-- An NIA invoice with every query parameter, on testnet4. -/
def fullText : String :=
  s!"rgb:{cOther}/{sNia}/BF/tb4:utxob:{sealText}?assignment_name=assetOwner&expiry=-1" ++
    s!"&pk={pkHex}&endpoints=rpc://proxy.example.com&x=y"

-- everything rgb-lib reads; a negative expiry wraps to a large `u64`
#guard (Invoice.new codec fullText).map (·.invoiceData) == .ok {
    recipientId := s!"tb4:utxob:{sealText}"
    assetSchema := some .nia
    assetId := some s!"rgb:{cOther}"
    assignment := .fungible 100
    assignmentName := some "assetOwner"
    network := .testnet4
    expirationTimestamp := some 18446744073709551615
    transportEndpoints := ["rpc://proxy.example.com"]
    publicKey := some pkHex
    encryption := .required
    unknownQueryParams := [("x", "y")] }
#guard (Invoice.new codec fullText).map (·.invoiceString) == .ok fullText
-- the parse error's text; a schema rgb-lib does not know; Liquid
#guard Invoice.new codec "rgb:~"
  == .error (.invalidInvoice "schema information is missing from the invoice.")
#guard Invoice.new codec base
  == .error (.unknownRgbSchema s!"rgb:sch:{sTest}#ladder-ecology-civil")
#guard Invoice.new codec s!"rgb:~/{sNia}/BF/lq:utxob:{sealText}"
  == .error (.unsupportedLayer1 "liquid")
-- the schema before the assignment, the assignment before the layer 1
#guard Invoice.new codec s!"rgb:~/{sTest}/1@0/lq:utxob:{sealText}"
  == .error (.unknownRgbSchema s!"rgb:sch:{sTest}#ladder-ecology-civil")
#guard Invoice.new codec s!"rgb:~/{sNia}/1@0/lq:utxob:{sealText}"
  == .error (.invalidInvoice "invalid assignment")

/-! ## Recipient ids and transport endpoints -/

#guard RecipientInfo.new codec bob == .ok ⟨bob, .blind, .mainnet⟩
#guard RecipientInfo.new codec s!"tb4:wvout:{voutText}+{ipk}"
  == .ok ⟨s!"tb4:wvout:{voutText}+{ipk}", .witness, .testnet4⟩
#guard (RecipientInfo.new codec s!"BCRT:utxob:{sealText}").map (·.network) == .ok .regtest
#guard (RecipientInfo.new codec s!"sbc:utxob:{sealText}").map (·.network) == .ok .signetCustom
#guard RecipientInfo.new codec s!"lq:utxob:{sealText}" == .error (.unsupportedLayer1 "liquid")
#guard RecipientInfo.new codec s!"xx:utxob:{sealText}" == .error .invalidRecipientId
#guard RecipientInfo.new codec "bc:nonsense" == .error .invalidRecipientId
#guard RecipientInfo.new codec sealText == .error .invalidRecipientId

-- a JSON-RPC proxy becomes an HTTP endpoint
#guard TransportEndpoint.new "rpc://proxy.example.com" == .ok ⟨"http://proxy.example.com", .jsonRpc⟩
#guard TransportEndpoint.new "rpcs://proxy.example.com:3000/json-rpc"
  == .ok ⟨"https://proxy.example.com:3000/json-rpc", .jsonRpc⟩
#guard TransportEndpoint.new "http://proxy.example.com" == .error .unsupportedTransportType
#guard TransportEndpoint.new "storm://_/" == .error .unsupportedTransportType
#guard TransportEndpoint.new "rpc://"
  == .error (.invalidTransportEndpoint "invalid transport host .")
#guard TransportEndpoint.new "proxy.example.com"
  == .error (.invalidTransportEndpoint "invalid transport proxy.example.com.")

end Rgb.Examples.InvoiceScenario
