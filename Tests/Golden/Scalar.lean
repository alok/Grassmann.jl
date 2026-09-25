import JuliaBase
import Lean.Data.Json

/-!
# Coefficient scalars of the element oracle

Decoding and re-encoding of the coefficient strings of `oracle/golden/**`
(docs/port-notes/oracle-schema.md §6):

| Julia `T` | JSON | Lean |
|---|---|---|
| `Int64` | `"-3"` | `Rat` (integral, range-checked) |
| `Bool` | `"true"` | `Rat` 0/1 |
| `Rational{Int64}` | `"-1//3"` (reduced, den > 0) | `Rat` |
| `Float64` | Julia `repr` (`"0.1"`, `"1.0e-5"`, `"-0.0"`, `"NaN"`) | `Float`, bit-exact |
| `Complex{T}` | `[re, im]` | a pair of the above |
| anything else | `string(c)` | kept as raw JSON (display-only, schema §6 "Other T") |

Float strings are parsed with the grammar of schema §6 into an exact decimal `m·10^e` and
rounded once with `Float.ofScientific` (correctly rounded in Lean core: an exact fast path
for `m < 2^53, e ≤ 22`, the exact `Float.Model` otherwise), so the recovered double is the
one Julia printed. Re-encoding uses `JuliaBase.F64.showString` (Ryu shortest, Julia's
`Base.Ryu.writeshortest`): since the shortest round-trip string of a double is unique,
`encode (decode s) = s` holds exactly when decoding is bit-exact.

Vectors of Float coefficients are stored in `FloatArray` (DESIGN.md §2.1).
-/

namespace Tests.ElementOracle

open Lean

/-! ## ASCII scanning -/

/-- Byte `i` of `s` (0 past the end). The coefficient grammar is ASCII. -/
@[inline] def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

/-- Whether byte `b` is an ASCII digit. -/
@[inline] def isDigitByte (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- Read the maximal run of ASCII digits of `s` starting at byte `i`, accumulating onto `acc`:
returns the value, the number of digits read and the next position. Tail-recursive. -/
def scanDigits (s : String) (i acc cnt : Nat) (fuel : Nat) : Nat × Nat × Nat :=
  match fuel with
  | 0 => (acc, cnt, i)
  | fuel + 1 =>
    let b := byteAt s i
    if isDigitByte b then scanDigits s (i + 1) (10 * acc + (b - 48).toNat) (cnt + 1) fuel
    else (acc, cnt, i)

/-- A decimal natural number that is exactly the substring `[i, j)` of `s` (at least one
digit, nothing else), or `none`. -/
def natSpan? (s : String) (i j : Nat) : Option Nat :=
  let (v, cnt, k) := scanDigits s i 0 0 (j - i)
  if cnt ≥ 1 && k == j then some v else none

/-! ## Unboxed float vectors -/

/-- `n` zeros as a `FloatArray`, pushed one by one (no intermediate `Array Float`,
DESIGN.md §2.1). -/
def floatZeros (n : Nat) : FloatArray := go n (FloatArray.emptyWithCapacity n)
where
  /-- Push `k` more zeros. -/
  go : Nat → FloatArray → FloatArray
    | 0, acc => acc
    | k + 1, acc => go k (acc.push 0)

/-- The `FloatArray` of `f i` for `i < n` (tail-recursive, unboxed). -/
@[inline] def floatOfFn (n : Nat) (f : Nat → Float) : FloatArray := go 0 (FloatArray.emptyWithCapacity n) n
where
  /-- Push `f i`, `f (i+1)`, … (`k` more). -/
  go (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | k + 1 => go (i + 1) (acc.push (f i)) k

/-! ## Scalar grammars (schema §6) -/

/-- Julia `Int64` literal: `-?[0-9]+` within `[-2^63, 2^63)`. -/
def parseInt64? (s : String) : Option Int :=
  let len := s.utf8ByteSize
  let neg := byteAt s 0 == 45
  let start := if neg then 1 else 0
  match natSpan? s start len with
  | none => none
  | some m =>
    let x : Int := if neg then -(m : Int) else m
    if -(2 ^ 63 : Int) ≤ x && x < (2 ^ 63 : Int) then some x else none

/-- Julia `Bool` literal. -/
def parseBool? (s : String) : Option Bool :=
  if s == "true" then some true else if s == "false" then some false else none

/-- Julia `Rational{Int64}` literal `num//den`: reduced, `den > 0`, sign on the numerator,
both parts within `Int64`. -/
def parseRational? (s : String) : Option Rat :=
  match s.splitOn "//" with
  | [p, q] => do
    let num ← parseInt64? p
    let den ← parseInt64? q
    if den ≤ 0 then none
    else
      let r : Rat := (num : Rat) / (den : Rat)
      if r.num == num && (r.den : Int) == den then some r else none
  | _ => none

/-- Julia `repr(::Float64)` (schema §6 grammar
`"-"? ("NaN" | "Inf" | digits "." digits ("e" "-"? digits)?)`), rounded once to the nearest
double (ties to even) through `Float.ofScientific`. `NaN` is the canonical quiet NaN (Julia
prints every NaN as `NaN`, so payloads are not recoverable); the sign of zero is kept. -/
def parseJuliaFloat? (s : String) : Option Float :=
  let len := s.utf8ByteSize
  let neg := byteAt s 0 == 45
  let i := if neg then 1 else 0
  let body := if neg then (s.drop 1).toString else s
  let sgn := fun (x : Float) => if neg then -x else x
  if body == "NaN" then (if neg then none else some (0.0 / 0.0))
  else if body == "Inf" then some (sgn (1.0 / 0.0))
  else
    let (ip, ic, j) := scanDigits s i 0 0 len
    if ic == 0 || byteAt s j != 46 then none else
    let (m, fc, k) := scanDigits s (j + 1) ip 0 len
    if fc == 0 then none else
    -- optional exponent
    let (e10, ok) : Int × Bool :=
      if k == len then (0, true)
      else if byteAt s k != 101 then (0, false)
      else
        let eneg := byteAt s (k + 1) == 45
        let es := if eneg then k + 2 else k + 1
        match natSpan? s es len with
        | some e => (if eneg then -(e : Int) else e, true)
        | none => (0, false)
    if !ok then none else
    let ex : Int := e10 - fc
    let x : Float :=
      if ex ≥ 0 then Float.ofScientific m false ex.toNat else Float.ofScientific m true ex.natAbs
    some (sgn x)

/-! ## Coefficient types -/

/-- A Julia coefficient type (the element's `T`, Julia's `valuetype`; schema §6). -/
inductive CoeffType where
  /-- `Int64`. -/
  | int64
  /-- `Bool`. -/
  | bool
  /-- `Rational{Int64}`. -/
  | rational
  /-- `Float64`. -/
  | float64
  /-- `Complex{T}` for one of the four real types. -/
  | complex (re : CoeffType)
  /-- Any other type (`Any`, `Irrational{:π}`, nested `Chain{…}`): display-only. -/
  | other (name : String)
  deriving BEq, Repr, Inhabited, Hashable

namespace CoeffType

/-- The real (non-complex) coefficient type named `s`. -/
def realOfName? (s : String) : Option CoeffType :=
  match s with
  | "Int64" => some .int64
  | "Bool" => some .bool
  | "Rational{Int64}" => some .rational
  | "Float64" => some .float64
  | _ => none

/-- Decode a Julia type name. -/
def ofName (s : String) : CoeffType :=
  match realOfName? s with
  | some t => t
  | none =>
    if s.startsWith "Complex{" && s.endsWith "}" then
      match realOfName? ((s.drop 8).dropEnd 1).toString with
      | some t => .complex t
      | none => .other s
    else .other s

/-- Julia's spelling of the type. -/
def name : CoeffType → String
  | .int64 => "Int64"
  | .bool => "Bool"
  | .rational => "Rational{Int64}"
  | .float64 => "Float64"
  | .complex t => "Complex{" ++ t.name ++ "}"
  | .other s => s

/-- Coefficients of this type can be decoded (schema §6 table). -/
def parseable : CoeffType → Bool
  | .other _ => false
  | _ => true

/-- `Float64` or `Complex{Float64}`. -/
def isFloat : CoeffType → Bool
  | .float64 | .complex .float64 => true
  | _ => false

/-- The real part type (itself for a real type). -/
def realPart : CoeffType → CoeffType
  | .complex t => t
  | t => t

/-- Rank in Julia's promotion order `Bool < Int64 < Rational{Int64} < Float64`. -/
private def rank : CoeffType → Nat
  | .bool => 0
  | .int64 => 1
  | .rational => 2
  | .float64 => 3
  | _ => 4

/-- Julia `promote_type` on the parseable coefficient types (`Bool` + `Int64` = `Int64`,
anything + `Float64` = `Float64`, complex if either is). `none` for other types. -/
def promote (a b : CoeffType) : Option CoeffType :=
  if !a.parseable || !b.parseable then none else
  let ra := a.realPart
  let rb := b.realPart
  let r := if rank ra ≥ rank rb then ra else rb
  match a, b with
  | .complex _, _ | _, .complex _ => some (.complex r)
  | _, _ => some r

end CoeffType

/-! ## Scalars and coefficient vectors -/

/-- One decoded coefficient. -/
inductive Scalar where
  /-- An `Int64`, `Bool` (0/1) or `Rational{Int64}` value. -/
  | exact (x : Rat)
  /-- A `Float64`, bit-exact. -/
  | float (x : Float)
  /-- A complex value (both parts of the same real kind). -/
  | complex (re im : Scalar)
  /-- An undecodable (display-only) coefficient, as given. -/
  | raw (j : Json)
  deriving Inhabited

/-- Decode one real coefficient string of real type `t`. -/
def decodeReal? (t : CoeffType) (s : String) : Option Scalar :=
  match t with
  | .int64 => (parseInt64? s).map fun x => .exact x
  | .bool => (parseBool? s).map fun b => .exact (if b then 1 else 0)
  | .rational => (parseRational? s).map .exact
  | .float64 => (parseJuliaFloat? s).map .float
  | _ => none

/-- Decode one coefficient of type `t` (schema §6). -/
def decodeScalar (t : CoeffType) (j : Json) : Except String Scalar :=
  match t, j with
  | .other _, _ => .ok (.raw j)
  | .complex r, .arr #[.str a, .str b] =>
    match decodeReal? r a, decodeReal? r b with
    | some x, some y => .ok (.complex x y)
    | _, _ => .error s!"bad {t.name} coefficient {j.compress}"
  | _, .str s =>
    match decodeReal? t s with
    | some x => .ok x
    | none => .error s!"bad {t.name} coefficient {s.quote}"
  | _, _ => .error s!"bad {t.name} coefficient {j.compress}"

/-- The Julia string of an exact integer or rational of real type `t`. -/
def encodeExact (t : CoeffType) (x : Rat) : String :=
  match t with
  | .bool => if x == 0 then "false" else "true"
  | .rational => toString x.num ++ "//" ++ toString x.den
  | _ => toString x.num

/-- Julia `repr(::Float64)` (Ryu shortest, `JuliaBase.F64.showString`). -/
@[inline] def encodeFloat (x : Float) : String := JuliaBase.F64.showString x

/-- Encode a coefficient of type `t` back to its JSON form. -/
def encodeScalar (t : CoeffType) : Scalar → Json
  | .exact x => .str (encodeExact t.realPart x)
  | .float x => .str (encodeFloat x)
  | .complex re im => .arr #[encodeScalar t.realPart re, encodeScalar t.realPart im]
  | .raw j => j

/-- A decoded coefficient vector (`dense`, `native`, `ref`, a Number's `value` as a
vector of length 1). Float data is unboxed (`FloatArray`). -/
inductive Coeffs where
  /-- `Int64`/`Bool`/`Rational{Int64}` coefficients. -/
  | exact (v : Array Rat)
  /-- `Float64` coefficients, bit-exact. -/
  | float (v : FloatArray)
  /-- `Complex` of an exact type: real and imaginary parts. -/
  | complexExact (re im : Array Rat)
  /-- `Complex{Float64}`: real and imaginary parts. -/
  | complexFloat (re im : FloatArray)
  /-- Undecodable coefficients (display-only types), as given. -/
  | raw (v : Array Json)
  deriving Inhabited

namespace Coeffs

/-- Number of coefficients. -/
def size : Coeffs → Nat
  | .exact v => v.size
  | .float v => v.size
  | .complexExact re _ => re.size
  | .complexFloat re _ => re.size
  | .raw v => v.size

/-- Coefficient `i` as a `Scalar` (0 past the end). -/
def get (c : Coeffs) (i : Nat) : Scalar :=
  match c with
  | .exact v => .exact (v[i]?.getD 0)
  | .float v => .float (v[i]?.getD 0)
  | .complexExact re im => .complex (.exact (re[i]?.getD 0)) (.exact (im[i]?.getD 0))
  | .complexFloat re im => .complex (.float (re[i]?.getD 0)) (.float (im[i]?.getD 0))
  | .raw v => .raw (v[i]?.getD .null)

/-- Julia `iszero` of coefficient `i` (a NaN is not zero; raw coefficients never are). -/
def isZeroAt (c : Coeffs) (i : Nat) : Bool :=
  match c with
  | .exact v => v[i]?.getD 0 == 0
  | .float v => v[i]?.getD 0 == 0
  | .complexExact re im => re[i]?.getD 0 == 0 && im[i]?.getD 0 == 0
  | .complexFloat re im => re[i]?.getD 0 == 0 && im[i]?.getD 0 == 0
  | .raw _ => false

/-- The coefficients at the given positions, in order. -/
def gather (c : Coeffs) (idx : Array Nat) : Coeffs :=
  let fa := fun (v : FloatArray) => idx.foldl (fun acc i => acc.push (v[i]?.getD 0)) FloatArray.empty
  match c with
  | .exact v => .exact (idx.map fun i => v[i]?.getD 0)
  | .float v => .float (fa v)
  | .complexExact re im => .complexExact (idx.map fun i => re[i]?.getD 0) (idx.map fun i => im[i]?.getD 0)
  | .complexFloat re im => .complexFloat (fa re) (fa im)
  | .raw v => .raw (idx.map fun i => v[i]?.getD .null)

/-- The zero vector of length `n` in the representation of type `t`. -/
def zeros (t : CoeffType) (n : Nat) : Coeffs :=
  match t with
  | .float64 => .float (floatZeros n)
  | .complex .float64 => .complexFloat (floatZeros n) (floatZeros n)
  | .complex _ => .complexExact (Array.replicate n 0) (Array.replicate n 0)
  | .other _ => .raw (Array.replicate n (.str "0"))
  | _ => .exact (Array.replicate n 0)

/-- Overwrite coefficient `i` with `x` (ignored if the representations differ). -/
def set (c : Coeffs) (i : Nat) (x : Scalar) : Coeffs :=
  match c, x with
  | .exact v, .exact y => .exact (v.setIfInBounds i y)
  | .float v, .float y => .float (if i < v.size then v.set! i y else v)
  | .complexExact re im, .complex (.exact a) (.exact b) =>
    .complexExact (re.setIfInBounds i a) (im.setIfInBounds i b)
  | .complexFloat re im, .complex (.float a) (.float b) =>
    .complexFloat (if i < re.size then re.set! i a else re) (if i < im.size then im.set! i b else im)
  | .raw v, .raw y => .raw (v.setIfInBounds i y)
  | c, _ => c

/-- Decode a JSON array of coefficients of type `t`. Real types are decoded with a
tail-recursive loop straight into `Array Rat`/`FloatArray`. -/
def decode (t : CoeffType) (js : Array Json) : Except String Coeffs := do
  match t with
  | .other _ => return .raw js
  | .float64 =>
    let mut out := FloatArray.emptyWithCapacity js.size
    for j in js do
      match j with
      | .str s => match parseJuliaFloat? s with
        | some x => out := out.push x
        | none => throw s!"bad Float64 coefficient {s.quote}"
      | _ => throw s!"bad Float64 coefficient {j.compress}"
    return .float out
  | .complex r =>
    let mut re : Array Scalar := #[]
    let mut im : Array Scalar := #[]
    for j in js do
      match ← decodeScalar t j with
      | .complex a b => re := re.push a; im := im.push b
      | _ => throw s!"bad {t.name} coefficient {j.compress}"
    if r == .float64 then
      let f := fun (xs : Array Scalar) => xs.foldl (fun acc x => match x with
        | .float y => acc.push y | _ => acc) FloatArray.empty
      return .complexFloat (f re) (f im)
    else
      let f := fun (xs : Array Scalar) => xs.map fun x => match x with | .exact y => y | _ => 0
      return .complexExact (f re) (f im)
  | _ =>
    let mut out : Array Rat := Array.mkEmpty js.size
    for j in js do
      match j with
      | .str s => match decodeReal? t s with
        | some (.exact x) => out := out.push x
        | _ => throw s!"bad {t.name} coefficient {s.quote}"
      | _ => throw s!"bad {t.name} coefficient {j.compress}"
    return .exact out

/-- Encode back to the JSON array form (schema §6). -/
def encode (t : CoeffType) : Coeffs → Array Json
  | .exact v => v.map fun x => .str (encodeExact t.realPart x)
  | .float v => v.foldl (fun acc x => acc.push (.str (encodeFloat x))) #[]
  | .complexExact re im =>
    (re.zip im).map fun (a, b) =>
      .arr #[.str (encodeExact t.realPart a), .str (encodeExact t.realPart b)]
  | .complexFloat re im =>
    (List.range re.size).toArray.map fun i =>
      .arr #[.str (encodeFloat (re[i]?.getD 0)), .str (encodeFloat (im[i]?.getD 0))]
  | .raw v => v

/-- Build a vector from scalars (all of one representation, as decoding produces). -/
def ofScalars (t : CoeffType) (xs : Array Scalar) : Coeffs :=
  xs.zipIdx.foldl (fun acc (x, i) => acc.set i x) (zeros t xs.size)

end Coeffs

/-! ## Value comparison (schema §11 rule 3) -/

/-- Julia `isequal` on doubles: bitwise, every NaN equal, the sign of zero kept. -/
@[inline] def floatSame (x y : Float) : Bool :=
  (x.isNaN && y.isNaN) || x.toBits == y.toBits

/-- The exact rational value of a finite double. -/
def floatToRat (x : Float) : Option Rat :=
  if !x.isFinite then none else
  let (m, e) := x.frExp
  -- x = m · 2^e with 0.5 ≤ |m| < 1: scale the mantissa to an integer exactly
  let mi : Int := (m.scaleB 53).toInt64.toInt
  let e' : Int := e - 53
  some (if e' ≥ 0 then (mi * 2 ^ e'.toNat : Int) else (mi : Rat) / ((2 ^ e'.natAbs : Nat) : Rat))

/-- How two coefficient vectors are compared. -/
inductive ValueMode where
  /-- Exact for exact types, bitwise for floats (NaN = NaN, signed zeros distinct). -/
  | exact
  /-- Componentwise `|x - y| ≤ atol + rtol·max(|x|, |y|)` for floats, exact otherwise
  (the documented 1e-12 kernel tolerance). -/
  | componentwise (rtol atol : Float)
  /-- `‖x − y‖₂ ≤ atol + rtol·max(‖x‖₂, ‖y‖₂)` (composite suite, schema §8.5). -/
  | norm2 (rtol atol : Float)
  deriving Inhabited, Repr

/-- A `Rat` as a double (exact for the dyadic and small values that occur). -/
@[inline] def ratAsFloat (x : Rat) : Float := Float.ofInt x.num / Float.ofNat x.den

/-- The coefficients as doubles (real part and imaginary part; exact values rounded). -/
def Coeffs.toFloats : Coeffs → FloatArray × FloatArray
  | .exact v => (floatOfFn v.size fun i => ratAsFloat v[i]!, floatZeros v.size)
  | .float v => (v, floatZeros v.size)
  | .complexExact re im => (floatOfFn re.size fun i => ratAsFloat re[i]!, floatOfFn im.size fun i => ratAsFloat im[i]!)
  | .complexFloat re im => (re, im)
  | .raw v => (floatZeros v.size, floatZeros v.size)

/-- Sum of squares of `a[i] - b[i]` (or of `a[i]` when `b` is empty), tail-recursive. -/
def sqDist (a b : FloatArray) (i : Nat) (acc : Float) : Nat → Float
  | 0 => acc
  | fuel + 1 =>
    if i < a.size then
      let d := a[i]!- (if b.size == 0 then 0 else b[i]!)
      sqDist a b (i + 1) (acc + d * d) fuel
    else acc

/-- Exact equality of two scalars (floats bitwise with NaN = NaN). Mixed exact/float
compares the double's exact value. -/
def scalarSame : Scalar → Scalar → Bool
  | .exact x, .exact y => x == y
  | .float x, .float y => floatSame x y
  | .exact x, .float y | .float y, .exact x => floatToRat y == some x
  | .complex a b, .complex c d => scalarSame a c && scalarSame b d
  | .raw a, .raw b => a == b
  | _, _ => false

/-- Human-readable form of a scalar for failure messages (`3`, `-1//3`, `0.5`, `(1, 2)`). -/
def Scalar.show : Scalar → String
  | .exact x => if x.den == 1 then toString x.num else s!"{x.num}//{x.den}"
  | .float x => encodeFloat x
  | .complex a b => s!"({a.show}, {b.show})"
  | .raw j => j.compress

/-- Float agreement under a comparison mode (componentwise tolerance or bitwise). -/
def floatAgree (mode : ValueMode) (x y : Float) : Bool :=
  match mode with
  | .componentwise rtol atol =>
    let ax := x.abs
    let ay := y.abs
    (x.isNaN && y.isNaN) || x == y || (x - y).abs ≤ atol + rtol * (if ax ≥ ay then ax else ay)
  | _ => floatSame x y

/-- Scalar agreement under a comparison mode (exact types always exactly). -/
def scalarAgree (mode : ValueMode) : Scalar → Scalar → Bool
  | .float x, .float y => floatAgree mode x y
  | .complex a b, .complex c d => scalarAgree mode a c && scalarAgree mode b d
  | x, y => scalarSame x y

/-- First index `≥ i` where the vectors disagree componentwise. -/
def firstDisagreement (mode : ValueMode) (got want : Coeffs) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if i ≥ got.size then none
    else if scalarAgree mode (got.get i) (want.get i) then firstDisagreement mode got want (i + 1) fuel
    else some i

/-- Compare two coefficient vectors; `none` when they agree, else a reason. -/
def compareCoeffs (mode : ValueMode) (got want : Coeffs) : Option String :=
  if got.size != want.size then some s!"length {got.size} vs {want.size}" else
  match mode with
  | .norm2 rtol atol =>
    let (gr, gi) := got.toFloats
    let (wr, wi) := want.toFloats
    let d := Float.sqrt (sqDist gr wr 0 0 gr.size + sqDist gi wi 0 0 gi.size)
    let ng := Float.sqrt (sqDist gr FloatArray.empty 0 0 gr.size + sqDist gi FloatArray.empty 0 0 gi.size)
    let nw := Float.sqrt (sqDist wr FloatArray.empty 0 0 wr.size + sqDist wi FloatArray.empty 0 0 wi.size)
    let bothNaN := d.isNaN && ng.isNaN && nw.isNaN
    if bothNaN || d ≤ atol + rtol * (if ng ≥ nw then ng else nw) then none
    else some s!"‖Δ‖₂ = {d} > {atol} + {rtol}·max({ng}, {nw})"
  | _ =>
    (firstDisagreement mode got want 0 got.size).map fun i =>
      s!"coefficient {i}: {(got.get i).show} vs {(want.get i).show}"

/-! ## Self-checks of the grammars -/

#guard parseInt64? "-9223372036854775808" == some (-9223372036854775808)
#guard parseInt64? "9223372036854775808" == none
#guard parseInt64? "1.0" == none
#guard parseRational? "-1//3" == some (-1/3)
#guard parseRational? "2//4" == none      -- not reduced
#guard parseRational? "1//-3" == none     -- sign on the numerator
#guard (parseJuliaFloat? "0.1").map (·.toBits) == some 0x3FB999999999999A
#guard (parseJuliaFloat? "-0.0").map (·.toBits) == some 0x8000000000000000
#guard (parseJuliaFloat? "5.0e-324").map (·.toBits) == some 1
#guard (parseJuliaFloat? "1.7976931348623157e308").map (·.toBits) == some 0x7FEFFFFFFFFFFFFF
#guard (parseJuliaFloat? "2.2250738585072014e-308").map (·.toBits) == some 0x0010000000000000
#guard (parseJuliaFloat? "-Inf").map (·.toBits) == some 0xFFF0000000000000
#guard (parseJuliaFloat? "NaN").map (·.isNaN) == some true
#guard parseJuliaFloat? "1e5" == none      -- Julia always prints the `.`
#guard parseJuliaFloat? "1.0e+5" == none   -- and never a `+` exponent
#guard parseJuliaFloat? ".5" == none
#guard (parseJuliaFloat? "0.30000000000000004").map encodeFloat == some "0.30000000000000004"
#guard CoeffType.ofName "Complex{Float64}" == .complex .float64
#guard CoeffType.ofName "Irrational{:π}" == .other "Irrational{:π}"
#guard CoeffType.promote .int64 .rational == some .rational
#guard CoeffType.promote .bool (.complex .float64) == some (.complex .float64)
#guard floatToRat 0.75 == some (3/4)
#guard floatToRat (-2.5e-3) == some (-5764607523034235/2305843009213693952)

end Tests.ElementOracle
