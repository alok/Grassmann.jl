import Tests.JuliaBase.Util
import Tests.Util.Random

/-!
Julia's own numerics against the oracle (`Tests/JuliaBase/math.json`, written by
`gen_golden.jl math`), all bit for bit, and property checks of the exact IEEE toolkit:

* `eps64`/`eps32`, `exponent64`/`exponent32`, `rat64`/`rat32`: `F64.epsOf`, `F32.epsOf`,
  `IEEEFloat.exponent`, and the correctly rounded `IEEEFloat.ofFraction`/`ofRat` of big
  rationals.
-/

open JuliaBase

namespace Tests.JuliaBase.Math

/-- A `Float32` from hex (`0` if malformed). -/
def f32 (s : String) : Float32 := (float32OfHex s).getD 0

/-- A `Float` from hex (`0` if malformed). -/
def f64 (s : String) : Float := (floatOfHex s).getD 0

/-- Bitwise `Float32` equality with all NaNs equal. -/
def sameF32 (x y : Float32) : Bool := (x.isNaN && y.isNaN) || x.toBits == y.toBits

/-- An integer field. -/
def int (s : String) : Int := s.toInt?.getD 0

/-- Check one `math.json` row (rows of kinds this module does not know are skipped). -/
def checkRow (t : Tally) : List String → Tally
  | ["eps64", hx, hr] =>
    let got := F64.epsOf (f64 hx)
    t.check (sameFloat got (f64 hr)) fun _ => s!"eps({F64.showString (f64 hx)}): got {F64.showString got}"
  | ["eps32", hx, hr] =>
    let got := F32.epsOf (f32 hx)
    t.check (sameF32 got (f32 hr)) fun _ => s!"eps({F32.showString (f32 hx)}): got {F32.showString got}"
  | ["exponent64", hx, e] =>
    let x := f64 hx
    t.check (IEEEFloat.exponent x == int e && F64.exponent x == int e) fun _ =>
      s!"exponent({F64.showString x}): got {IEEEFloat.exponent x}, want {e}"
  | ["exponent32", hx, e] =>
    let x := f32 hx
    t.check (IEEEFloat.exponent x == int e) fun _ =>
      s!"exponent({F32.showString x}): got {IEEEFloat.exponent x}, want {e}"
  | ["rat64", p, q, hr] =>
    let got := IEEEFloat.ofFraction Float (int p) (int q).toNat
    let viaRat := IEEEFloat.ofRat Float ((int p : Rat) / (int q : Rat))
    t.check (sameFloat got (f64 hr) && sameFloat viaRat (f64 hr)) fun _ =>
      s!"Float64({p}/{q}): got {F64.showString got}, want {F64.showString (f64 hr)}"
  | ["rat32", p, q, hr] =>
    let got := IEEEFloat.ofFraction Float32 (int p) (int q).toNat
    t.check (sameF32 got (f32 hr)) fun _ =>
      s!"Float32({p}/{q}): got {F32.showString got}, want {F32.showString (f32 hr)}"
  | _ => t

/-- A random finite `Float` from random bits. -/
def randFinite (g : Tests.Rng) : Float × Tests.Rng :=
  let (u, g) := g.next
  let x := Float.ofBits u
  (if x.isFinite then x else Float.ofBits (u &&& 0x3FFFFFFFFFFFFFFF), g)

/-- Property checks of the exact IEEE toolkit against the bit-level `F64`/`F32` functions. -/
def props : Tally := Id.run do
  let mut t : Tally := {}
  let mut g := Tests.Rng.ofSeed 0x1EEE754
  for _ in [0:5000] do
    let (x, g') := randFinite g
    g := g'
    t := t.check ((IEEEFloat.toRat? x).map (fun q => sameFloat (IEEEFloat.ofRat Float q) x || (x == 0 && q == 0))
      |>.getD false) fun _ => s!"ofRat ∘ toRat at {F64.showString x}"
    t := t.check (sameFloat (IEEEFloat.nextFloat x) (F64.nextfloat x) &&
      sameFloat (IEEEFloat.prevFloat x) (F64.prevfloat x) && IEEEFloat.signBit x == F64.signbit x) fun _ =>
      s!"nextFloat/prevFloat/signBit at {F64.showString x}"
    let (u, g') := g.next
    g := g'
    let y := Float32.ofBits u.toUInt32
    t := t.check (IEEEFloat.toRat? y |>.map (fun q => sameF32 (IEEEFloat.ofRat Float32 q) y || (y == 0 && q == 0))
      |>.getD (!IEEEFloat.isFinite y)) fun _ => s!"Float32 ofRat ∘ toRat at {F32.showString y}"
    t := t.check (sameF32 (IEEEFloat.nextFloat y) (F32.nextfloat y) &&
      sameF32 (IEEEFloat.prevFloat y) (F32.prevfloat y)) fun _ => s!"Float32 neighbours at {F32.showString y}"
    let (a, g1) := g.int (-1000000) 1000000
    let (b, g2) := g1.nat 1000000
    g := g2
    t := t.check (sameFloat (IEEEFloat.ofFraction Float a (b + 1)) (Float.ofInt a / Float.ofNat (b + 1)))
      fun _ => s!"ofFraction {a}/{b + 1}"
  -- the generic constants agree with the bit-level ones, and with Julia's printed values
  t := t.check ([IEEEFloat.eps Float, IEEEFloat.floatmax Float, IEEEFloat.floatmin Float,
      IEEEFloat.maxintfloat Float, IEEEFloat.inf Float, IEEEFloat.nan Float].zip [F64.eps, F64.floatmax,
      F64.floatmin, F64.maxintfloat, F64.inf, F64.nan] |>.all fun (a, b) => sameFloat a b)
    fun _ => "generic Float64 constants"
  t := t.check ([IEEEFloat.eps Float32, IEEEFloat.floatmax Float32, IEEEFloat.floatmin Float32,
      IEEEFloat.maxintfloat Float32, IEEEFloat.inf Float32, IEEEFloat.nan Float32].zip [F32.eps, F32.floatmax,
      F32.floatmin, F32.maxintfloat, F32.inf, F32.nan] |>.all fun (a, b) => sameF32 a b)
    fun _ => "generic Float32 constants"
  t := t.check (([F32.eps, F32.floatmax, F32.floatmin, F32.maxintfloat, F32.prevfloat F32.inf].map
      F32.showString) == ["1.1920929f-7", "3.4028235f38", "1.1754944f-38", "1.6777216f7", "3.4028235f38"])
    fun _ => "Julia's Float32 constants"
  return t

/-- The committed golden `math.json`, plus the property checks. -/
def golden : IO (Nat × Nat) := do
  let j ← loadGolden "math.json"
  let mut t : Tally := props
  for row in jArr j "cases" do t := checkRow t (jRow row)
  t.report "math golden"

/-- The TSV fuzz file `PREFIX_math.tsv`. -/
def fuzz (path : System.FilePath) : IO (Nat × Nat) := do
  let mut t : Tally := {}
  for row in ← readTsv path do t := checkRow t row
  t.report "math fuzz"

end Tests.JuliaBase.Math
