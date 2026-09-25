import Cartan
import FlowGeometry.Eval

/-!
# Sample axes, range slicing, and the 1-D gradient

* `interval p c x0` is Julia's `range(x0, c, length = p)` (`profiles.jl:42`: `c` is the **end
  point**), a `TwicePrecision` range whose elements `Cartan.Axis` computes bit for bit;
  `doubleinterval` (`profiles.jl:43`) is the base of the closed outline.
* `sliceRange` is Julia's `getindex(r::StepRangeLen, a:b)` (`base/twiceprecision.jl:495-530`),
  which re-anchors the reference point: `RakichPlate` reads `x[2:end-1]` of an interval, and its
  elements differ in the last bit from the parent's.
* `gradient1` is Cartan's `gradient` of a real field over an open 1-D grid
  (`Cartan.jl src/grid.jl:596, 641-718, 788-800`): the fourth-order stencil of the fibers divided
  by the same stencil of the points. `UpperArc`/`LowerArc` define their slope this way
  (`airfoils.jl:40`). (The Cartan port's grid calculus is its next stage; this is the one case
  FlowGeometry needs.)

These helpers belong to `JuliaBase`/`Cartan` by DESIGN.md §2.9; they live here until those
libraries take them over.
-/

namespace FlowGeometry

open JuliaBase Cartan

/-- `range(0, 1, length = n)` for `n ≥ 2`, built directly: Julia's `_linspace(Float64, 0, 1, n, 1)`
(`twiceprecision.jl:716`) has the reference `0` at offset `1` and the step
`twiceprecision(TwicePrecision(1)/Float64(n-1), nbitslen(n, 1))`. The general `Axis.range` reaches
the same fields through `rat` and several `Int` conversions (about 1 µs);
`Tests/FlowGeometry/Meshes.lean` checks the two agree for `n = 2 … 3000`. -/
def unitRange (n : Nat) : StepRangeLen :=
  let d := (n - 1).toUInt64.toFloat
  ⟨⟨0, 0⟩, TwicePrecision.twiceprecision (TwicePrecision.div ⟨1, 0⟩ ⟨d, 0⟩) (StepRangeLen.nbitslen n 1), n, 1⟩

/-- Julia `interval(p::Int, c = 1, x0 = 0) = range(x0, c, length = p)` (`profiles.jl:42`). -/
def interval (p : Nat) (c : Float := 1) (x0 : Float := 0) : Axis :=
  if c == 1 && x0.toBits == 0 && p ≥ 2 then .stepLen (unitRange p) else Axis.range x0 c p

/-- Julia `chord(p) = range(0, 0, length = p)` (`airfoils.jl:44`): `p` zeros. -/
def chord (p : Nat) : Axis := Axis.range 0 0 p

/-- Julia `doubleinterval(r) = r[1]:step(r):r[1]+2(r[end]-r[1])` (`profiles.jl:43`): the range
continued to twice its width (`2n-1` points), the base of a closed outline. Julia has no `step`
for an explicit vector (the interval of an `UpperArc`-based airfoil); the port reflects the
points about the last one. -/
def doubleinterval (a : Axis) : Axis :=
  match a with
  | .stepLen r =>
    -- the unit interval `range(0, 1, length = n)`: `0:1/(n-1):2` is `floatrange(0, 1, 2n-1, n-1)`
    -- (`twiceprecision.jl:376`), built directly (checked against `Axis.colon` in the tests)
    let n := r.len
    let d := (n - 1).toUInt64.toFloat
    if n ≥ 2 && r.first.toBits == 0 && r.last == 1 && (1 : Float) / d == r.stepValue then
      .stepLen ⟨⟨0, 0⟩, TwicePrecision.twiceprecision (TwicePrecision.div ⟨1, 0⟩ ⟨d, 0⟩)
        (StepRangeLen.nbitslen (2 * n - 1) 1), 2 * n - 1, 1⟩
    else doubleintervalGeneric a
  | _ => doubleintervalGeneric a
where
  /-- the general case -/
  doubleintervalGeneric (a : Axis) : Axis :=
  match a.step? with
  | some s => Axis.colon a.first s (a.first + 2 * (a.last - a.first))
  | none =>
    let n := a.length
    let l := a.last
    .explicit (floatsOfFn (2 * n - 1) fun i => if i < n then a.get i else 2 * l - a.get (2 * n - 2 - i))

/-- Julia `*(x::TwicePrecision{Float64}, v::Integer)` (`twiceprecision.jl:310-315`): truncate
`hi` to `top_set_bit(|v|-1)` bits so that `u·v` is exact. -/
def twiceMulInt (x : TwicePrecision) (v : Int) : TwicePrecision :=
  if v == 0 then ⟨x.hi * Float.ofInt v, x.lo * Float.ofInt v⟩
  else
    let nb := Nat.log2 (v.natAbs - 1) + (if v.natAbs - 1 == 0 then 0 else 1)
    let u := TwicePrecision.truncbits x.hi nb
    TwicePrecision.canonicalize2 (u * Float.ofInt v) (((x.hi - u) + x.lo) * Float.ofInt v)

/-- Julia `r[a:b]` (1-based, unit step) of a `TwicePrecision` range
(`twiceprecision.jl:495-530`): the sub-range, re-anchored at its own reference element. -/
def sliceRange (r : StepRangeLen) (a b : Nat) : StepRangeLen :=
  let len := b + 1 - a
  let soffset : Int := F64.roundInt (Float.ofInt (r.offset - a) / 1 + 1)
  let soffset : Int := if soffset < 1 then 1 else if soffset > len then len else soffset
  let ioffset : Int := a + (soffset - 1)
  let soffset := max 1 soffset
  if ioffset == r.offset then ⟨r.ref, r.step, len, soffset⟩
  else ⟨TwicePrecision.add r.ref (twiceMulInt r.step (ioffset - r.offset)), r.step, len, soffset⟩

/-- Julia `a[i:j]` (1-based) of a coordinate vector: a range slice as Julia computes it, or the
elements of an explicit vector. -/
def sliceAxis (a : Axis) (i j : Nat) : Axis :=
  match a with
  | .stepLen r => .stepLen (sliceRange r i j)
  | _ => .explicit (floatsOfFn (j + 1 - i) fun k => a.get (i - 1 + k))

/-- Cartan's fourth-order stencil at the 0-based index `i` of a vector of length `l ≥ 4`
(`grid.jl:788-800`, `centraldiff_slow_calc` on an open grid). -/
@[inline] def stencil (f : FloatArray) (l i : Nat) : Float :=
  let g (k : Nat) : Float := f.get! k
  if i == 0 then 18 * g 1 - 9 * g 2 + 2 * g 3 - 11 * g 0
  else if i + 1 == l then 11 * g i - 18 * g (i - 1) + 9 * g (i - 2) - 2 * g (i - 3)
  else if i == 1 then 6 * g 2 - g 3 - 3 * g 1 - 2 * g 0
  else if i + 2 == l then 3 * g i - 6 * g (i - 1) + g (i - 2) + 2 * g (i + 1)
  else g (i - 2) + 8 * (g (i + 1) - g (i - 1)) - g (i + 2)

/-- Cartan's `gradient(f)` of a real field over an open 1-D grid (`grid.jl:596, 645`,
`gradient_slow`): at every point the stencil of the fibers over the stencil of the points. Julia
throws a `BoundsError` below four points; the port gives `NaN`s. -/
def gradient1 (xs ys : FloatArray) : FloatArray :=
  let l := ys.size
  if l < 4 then floatsOfFn l fun _ => F64.nan
  else floatsOfFn l fun i => stencil ys l i / stencil xs l i

/-- The elements `r[i+1] … r[i+k]` of a `TwicePrecision` range appended to `acc`, with the
index offset `u = i + 1 - offset` kept as a running `Float` (exact for any realistic length), so
the loop does no `Int` arithmetic; bit-identical to `StepRangeLen.get`
(`base/twiceprecision.jl:477-483`). -/
def rangeFill (r : StepRangeLen) (u : Float) (i : Nat) : Nat → FloatArray → FloatArray
  | 0, acc => acc
  | k + 1, acc =>
    let x := TwicePrecision.add12 r.ref.hi (u * r.step.hi)
    rangeFill r (u + f64! 1.0) (i + 1) k (acc.set! i (x.hi + (x.lo + (u * r.step.lo + r.ref.lo))))

/-- Julia `collect(r)` of a coordinate vector, with the fast loop for `TwicePrecision` ranges. -/
def axisValues (a : Axis) : FloatArray :=
  match a with
  | .stepLen r => rangeFill r (Axis.intToFloat (1 - r.offset)) 0 r.len (zeros r.len)
  | _ => a.toFloatArray

/-- Julia `GridBundle(PointArray(0, r))` of a 1-D coordinate vector: the open interval with real
points, as `Cartan.GridBundle.ofAxis a`, with the coordinates materialized by `axisValues` (the
same elements, several times faster than the generic `Axis.toFloatArray`; the tests compare the
two bases). -/
def grid1 (a : Axis) : GridBundle 1 Float :=
  let ps : ProductSpace 1 := ⟨#v[a], #v[axisValues a]⟩
  ⟨ps, MeshTopology.QuotientTopology.openTop ps.size, .induced, 0, rfl⟩

/-- A field with the given flat fibers (no copy when the length is right, which the callers
guarantee; otherwise the fibers are read with zero padding). -/
def fieldOf {M : Type} [FrameBundle M] {F : Type} [FlatFiber F] (m : M) (data : FloatArray) :
    TensorField m F :=
  if h : data.size = FlatFiber.width F * card m then ⟨data, h, none⟩
  else TensorField.ofFn m fun i => FlatFiber.read data (i * FlatFiber.width F)

/-- The real parts of an interleaved complex vector. -/
def reParts (z : FloatArray) : FloatArray := floatsOfFn (z.size / 2) fun i => z.get! (2 * i)

/-- The imaginary parts of an interleaved complex vector. -/
def imParts (z : FloatArray) : FloatArray := floatsOfFn (z.size / 2) fun i => z.get! (2 * i + 1)

end FlowGeometry
