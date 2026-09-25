import Cartan.Fiber
import MeshTopology

/-!
# Coordinate axes: Julia's 1-D point vectors

Every structured Cartan base is a product of 1-D coordinate vectors (Julia `ProductSpace.v`,
`topology.jl:46-50`), and a 1-D base built from a range keeps the range itself as its points.
Julia distinguishes the vector types, and their elements differ in the last bit:

* `a:s:b` and `range(a, b; length = n)` for `Float64` are `StepRangeLen`s with
  `TwicePrecision` reference and step (`(0:0.1:1)[4] == 0.3` exactly);
* `LinRange(a, b, n)` computes `(1-t)*a + t*b`;
* integer ranges (`UnitRange`, `StepRange`, `OneTo`) are exact;
* any other vector is explicit data.

`Axis` keeps that distinction, with the elements from `JuliaBase.Range` (bit-exact with Julia).
Integer ranges are stored exactly but their points are read as `Float`s: Julia's integer points
(`Chain{V,1,Int}`) are not modelled (docs/port-notes/cartan-core.md §4.4).

Julia keeps a range *lazy* under the broadcasts `x .* r`, `r .* x`, `r ./ x`, `-r` and `r₁ ± r₂`
(`base/broadcast.jl:1133-1191`, `base/twiceprecision.jl:625-641`, `base/range.jl:1471-1500`),
so the identity field of a range, scaled or added to another, keeps producing
`TwicePrecision`-exact elements (`2π .* (0:0.1:1)` is not `2π .* collect(0:0.1:1)`). The
`neg`, `scale`, `div`, `add`, `sub` operations below are those range methods; Cartan's `Float`
fields use them to stay bit-identical with Julia.
-/

namespace Cartan

open JuliaBase

/-! ## Constants (Julia's `Irrational` arithmetic, rounded as `Float64`) -/

/-- Julia `Float64(π)`. -/
def piF : Float := f64! 3.141592653589793
/-- Julia `2π` (`Float64(2) * Float64(π)`, exact). -/
def twoPiF : Float := f64! 6.283185307179586
/-- Julia `4π`. -/
def fourPiF : Float := f64! 12.566370614359172
/-- Julia `π/2`. -/
def halfPiF : Float := f64! 1.5707963267948966

/-- A Julia 1-D coordinate vector (the element type of `ProductSpace.v`). -/
inductive Axis where
  /-- `StepRangeLen{Float64, TwicePrecision, TwicePrecision}`: `a:s:b`, `range(a, b; length)`. -/
  | stepLen (r : StepRangeLen)
  /-- `LinRange{Float64}`: `LinRange(a, b, n)`. -/
  | lin (r : LinRange)
  /-- `UnitRange`/`StepRange{Int}`/`OneTo`: `start, start + step, …` (`len` points). -/
  | ints (start step : Int) (len : Nat)
  /-- Any other `AbstractVector{Float64}`. -/
  | explicit (xs : FloatArray)
  deriving Inhabited

namespace Axis

/-! ## Constructors -/

/-- Julia `a:s:b` for `Float64` (`base/twiceprecision.jl:390-432`). -/
def colon (a s b : Float) : Axis := .stepLen (JuliaBase.colon a s b)

/-- Julia `range(a, b; length = n)` for `Float64` (`base/twiceprecision.jl:645-666`). -/
def range (a b : Float) (n : Nat) : Axis := .stepLen (JuliaBase.range a b n)

/-- Julia `LinRange(a, b, n)` (`base/range.jl:579-610`). -/
def linRange (a b : Float) (n : Nat) : Axis := .lin (LinRange.mk' a b n)

/-- Julia `a:b` for integers. -/
def unitRange (a b : Int) : Axis := .ints a 1 (b - a + 1).toNat

/-- Julia `Base.OneTo(n)` = `1:n`. -/
def oneTo (n : Nat) : Axis := .ints 1 1 n

/-- An explicit vector of points. -/
def ofArray (xs : FloatArray) : Axis := .explicit xs

/-! ## Access -/

/-- Julia `length(r)`. -/
def length : Axis → Nat
  | stepLen r => r.len
  | lin r => r.len
  | ints _ _ n => n
  | explicit xs => xs.size

/-- Element `i` (0-based; Julia `r[i+1]`, unchecked: out-of-range indices extrapolate the
range, or read `0.0` from an explicit vector). -/
@[inline] def get (a : Axis) (i : Nat) : Float :=
  match a with
  | stepLen r => r.get (Int.ofNat i + 1)
  | lin r => r.get (Int.ofNat i + 1)
  | ints s d _ => Float.ofInt (s + d * Int.ofNat i)
  | explicit xs => xs[i]!

/-- Julia `first(r)`. -/
def first (a : Axis) : Float := a.get 0

/-- Julia `last(r)` (`r[end]`). -/
def last (a : Axis) : Float := a.get (a.length - 1)

/-- Julia `step(r)` for a range (`Float64(r.step)`, `(stop - start)/lendiv` for a `LinRange`);
`none` for an explicit vector. -/
def step? : Axis → Option Float
  | stepLen r => some r.stepValue
  | lin r => some r.stepValue
  | ints _ d _ => some (Float.ofInt d)
  | explicit _ => none

/-- Julia `isrange(r)` (`topology.jl:72-73`): `true` for every `AbstractRange`. -/
def isRange : Axis → Bool
  | explicit _ => false
  | _ => true

/-- Julia `widths(r) = r[end] - r[1]` (`topology.jl:117`). -/
def width (a : Axis) : Float := a.last - a.first

/-- Julia `collect(r)`, packed. -/
def toFloatArray (a : Axis) : FloatArray :=
  match a with
  | explicit xs => xs
  | _ => buildFlat a.length a.get

@[simp] theorem size_toFloatArray (a : Axis) : a.toFloatArray.size = a.length := by
  cases a <;> simp [toFloatArray, length, FlatFiber.width]

/-- Julia `r == s` for vectors: same length and equal elements. -/
def eqv (a b : Axis) : Bool :=
  a.length == b.length && (List.range a.length).all fun i => a.get i == b.get i

instance : BEq Axis := ⟨eqv⟩

/-! ## Resampling and extension -/

/-- Julia `resample(r, n)` (MeshTopology.jl `src/MeshTopology.jl:36-46`): a `StepRangeLen` keeps its
first element and spreads the same span over `n` points (`range(r[1]; step = step·(len-1)/(n-1),
length = n)`); every other vector becomes `LinRange(r[1], r[end], n)`. -/
def resample (a : Axis) (n : Nat) : Axis :=
  match a with
  | stepLen r =>
    .stepLen (rangeStep r.first ((r.stepValue * Float.ofNat (r.len - 1)) / Float.ofNat (n - 1)) n)
  | _ => .lin (LinRange.mk' a.first a.last n)

/-- Julia `extend(r, i) = r[1]:step(r):r[end]+step(r)*(i-length(r))` (`Cartan.jl:559`): the range
continued by whole steps to `i` points; `none` for an explicit vector. -/
def extend (a : Axis) (i : Nat) : Option Axis := do
  let s ← a.step?
  match a with
  | ints st d n => return .ints st d (if n ≥ i then n else i)
  | _ =>
    let stop := a.last + s * (Float.ofInt ((i : Int) - (a.length : Int)))
    return .stepLen (JuliaBase.colon a.first s stop)

/-! ## Lazy range arithmetic (Julia keeps these results as ranges) -/

/-- Julia `-r` (broadcast `.-r`, `base/broadcast.jl:1138-1141`); `none` if not a float range. -/
def neg : Axis → Option Axis
  | stepLen r => some (.stepLen r.neg)
  | lin r => some (.lin r.neg)
  | _ => none

/-- Julia `x .* r` = `r .* x` (`base/broadcast.jl:1172-1184`); `none` if not a float range. -/
def scale (x : Float) : Axis → Option Axis
  | stepLen r => some (.stepLen (r.bcastMul x))
  | lin r => some (.lin (r.bcastMul x))
  | _ => none

/-- Julia `r ./ x` (`base/broadcast.jl:1186-1190`); `none` if not a float range. -/
def div (x : Float) : Axis → Option Axis
  | stepLen r => some (.stepLen (r.bcastDiv x))
  | lin r => some (.lin (r.bcastDiv x))
  | _ => none

/-- Julia `_getindex_hiprec(r, i)` (`base/twiceprecision.jl:486-492`): element `i` (1-based)
as a `TwicePrecision`. -/
def hiprec (r : StepRangeLen) (i : Int) : TwicePrecision :=
  let u := Float.ofInt (i - r.offset)
  let shiftHi := u * r.step.hi
  let shiftLo := u * r.step.lo
  let x := TwicePrecision.add12 r.ref.hi shiftHi
  TwicePrecision.add12 x.hi (x.lo + (shiftLo + r.ref.lo))

/-- Julia `+(r1::StepRangeLen{T,<:TwicePrecision}, r2)` (`base/twiceprecision.jl:625-641`). -/
def addStepLen (r1 r2 : StepRangeLen) : StepRangeLen :=
  let len := r1.len
  let (imid, ref) :=
    if r1.offset == r2.offset then (r1.offset, TwicePrecision.add r1.ref r2.ref)
    else
      let imid := F64.roundInt ((Float.ofInt r1.offset + Float.ofInt r2.offset) / 2)
      (imid, TwicePrecision.add (hiprec r1 imid) (hiprec r2 imid))
  let step := TwicePrecision.twiceprecision (TwicePrecision.add r1.step r2.step)
    (StepRangeLen.nbitslen len imid)
  ⟨ref, step, len, imid⟩

/-- Julia `r₁ + r₂` of two ranges of the same length that Julia keeps lazy (two `StepRangeLen`s,
two `LinRange`s: `base/range.jl:1471-1500`); `none` otherwise. -/
def add : Axis → Axis → Option Axis
  | stepLen r1, stepLen r2 => if r1.len == r2.len then some (.stepLen (addStepLen r1 r2)) else none
  | lin r1, lin r2 =>
    if r1.len == r2.len then some (.lin (LinRange.mk' (r1.start + r2.start) (r1.stop + r2.stop) r1.len))
    else none
  | _, _ => none

/-- Julia `r₁ - r₂` (`base/range.jl:1471-1502`: `r₁ + (-r₂)` for `StepRangeLen`s, endpoint
differences for `LinRange`s); `none` otherwise. -/
def sub : Axis → Axis → Option Axis
  | stepLen r1, stepLen r2 => if r1.len == r2.len then some (.stepLen (addStepLen r1 r2.neg)) else none
  | lin r1, lin r2 =>
    if r1.len == r2.len then some (.lin (LinRange.mk' (r1.start - r2.start) (r1.stop - r2.stop) r1.len))
    else none
  | _, _ => none

/-! ## Display -/

/-- Julia `show(io, r)`: `first:step:last` for a float or integer range
(`base/range.jl:1114, 1121`), `LinRange{Float64}(start, stop, len)` (`base/range.jl:622`),
`Base.OneTo(n)`, and `[x₁, x₂, …]` for a vector. -/
def showString : Axis → String
  | stepLen r => s!"{F64.showString r.first}:{F64.showString r.stepValue}:{F64.showString r.last}"
  | lin r => s!"LinRange\{Float64}({F64.showString r.start}, {F64.showString r.stop}, {r.len})"
  | ints s d n =>
    if s == 1 && d == 1 then s!"Base.OneTo({n})"
    else if d == 1 then s!"{s}:{s + Int.ofNat n - 1}"
    else s!"{s}:{d}:{s + d * (Int.ofNat n - 1)}"
  | explicit xs => "[" ++ ", ".intercalate (xs.toList.map F64.showString) ++ "]"

instance : ToString Axis := ⟨showString⟩

end Axis

end Cartan
