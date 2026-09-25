import JuliaBase.Range

/-!
# Wilkinson's sample grids: Julia float ranges `l:st:u`

Wilkinson samples `floatset(T, N; scale) = l:(u-l)/(N-1):u`, a Julia
`StepRangeLen`, and compares it point for point against Julia: `JuliaBase.colon` for
`Float64` (a `TwicePrecision` range, base/twiceprecision.jl:390-432) and
`JuliaBase.colon32` for `Float32` (a `JuliaBase.StepRangeLen32`).

`FloatSet` is the element-type-tagged grid the analysis runs over.
-/

namespace Wilkinson

open JuliaBase

/-- The element types Wilkinson evaluates in. -/
inductive NumType where
  /-- `Float64`. -/
  | f64
  /-- `Float32`. -/
  | f32
  /-- `BigFloat` (256 bits). -/
  | big
  deriving BEq, Inhabited, Repr, DecidableEq

/-- A Julia float grid: `StepRangeLen{Float64, TwicePrecision}` or
`StepRangeLen{Float32, Float64}`. -/
inductive FloatSet where
  /-- A `Float64` range. -/
  | f64 (r : StepRangeLen)
  /-- A `Float32` range. -/
  | f32 (r : StepRangeLen32)
  deriving Inhabited

namespace FloatSet

/-- Julia `length(r)`. -/
def len : FloatSet → Nat
  | .f64 r => r.len
  | .f32 r => r.len

/-- Julia `eltype(r)`. -/
def elemType : FloatSet → NumType
  | .f64 _ => .f64
  | .f32 _ => .f32

/-- Element `i` (1-based), widened to `Float64`. -/
def get (s : FloatSet) (i : Nat) : Float :=
  match s with
  | .f64 r => r.get i
  | .f32 r => (r.get i).toFloat

/-- Julia `first(r)`. -/
def first (s : FloatSet) : Float := s.get 1

/-- Julia `last(r)`. -/
def last (s : FloatSet) : Float := s.get s.len

/-- Julia `step(r)`, widened (`Float32(r.step)` for a `Float32` range). -/
def stepValue : FloatSet → Float
  | .f64 r => r.stepValue
  | .f32 r => r.step.toFloat32.toFloat

/-- Julia `collect(r)`, widened to `Float64` and packed. -/
def collect (s : FloatSet) : FloatArray :=
  go 1 (FloatArray.emptyWithCapacity s.len) s.len
where
  /-- Tail-recursive fill. -/
  go (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | k + 1 => go (i + 1) (acc.push (s.get i)) k

end FloatSet

end Wilkinson
