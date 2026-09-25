import JuliaBase.Range

/-!
# Wilkinson's sample grids: Julia float ranges `l:st:u`

Wilkinson samples `floatset(T, N; scale) = l:(u-l)/(N-1):u`, a Julia
`StepRangeLen`, and compares it point for point against Julia. For `Float64`
that is `JuliaBase.colon` (a `TwicePrecision` range, base/twiceprecision.jl:390-432).
`JuliaBase` has no `Float32` colon, so it is ported here: the same algorithm with
`rat` and the range checks in `Float32` arithmetic and a `Float64` reference and
step (`steprangelen_hp(::Type{Float32}, …)`, twiceprecision.jl:340-362), which is
`JuliaBase.StepRangeLen32`.

`FloatSet` is the element-type-tagged grid the analysis runs over.
-/

namespace Wilkinson

open JuliaBase

/-- Julia `isbetween(a, x, b)` for `Float32` (twiceprecision.jl:790). -/
@[inline] def isbetween32 (a x b : Float32) : Bool := (a ≤ x && x ≤ b) || (b ≤ x && x ≤ a)

/-- Julia `round(Int, x::Float32)` (ties to even; exact through `Float64`). -/
@[inline] def roundInt32 (x : Float32) : Int := F64.roundInt x.toFloat

/-- Julia `floatrange(Float32, start_n, step_n, len, den)` (twiceprecision.jl:376) with the
`Float32` `steprangelen_hp`: reference and step are the `Float64` quotients `n/den`. -/
def floatrange32 (startN stepN : Int) (len : Nat) (den : Int) : StepRangeLen32 :=
  let q (n : Int) : Float := Float.ofInt n / Float.ofInt den
  if len < 2 || stepN == 0 then ⟨q startN, q stepN, len, 1⟩
  else
    let imin := F64.roundInt (Float.ofInt (-startN) / Float.ofInt stepN + 1)
    let imin := if imin < 1 then 1 else if imin > len then (len : Int) else imin
    ⟨q (startN + (imin - 1) * stepN), q stepN, len, imin⟩

/-- Julia `start:step:stop` for `Float32` (`(:)(start::T, step::T, stop::T)`,
twiceprecision.jl:390-432): exact rational endpoints give a `floatrange`,
otherwise start and step are taken literally. `T(n/d)` checks divide in `Float64`
and round, as Julia's `Int/Int` does. Julia throws for `step == 0`; this returns an
empty range. -/
def colon32 (start step stop : Float32) : StepRangeLen32 :=
  if step == 0 then ⟨start.toFloat, 0, 0, 1⟩
  else
    let literal : Unit → StepRangeLen32 := fun _ =>
      let lf := (stop - start) / step
      let len : Int :=
        if lf < 0 then 0
        else if lf == 0 then 1
        else
          let len := roundInt32 lf + 1
          let stop' := start + Float32.ofInt (len - 1) * step
          len - (if start < stop && stop < stop' then 1 else 0)
              - (if start > stop && stop > stop' then 1 else 0)
      ⟨start.toFloat, step.toFloat, len.toNat, 1⟩
    let exact (n d : Int) (x : Float32) : Bool := (Float.ofInt n / Float.ofInt d).toFloat32 == x
    let (stepN, stepD) := rat32 step
    if stepD != 0 && exact stepN stepD step then
      let (startN, startD) := rat32 start
      let (stopN, stopD) := rat32 stop
      if startD != 0 && stopD != 0 && exact startN startD start && exact stopN stopD stop then
        let den := lcmUnchecked startD stepD
        let denF := Float32.ofInt den
        let m : Float32 := 16777216
        if den != 0 && (start * denF).abs ≤ m && (step * denF).abs ≤ m &&
            den.tmod startD == 0 && den.tmod stepD == 0 then
          let startN := roundInt32 (start * denF)
          let stepN := roundInt32 (step * denF)
          let len := max 0 ((den * stopN - stopD * startN + stepN * stopD).tdiv (stepN * stopD))
          if isbetween32 start (start + Float32.ofInt (len - 1) * step) (stop + step / 2) &&
              !isbetween32 start (start + Float32.ofInt len * step) stop then
            floatrange32 startN stepN len.toNat den
          else literal ()
        else literal ()
      else literal ()
    else literal ()

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
