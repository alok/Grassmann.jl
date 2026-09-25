import MeshTopology.Product
import JuliaBase.Range

/-!
# Resampling coordinate ranges

MeshTopology.jl `resample(m, i)` on ranges and vectors (`src/MeshTopology.jl:31-46`): the
coordinate axes of Cartan's `ProductSpace` are resampled to `i` points with the same end points.
Integer ranges, `LinRange`s and plain vectors become `LinRange(first, last, i)`; a
`StepRangeLen` keeps its first element and is respaced with `range(first; step, length = i)`,
`step = step(m)·(length(m)-1)/(i-1)`. Every element is bit-exact with Julia (the ranges come from
`JuliaBase.Range`).
-/

namespace MeshTopology

open JuliaBase

/-- The `Float64` ranges `resample` returns. -/
inductive FloatRange where
  /-- `LinRange{Float64}`. -/
  | lin (r : LinRange)
  /-- `StepRangeLen{Float64, TwicePrecision, TwicePrecision}`. -/
  | stepLen (r : StepRangeLen)
  deriving Inhabited

namespace FloatRange

/-- Julia type name (`LinRange` or `StepRangeLen`). -/
def typeName : FloatRange → String
  | lin _ => "LinRange"
  | stepLen _ => "StepRangeLen"

/-- Julia `collect`, packed. -/
def toFloatArray : FloatRange → FloatArray
  | lin r => r.toFloatArray
  | stepLen r => r.toFloatArray

/-- Number of points. -/
def length : FloatRange → Nat
  | lin r => r.len
  | stepLen r => r.len

/-- Julia `resample(m, i)` (MT:39-40): a `LinRange` keeps its end points; a `StepRangeLen` keeps
its first element and spreads the same span over `i` points. -/
def resample (m : FloatRange) (i : Nat) : FloatRange :=
  match m with
  | lin r => lin (LinRange.mk' r.start r.stop i)
  | stepLen r =>
    stepLen (rangeStep r.first ((r.stepValue * Float.ofNat (r.len - 1)) / Float.ofNat (i - 1)) i)

end FloatRange

/-- Julia `resample(m, i)` for an integer axis (MT:36-38, 46): `LinRange(first, last, i)`
(`OneTo`, `UnitRange`, `StepRange`, and as a plain vector `CrossRange`/`Vector{Int}`). -/
def AxisMap.resampleFloat (m : AxisMap) (i : Nat) : FloatRange :=
  .lin (LinRange.mk' (Float.ofInt m.first) (Float.ofInt m.last) i)

/-- Julia `resample(v::AbstractVector, i = length(v))` (MT:46): `LinRange(v[1], v[end], i)`. -/
def resampleVector (v : FloatArray) (i : Nat := v.size) : FloatRange :=
  .lin (LinRange.mk' v[0]! v[v.size - 1]! i)

end MeshTopology
