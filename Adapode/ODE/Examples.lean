import Adapode.ODE.Solve

/-!
# The chaotic systems of `examples/chaos.jl`

Adapode's example file integrates classic chaotic attractors with the default solver
(`odesolve(f, x0)`: RK4, `h = 2^-15`, `t ∈ [0, 2π]`, 205 888 points) from `x0 = (10, 10, 10)`:

| Julia (`examples/chaos.jl`) | Lean |
|---|---|
| `Lorenz(σ,r,b)` (lines 4-7): `(σ(y-x), x(r-z)-y, xy-bz)` | `lorenz`, `lorenzInto` |
| `DiskDynamo(a,b,c)` (13-16): `(a(y-x), zx-y, b-xy-cz)` | `diskDynamo`, `diskDynamoInto` |
| `Rossler(a,b,c)` (19-22): `(-(y+z), x+ay, b+z(x-c))` | `rossler`, `rosslerInto` |
| `ChemicalKinetics(a1,…,a5,k1,k2)` (34-38) | `chemicalKinetics` (fixed) |
| `Rossler4(a,b,c,d)` (40-45) | `rossler4` (fixed) |

Each system is written with Julia's operation order (`x[1]*(r-x[3])-x[2]` is `x₁(r - x₃) - x₂`,
`b-x[1]*x[2]-c*x[3]` is `(b - x₁x₂) - cx₃`), so trajectories match Julia bit for bit
(`Tests/Adapode`). The `…Into` forms write into the scratch state (no allocation per evaluation;
use them with `Flow.into`); the plain forms return a new `Chain`, as Julia's do.

The example file has two broken systems (port notes B22): `ChemicalKinetics` is called with eight
arguments but takes seven and reads an undefined `k5` (here `k5` is the eighth parameter), and
`Rossler4` reads `x[4]` of a three-dimensional state (here it is a system on `ℝ4`).
-/

namespace Adapode

open JuliaBase Grassmann DirectSum StaticVectors Cartan

/-- `Chain(a, b, c)` in `ℝ3` (Julia `Chain(a, b, c)`). -/
@[inline] def vec3 (a b c : Float) : Chain ℝ3 1 Float :=
  ⟨⟨((FloatArray.emptyWithCapacity 3).push a |>.push b |>.push c),
    by show FloatArray.size _ = _; simp only [FloatArray.size_push']; rfl⟩⟩

/-- `Chain(a, b, c, d)` in `ℝ4`. -/
@[inline] def vec4 (a b c d : Float) : Chain ℝ4 1 Float :=
  ⟨⟨((FloatArray.emptyWithCapacity 4).push a |>.push b |>.push c |>.push d),
    by show FloatArray.size _ = _; simp only [FloatArray.size_push']; rfl⟩⟩

/-- Overwrite a vector of `ℝ3` with `(a, b, c)` (in place when unshared). -/
@[inline] def put3 (x : Chain ℝ3 1 Float) (a b c : Float) : Chain ℝ3 1 Float :=
  ⟨⟨((x.v.data.set! 0 a).set! 1 b).set! 2 c,
    by show FloatArray.size _ = _; simp only [FloatArray.size_set!']; exact x.v.size_eq⟩⟩

/-- Component `i` (0-based; Julia `x[i+1]`). -/
@[inline] def comp {V : TensorBundle} (x : Chain V 1 Float) (i : Nat) : Float := x.v.data.get! i

/-- Julia `Lorenz(σ,r,b)` (`examples/chaos.jl:4-7`). -/
@[inline] def lorenz (σ r b : Float) (x : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  vec3 (σ * (x2 - x1)) (x1 * (r - x3) - x2) (x1 * x2 - b * x3)

/-- `lorenz` written into `out`. -/
@[inline] def lorenzInto (σ r b : Float) (x out : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  put3 out (σ * (x2 - x1)) (x1 * (r - x3) - x2) (x1 * x2 - b * x3)

/-- Julia `DiskDynamo(a,b,c)` (`examples/chaos.jl:13-16`). -/
@[inline] def diskDynamo (a b c : Float) (x : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  vec3 (a * (x2 - x1)) (x3 * x1 - x2) (b - x1 * x2 - c * x3)

/-- `diskDynamo` written into `out`. -/
@[inline] def diskDynamoInto (a b c : Float) (x out : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  put3 out (a * (x2 - x1)) (x3 * x1 - x2) (b - x1 * x2 - c * x3)

/-- Julia `Rossler(a,b,c)` (`examples/chaos.jl:19-22`). -/
@[inline] def rossler (a b c : Float) (x : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  vec3 (-(x2 + x3)) (x1 + a * x2) (b + x3 * (x1 - c))

/-- `rossler` written into `out`. -/
@[inline] def rosslerInto (a b c : Float) (x out : Chain ℝ3 1 Float) : Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  put3 out (-(x2 + x3)) (x1 + a * x2) (b + x3 * (x1 - c))

/-- Julia `ChemicalKinetics(a1,a2,a3,a4,a5,k1,k2)` (`examples/chaos.jl:34-38`) with the missing `k5`
as an eighth parameter (the file calls it with eight arguments, B22). -/
@[inline] def chemicalKinetics (a1 a2 a3 a4 a5 k1 k2 k5 : Float) (x : Chain ℝ3 1 Float) :
    Chain ℝ3 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2
  vec3 (x1 * (a1 - k1 * x1 - x3 - x2) + k2 * x2 * x2 + a3) (x2 * (x1 - k2 * x2 - a5) + a2)
    (x3 * (a4 - x1 - k5 * x3) + a3)

/-- Julia `Rossler4(a,b,c,d)` (`examples/chaos.jl:40-45`), Rössler's hyperchaos on `ℝ4` (the file
starts it from a three-dimensional state, B22). -/
@[inline] def rossler4 (a b c d : Float) (x : Chain ℝ4 1 Float) : Chain ℝ4 1 Float :=
  let x1 := comp x 0; let x2 := comp x 1; let x3 := comp x 2; let x4 := comp x 3
  vec4 (-(x2 + x3)) (x1 + a * x2 + x4) (b + x3 * x1) (d * x4 - c * x3)

/-- The starting point of `examples/chaos.jl`, `Chain(10.0, 10.0, 10.0)`. -/
def chaosStart : Chain ℝ3 1 Float := vec3 10 10 10

end Adapode
