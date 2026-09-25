import Adapode.ODE.Leapfrog

/-!
# Geodesic equations (`geodesic`, `geosolve`)

Adapode's geodesic front-end (`src/Adapode.jl:609-622`) integrates Cartan's geodesic system
(`Cartan.jl src/diffgeo.jl:1266-1272`) on the phase state `X = (x, v)` (Julia `Chain(x0, v0)`):

```
f(X) = ( v , -Σⱼ Σᵢ Γ(x)[i,j] (vᵢ vⱼ) )
```

where `Γ(x)[i,j]` is the vector of Christoffel symbols of the second kind `Γᵏᵢⱼ` (Julia's
`TensorOperator(Chain(C₁, …, Cₙ))[i,j] = Cⱼ[i]`). The double sum is one left fold over `j` outer,
`i` inner (`+(Γ[1,1]*(v₁v₁), Γ[2,1]*(v₂v₁), Γ[1,2]*(v₁v₂), …)`), each term the vector `Γ[i,j]`
scaled by `vᵢ vⱼ`, and the result is negated.

`Christoffel n` stores `Γ(x)` flat in Julia's memory order: `Γ[i,j]ₖ` at `(j·n + i)·n + k`
(0-based). The metric of the README's upper half plane `(dx² + dy²)/y²` is `halfPlane`.

`geosolve` returns the positions (Julia `getindex.(odesolve(…), 1)`).
-/

namespace Adapode

open JuliaBase Grassmann DirectSum StaticVectors Cartan

/-- Christoffel symbols of the second kind at a point: `n³` floats, `Γ[i,j]ₖ` at `(j·n + i)·n + k`
(Julia `TensorOperator(Chain(C₁, …, Cₙ))`, `Cⱼ[i] = Γ[i,j]`). -/
abbrev Christoffel := FloatArray

/-- `acc + Γ[i,j]ₖ (vᵢ vⱼ)` over the remaining pairs `(i, j)` (`j` outer, `i` inner), component `k`. -/
def geoSumLoop (Γ v : FloatArray) (n k : Nat) : (m p : Nat) → Float → Float
  | 0, _, acc => acc
  | m + 1, p, acc =>
    let i := p % n
    let j := p / n
    geoSumLoop Γ v n k m (p + 1) (acc + Γ.get! ((j * n + i) * n + k) * (v.get! i * v.get! j))

/-- Julia `geodesic(x2, Γ)` component `k` (`diffgeo.jl:1270-1272`): the first term starts the sum. -/
@[inline] def geoSum (Γ v : FloatArray) (n k : Nat) : Float :=
  geoSumLoop Γ v n k (n * n - 1) 1 (Γ.get! k * (v.get! 0 * v.get! 0))

/-- Write `f(X) = (v, -Σ Γ[i,j] vᵢvⱼ)` for the flat phase state `X = (x, v)` into `out`. -/
def geoWriteLoop (Γ v : FloatArray) (n : Nat) : (m k : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | m + 1, k, out =>
    geoWriteLoop Γ v n m (k + 1) ((out.set! k (v.get! k)).set! (n + k) (-(geoSum Γ v n k)))

@[simp] theorem size_geoWriteLoop (Γ v : FloatArray) (n : Nat) :
    ∀ (m k : Nat) (out : FloatArray), (geoWriteLoop Γ v n m k out).size = out.size
  | 0, _, _ => rfl
  | m + 1, k, out => by
    rw [geoWriteLoop, size_geoWriteLoop Γ v n m (k + 1), FloatArray.size_set!', FloatArray.size_set!']

/-- The geodesic system of the Christoffel field `Γ` on phase states (Julia `geodesic(Γ)`,
`diffgeo.jl:1266-1269`), in destination-passing form. -/
@[inline] def geodesicSystem {V : TensorBundle} (Γ : Chain V 1 Float → Christoffel) :
    Float → Float → Phase V → Phase V → Phase V :=
  fun _ _ X out =>
    let n := Leibniz.binomial V.n 1
    ⟨geoWriteLoop (Γ X.pos) (slice X.data n n) n n 0 out.data, by simp [out.size_data]⟩

/-- Julia `geodesic(Γ, x0, v0, tmax=2π)` (`Adapode.jl:613-614`): the initial condition of the
geodesic through `x0` with velocity `v0`. -/
@[inline] def geodesic {V : TensorBundle} (Γ : Chain V 1 Float → Christoffel) (x0 v0 : Chain V 1 Float)
    (tmax : Float := twoPi) : InitialCondition (Phase V) :=
  ⟨⟨geodesicSystem Γ, tmax⟩, Phase.mk' x0 v0, 0⟩

/-- The upper half plane `(dx² + dy²)/y²` of the README (`README.md:131-139`): `Γ[1,1] = (0, 1/y)`,
`Γ[1,2] = Γ[2,1] = (-1/y, 0)`, `Γ[2,2] = (0, -1/y)` (Julia `inv(x[2])`). -/
def halfPlane (x : Chain ℝ2 1 Float) : Christoffel :=
  let r := f64! 1 / x.v.get! 1
  let a : FloatArray := FloatArray.empty
  -- j = 1: Γ[1,1], Γ[2,1]; j = 2: Γ[1,2], Γ[2,2]
  ((((((((a.push 0).push r).push (-r)).push 0).push (-r)).push 0).push 0).push (-r))

end Adapode
