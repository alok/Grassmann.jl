import Grassmann.Algebra.Metric
import Grassmann.Composite.Ring

/-!
# Composite functions with a runtime metric (Julia's `exp(t, g)`, `log_metric`, …)

Julia generates every composite function of `src/composite.jl` twice:
`for (op, field) ∈ ((:⟑, false), (:wedgedot_metric, true))`
(port-notes/grassmann-composite.md §4). The `field = true` copy is the same series with
`wedgedot_metric(·, ·, g)` in place of `⟑`. This module computes the same functions over
`Grassmann.Algebra.Metric`'s Gram-matrix product, **without** Julia's series loop.

Julia's loop runs `while (‖termₖ‖ < ‖termₖ₋₁‖ || ‖termₖ‖ > 1) && k ≤ 10000`: it stops as soon
as a term below 1 is not smaller than the one before. Under a general metric the product can
enlarge coefficient norms (`‖b ⟑_g b‖ > ‖b‖` for `‖b‖ < 1`), so the loop stops after the first
term and returns `1 + b` for `exp(b)`. With random symmetric `g` this gave
`‖exp(a) exp(−a) − 1‖ ≈ 0.3` (defect `series-stop-nonmonotone` in `oracle/defects.toml`).
The functions here use the standard matrix-function methods instead (Higham, *Functions of
Matrices*, ch. 10–11), and are accurate to a few ulps of the coefficient norm:

* `expMetric`: `e^s · exp(b)` for `t = s + b`, with `s` the scalar part. If `b ⟑_g b` is a
  scalar `h`, this is the closed form `cos θ + b sin θ/θ` (`θ = √|h|`; or the `cosh`/`sinh`
  one, or `1 + b`). Otherwise it is scaling and squaring: `exp(b) = exp(b/2ˢ)^(2ˢ)` with
  `ν(b)/2ˢ ≤ ½`, `ν(b) = max(‖b‖, √‖b ⟑_g b‖)`, and a Taylor sum that stops after two
  consecutive terms below `2⁻⁵⁵` of the sum.
* `expm1Metric`, `coshMetric`, `sinhMetric`: the Taylor series directly for `ν ≤ 1` (no
  cancellation), else from `exp(±b)`.
* `logMetric?`: inverse scaling and squaring: `log t = 2ᵏ log(t^(1/2ᵏ))`, with square roots
  until `‖t^(1/2ᵏ) − 1‖ ≤ ¼`, then `2 atanh((v − 1) ⟑ inv(v + 1))` by its series.
* `sqrtMetric?`: the product-form Denman–Beavers iteration
  `Mₖ₊₁ = ½ + (Mₖ + Mₖ⁻¹)/4`, `Yₖ₊₁ = Yₖ (1 + Mₖ⁻¹)/2` from `M₀ = Y₀ = t`.
* `invMetricLinear?`: the inverse of **any** invertible multivector. It solves
  `t ⟑_g x = 1` as a `2ⁿ × 2ⁿ` linear system with partial pivoting. Julia's `inv`, by
  contrast, only covers elements whose `~t ⟑ t` has a single grade.

A multivector counts as a scalar here only when every other coefficient is exactly zero
(Julia's `isscalar` accepts relative non-scalar parts up to `1.7e-4`, which would make
`log(1 + 10⁻⁵ e₁) = 0`).

With the induced metric these reproduce `Multivector.exp`/`log`/… to Julia's series
tolerance; for random metrics they satisfy `exp(a) exp(−a) = 1`, `exp(log u) = u`,
`√u √u = u` and commute with congruences (`Tests.Grassmann.Metric`).
-/

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase Composite Metric

variable {V : TensorBundle}

namespace MetricSeries

/-- The coefficient norm. -/
@[inline] def norm (m : Multivector V Float) : Float :=
  Float.sqrt (m.v.toList.foldl (fun s x => s + x * x) 0)

/-- `m + k` on the scalar part. -/
@[inline] def addScalar (k : Float) (m : Multivector V Float) : Multivector V Float :=
  Multivector.ofFn fun i => if i.1 = 0 then m.v.get i + k else m.v.get i

/-- `m / k`. -/
@[inline] def sdiv (m : Multivector V Float) (k : Float) : Multivector V Float := m.map (· / k)

/-- `k m`. -/
@[inline] def smul (k : Float) (m : Multivector V Float) : Multivector V Float := m.map (k * ·)

/-- `a + b`. -/
@[inline] def add (a b : Multivector V Float) : Multivector V Float :=
  Multivector.ofFn fun i => a.v.get i + b.v.get i

/-- The scalar multivector `x`. -/
@[inline] def scalar (x : Float) : Multivector V Float := Multivector.scalar x

end MetricSeries

open MetricSeries

/-- The inverse of any invertible multivector under the runtime metric `g`. It solves
`t ⟑_g x = 1` by Gaussian elimination with partial pivoting on the `2ⁿ × 2ⁿ` matrix of left
multiplication by `t`. The result is `none` when a pivot is below `1e-13` of the largest
entry (numerically singular). -/
def invMetricLinear? (g : Gram Float) (t : Multivector V Float) : Option (Multivector V Float) := Id.run do
  let N := 2 ^ V.n
  let bs := Leibniz.indexBasisAll V.n
  -- column j of the matrix is t ⟑ e_{b_j}
  let cols : Array (Array Float) := (Array.range N).map fun j =>
    (wedgedotMetric g t (ofTerms (({} : Terms Float).insert bs[j]! 1) : Multivector V Float)).v.toArray
  let mut A : Array (Array Float) := (Array.range N).map fun i =>
    ((Array.range N).map fun j => (cols[j]!)[i]!).push (if i == 0 then 1 else 0)
  let scale := A.foldl (fun m row => row.foldl (fun m x => max m x.abs) m) 0
  if scale == 0 then return none
  for c in [0:N] do
    let mut p := c
    for r in [c + 1:N] do
      if (A[r]!)[c]!.abs > (A[p]!)[c]!.abs then p := r
    if (A[p]!)[c]!.abs ≤ 1e-13 * scale then return none
    if p != c then
      let rp := A[p]!; let rc := A[c]!
      A := (A.set! p rc).set! c rp
    let piv := A[c]!
    for r in [0:N] do
      if r != c then
        let f := (A[r]!)[c]! / piv[c]!
        if f != 0 then
          A := A.modify r fun row => (Array.range (N + 1)).map fun k => row[k]! - f * piv[k]!
  return some (Multivector.ofFn fun i => (A[i.1]!)[N]! / (A[i.1]!)[i.1]!)

/-- Every non-scalar coefficient is exactly zero. -/
@[inline] def exactScalar (m : Multivector V Float) : Bool :=
  (List.range (2 ^ V.n)).all fun i => i == 0 || m.v.toList[i]! == 0

/-- `ν(b) = max(‖b‖, √‖b ⟑_g b‖)`, the size that decides the scaling. -/
@[inline] def metricSize (g : Gram Float) (b : Multivector V Float) : Float :=
  max (norm b) (Float.sqrt (norm (wedgedotMetric g b b)))

/-- The sum `S + term + step term k + …`, until two consecutive terms are below `2⁻⁵⁵` of the
partial sum (at most `fuel` terms). -/
def taylorLoop (step : Multivector V Float → Nat → Multivector V Float)
    (S term : Multivector V Float) (k small : Nat) : Nat → Multivector V Float
  | 0 => S
  | fuel + 1 =>
    let S := add S term
    let small := if norm term ≤ 2.8e-17 * norm S then small + 1 else 0
    if small ≥ 2 then S else taylorLoop step S (step term k) (k + 1) small fuel

/-- `x ⟑_g x` repeated `s` times. -/
def squareN (g : Gram Float) (x : Multivector V Float) : Nat → Multivector V Float
  | 0 => x
  | s + 1 => squareN g (wedgedotMetric g x x) s

/-- The smallest `s ≤ 64` with `ν / 2ˢ ≤ ½`. -/
def scalingFor (ν : Float) (s : Nat := 0) : Nat → Nat
  | 0 => s
  | fuel + 1 => if ν ≤ 0.5 then s else scalingFor (ν / 2) (s + 1) fuel

/-- The Taylor series of `exp(c) − 1` (no scaling). -/
@[inline] def expm1Taylor (g : Gram Float) (c : Multivector V Float) : Multivector V Float :=
  taylorLoop (fun t k => wedgedotMetric g t (sdiv c k.toFloat)) (MetricSeries.scalar 0) c 2 0 400

/-- `exp(b)` by scaling and squaring. -/
def expScaled (g : Gram Float) (b : Multivector V Float) : Multivector V Float :=
  let s := scalingFor (metricSize g b) 0 64
  let c := sdiv b (2 ^ s.toFloat)
  squareN g (addScalar 1 (expm1Taylor g c)) s

/-- Julia `expm1(t, g)`: the Taylor series for `ν(t) ≤ 1`, else `exp(t) − 1`. -/
def expm1Metric (g : Gram Float) (b : Multivector V Float) : Multivector V Float :=
  if exactScalar b then scalar (Float.exp b.scalarValue - 1)
  else if metricSize g b ≤ 1 then expm1Taylor g b
  else addScalar (-1) (expScaled g b)

/-- Julia `exp(t, g)`: `e^s exp(b)` with `s` the scalar part. `exp(b)` is in closed form when
`b ⟑_g b` is a scalar, and is computed by scaling and squaring otherwise. -/
def expMetric (g : Gram Float) (t : Multivector V Float) : Multivector V Float :=
  let s := t.scalarValue
  let b := addScalar (-s) t
  let es := Float.exp s
  let sq := wedgedotMetric g b b
  if norm b == 0 then scalar es
  else if exactScalar sq then
    let h := sq.scalarValue
    if h == 0 then smul es (addScalar 1 b)
    else
      let θ := Float.sqrt h.abs
      let (c, x) := if h < 0 then (Float.cos θ, Float.sin θ / θ) else (Float.cosh θ, Float.sinh θ / θ)
      smul es (addScalar c (smul x b))
  else smul es (expScaled g b)

/-- Julia `cosh(t, g)`: `1 + τ/2 + τ²/4! + …` (`τ = t ⟑_g t`) for `ν(t) ≤ 1`, else
`(exp t + exp(−t))/2`. -/
def coshMetric (g : Gram Float) (b : Multivector V Float) : Multivector V Float :=
  if exactScalar b then scalar (Float.cosh b.scalarValue)
  else if metricSize g b ≤ 1 then
    let τ := wedgedotMetric g b b
    taylorLoop (fun t k => wedgedotMetric g t (sdiv τ (2 * k * (2 * k - 1)).toFloat)) (MetricSeries.scalar 1)
      (sdiv τ 2) 2 0 400
  else sdiv (add (expMetric g b) (expMetric g (smul (-1) b))) 2

/-- Julia `sinh(t, g)`: `t + t⟑τ/3! + …` (`τ = t ⟑_g t`) for `ν(t) ≤ 1`, else
`(exp t − exp(−t))/2`. -/
def sinhMetric (g : Gram Float) (b : Multivector V Float) : Multivector V Float :=
  if exactScalar b then scalar (Float.sinh b.scalarValue)
  else if metricSize g b ≤ 1 then
    let τ := wedgedotMetric g b b
    taylorLoop (fun t k => wedgedotMetric g t (sdiv τ (2 * k * (2 * k + 1)).toFloat)) (MetricSeries.scalar 0) b 1
      0 400
  else sdiv (add (expMetric g b) (smul (-1) (expMetric g (smul (-1) b)))) 2

/-- The product-form Denman–Beavers iteration from `(M, Y)`. -/
def dbLoop (g : Gram Float) (M Y : Multivector V Float) : Nat → Option (Multivector V Float)
  | 0 => none
  | fuel + 1 => do
    let Mi ← invMetricLinear? g M
    let Y' := wedgedotMetric g Y (sdiv (addScalar 1 Mi) 2)
    let M' := addScalar 0.5 (sdiv (add M Mi) 4)
    if norm (addScalar (-1) M') ≤ 1e-15 * (1 + norm Y') then some Y'
    else dbLoop g M' Y' fuel

/-- The principal square root by Denman–Beavers (`none` when an iterate is singular, as for an
element with eigenvalues on the negative real axis, or when it does not converge). -/
@[inline] def sqrtDB (g : Gram Float) (t : Multivector V Float) : Option (Multivector V Float) :=
  dbLoop g t t 100

/-- `Σ_{k ≥ 0} w^(2k+1)/(2k+1)` (`atanh w`) from `pow = w^(2k+1)`. -/
def atanhLoop (g : Gram Float) (w2 S pow : Multivector V Float) (k small : Nat) :
    Nat → Multivector V Float
  | 0 => S
  | fuel + 1 =>
    let term := sdiv pow (2 * k + 1).toFloat
    let S := add S term
    let small := if norm term ≤ 2.8e-17 * norm S then small + 1 else 0
    if small ≥ 2 then S else atanhLoop g w2 S (wedgedotMetric g pow w2) (k + 1) small fuel

/-- Square roots of `v` until `‖v − 1‖ ≤ ¼`, with their count. -/
def rootsToOne (g : Gram Float) (v : Multivector V Float) (k : Nat) :
    Nat → Option (Multivector V Float × Nat)
  | 0 => none
  | fuel + 1 =>
    if norm (addScalar (-1) v) ≤ 0.25 then some (v, k)
    else (sqrtDB g v).bind fun r => rootsToOne g r (k + 1) fuel

/-- Julia `log(t, g)` by inverse scaling and squaring (`none` where the principal logarithm
is undefined or a square root does not converge). -/
def logMetric? (g : Gram Float) (t : Multivector V Float) : Option (Multivector V Float) :=
  if exactScalar t then
    if t.scalarValue > 0 then some (scalar (Float.log t.scalarValue)) else none
  else do
    let (v, k) ← rootsToOne g t 0 64
    let i ← invMetricLinear? g (addScalar 1 v)
    let w := wedgedotMetric g (addScalar (-1) v) i
    let L := atanhLoop g (wedgedotMetric g w w) (MetricSeries.scalar 0) w 0 0 400
    return smul (2 ^ (k + 1).toFloat) L

/-- Julia `sqrt(t, g)`: the principal square root (`none` where it is undefined). -/
def sqrtMetric? (g : Gram Float) (t : Multivector V Float) : Option (Multivector V Float) :=
  if exactScalar t then
    if t.scalarValue ≥ 0 then some (scalar (Float.sqrt t.scalarValue)) else none
  else sqrtDB g t

end Grassmann
