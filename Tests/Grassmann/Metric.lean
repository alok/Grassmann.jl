/-
`grassmann/metric`: products with a runtime metric (`Grassmann.Algebra.Metric`, Julia's
`wedgedot_metric`/`contraction_metric` family):

* **induced metric**: with `g = Gram.ofSpace V` the runtime-metric product and contraction
  are the plan kernels' `*` and `⋅`, for random multivectors in every non-dyadic `props`
  space. That covers diagonal, Lorentzian, degenerate (PGA) and conformal spaces, the last
  with the null pair `g(∞, ∅) = −1`;
* **non-diagonal metrics**: for `g = Pᵀ D P` with a random integer `P` (not necessarily
  invertible), the outermorphism `φ` of `P` is an algebra homomorphism `Cl(g) → Cl(D)`,
  so `φ(a ⟑_g b) = φ(a) ⟑ φ(b)` and `φ(a ⋅_g b) = φ(a) ⋅ φ(b)` with the kernel products of the
  diagonal space;
* the algebra axioms for random symmetric (also indefinite and degenerate) `g`: `x x = g(x,x)` for
  vectors, associativity, `inv` of vectors and of products of vectors, `^`;
* the composite functions: `exp`, `cosh`, `sinh` and `log` with the induced metric against the
  dense `Multivector` functions, the unprojected sandwiches against the kernels,
  `exp(a) exp(−a) = 1`, `exp(log u) = u` and `a inv(a) = 1` (the linear-solve inverse) for random `g`,
  and `φ(exp_g a) = exp(φ a)` for congruences.
-/
import Tests.Grassmann.Common
import Grassmann.Composite.Metric

open Grassmann DirectSum StaticVectors
open Grassmann.Metric (Terms termsOf ofTerms addTerm vecWedgeInto gens)

namespace GrassmannTests.MetricSuite

/-- Densify. -/
@[inline] def mv {X : Type} {V : TensorBundle} {α : Type} [AbstractTensors.Coeff α] [DenseLayout X V α]
    (x : X) : Multivector V α := toMultivector x

/-- The outermorphism of the matrix `P` (`φ(eᵢ) = Σⱼ Pⱼᵢ eⱼ`) applied to a multivector. -/
def outermorphism {V : TensorBundle} {α : Type} [AbstractTensors.Coeff α] (P : Array (Array Int))
    (m : Multivector V α) : Multivector V α :=
  let n := V.n
  let image := fun (A : UInt64) (x : α) => Id.run do
    -- φ(e_{a₁} ∧ … ∧ e_{aₖ}) = φ(e_{a₁}) ∧ … ∧ φ(e_{aₖ}), built right to left
    let mut t : Terms α := ({} : Terms α).insert 0 x
    for a in (gens A).reverse do
      t := t.fold (fun acc B y => Id.run do
        let mut acc := acc
        for j in [0:n] do
          let p := (P[j]!)[a]!
          if p != 0 then acc := vecWedgeInto j B (AbstractTensors.Coeff.ofInt p * y) acc
        return acc) {}
    return t
  ofTerms ((termsOf m).fold (fun acc A x =>
    (image A x).fold (fun acc C y => addTerm acc C y) acc) {})

/-- A random `n × n` integer matrix. -/
def randMat (n : Nat) (lo hi : Int) : Tests.Gen (Array (Array Int)) := do
  let mut rows := #[]
  for _ in [0:n] do
    rows := rows.push (← Tests.Gen.array n (Tests.Gen.int lo hi))
  return rows

/-- `Pᵀ D P` for a diagonal `D`. -/
def congruence (P : Array (Array Int)) (d : Array Int) : Gram Int :=
  Gram.ofFn d.size fun i k =>
    (List.range d.size).foldl (fun s j => s + (P[j]!)[i]! * d[j]! * (P[j]!)[k]!) 0

/-- A random symmetric integer Gram matrix. -/
def randSym (n : Nat) : Tests.Gen (Gram Int) := do
  let M ← randMat n (-2) 2
  return Gram.ofFn n fun i j => if i ≤ j then (M[i]!)[j]! else (M[j]!)[i]!

/-- The induced metric reproduces the kernels. -/
def induced (nm : String) (V : TensorBundle) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  let g : Gram Int := Gram.ofSpace V
  for _ in [0:trials] do
    let a ← randMV V
    let b ← randMV V
    t := t.check (wedgedotMetric g a b == a * b) s!"{nm}: wedgedot_metric(a, b, g_V) ≠ a * b"
    t := t.check (contractionMetric g a b == mv (AbstractTensors.Contraction.contraction a b))
      s!"{nm}: contraction_metric(a, b, g_V) ≠ a ⋅ b"
    let x ← randChain V 1
    let X := mv x
    t := t.check (contractionLeftMetric g X a == mv (leftContraction x a))
      s!"{nm}: x ⨼_g a ≠ x ⨼ a"
  return t

/-- Non-diagonal `g = Pᵀ D P` against the diagonal space `V` (`D` its own metric). -/
def congruent (nm : String) (V : TensorBundle) (d : Array Int) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let P ← randMat V.n (-2) 2
    let g := congruence P d
    let a ← randMV V
    let b ← randMV V
    let φ := outermorphism (V := V) P
    t := t.check (φ (wedgedotMetric g a b) == φ a * φ b) s!"{nm}: φ(a ⟑_g b) ≠ φ(a) ⟑ φ(b)"
    t := t.check (φ (contractionMetric g a b) == mv (AbstractTensors.Contraction.contraction (φ a) (φ b)))
      s!"{nm}: φ(a ⋅_g b) ≠ φ(a) ⋅ φ(b)"
  return t

/-- Algebra axioms for a random symmetric metric. -/
def axioms (nm : String) (V : TensorBundle) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:trials] do
    let g ← randSym V.n
    let a ← randMV V
    let b ← randMV V
    let c ← randMV V
    t := t.check (wedgedotMetric g (wedgedotMetric g a b) c == wedgedotMetric g a (wedgedotMetric g b c))
      s!"{nm}: (ab)c ≠ a(bc) for a random g"
    let x ← randChain V 1
    let X := mv x
    let gxx := (List.range V.n).foldl (fun s i =>
      (List.range V.n).foldl (fun s j => s + x.v.toList[i]! * g.get i j * x.v.toList[j]!) s) 0
    t := t.check (wedgedotMetric g X X == Multivector.scalar gxx) s!"{nm}: x x ≠ g(x, x)"
    t := t.check (powMetric g X 3 == wedgedotMetric g X (wedgedotMetric g X X)) s!"{nm}: x^3 ≠ x x x"
    -- inverses over ℚ: a vector, and a product of two vectors (a versor)
    let gq : Gram Rat := ⟨g.rows.map (·.map fun (k : Int) => (k : Rat))⟩
    let y ← randChain V 1
    let Xq := toRat X
    let R := wedgedotMetric gq Xq (toRat (mv y))
    for (lbl, u) in [("x", Xq), ("xy", R)] do
      match invMetric? gq u with
      | some ui =>
        t := t.check (wedgedotMetric gq u ui == Multivector.one) s!"{nm}: {lbl} inv({lbl}) ≠ 1"
      | none =>
        let n2 := (abs2Metric gq u).scalarValue
        t := t.check (n2 == 0) s!"{nm}: inv({lbl}) failed with ⟨~{lbl} {lbl}⟩₀ = {n2} ≠ 0"
  return t

/-- `‖a − b‖∞ / (1 + ‖b‖∞)`. -/
def relErr {V : TensorBundle} (a b : Multivector V Float) : Float :=
  let d := (List.range (2 ^ V.n)).foldl (fun m i => max m (a.v.toList[i]! - b.v.toList[i]!).abs) 0
  let s := b.v.toList.foldl (fun m x => max m x.abs) 0
  d / (1 + s)

/-- `‖a − b‖∞ ≤ tol (1 + ‖b‖∞)`. -/
def close {V : TensorBundle} (a b : Multivector V Float) (tol : Float := 1e-7) : Bool :=
  relErr a b ≤ tol

/-- A random multivector with coefficients in `[−0.3, 0.3]`. -/
def randSmall (V : TensorBundle) : Tests.Gen (Multivector V Float) := do
  let m ← randMV V
  return m.map fun (k : Int) => Float.ofInt k / 10

/-- A Gram matrix as floats. -/
def gramF (g : Gram Int) : Gram Float := ⟨g.rows.map (·.map Float.ofInt)⟩

/-- The composite functions with the induced metric against the dense ones, and the
metric-free identities for random metrics. -/
def composite (nm : String) (V : TensorBundle) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  let gV : Gram Float := Gram.ofSpace V
  let gI : Gram Int := Gram.ofSpace V
  for _ in [0:trials] do
    let a ← randSmall V
    t := t.check (close (expMetric gV a) (Multivector.exp a)) s!"{nm}: exp(a, g_V) ≠ exp(a)"
    t := t.check (close (coshMetric gV a) (Multivector.cosh a)) s!"{nm}: cosh(a, g_V) ≠ cosh(a)"
    t := t.check (close (sinhMetric gV a) (Multivector.sinh a)) s!"{nm}: sinh(a, g_V) ≠ sinh(a)"
    let u := MetricSeries.addScalar 1 (a.map (· / 2))
    match logMetric? gV u, Multivector.log? u with
    | some l, some l' => t := t.check (close l l' 1e-6) s!"{nm}: log(u, g_V) ≠ log(u)"
    | _, _ => pure ()
    -- the sandwiches with the induced metric are the kernels' unprojected ones
    let R ← randMV V
    let x ← randMV V
    t := t.check (tsandwichMetric gI R x == tsandwichFull R x) s!"{nm}: R ⟑_g x ⟑_g clifford(R) ≠ kernel"
    t := t.check (sandwichMetric gI x R == sandwichFull x R) s!"{nm}: ~R ⟑_g x ⟑_g involute(R) ≠ kernel"
    -- a random symmetric metric
    let g := gramF (← randSym V.n)
    match invMetricLinear? g a with
    | some ai => t := t.check (close (wedgedotMetric g a ai) Multivector.one 1e-9) s!"{nm}: a ⟑_g inv(a) ≠ 1"
    | none => pure ()
    t := t.check (close (wedgedotMetric g (expMetric g a) (expMetric g (a.map (- ·)))) Multivector.one 1e-9)
      s!"{nm}: exp(a) exp(−a) ≠ 1 for a random g (err {relErr (wedgedotMetric g (expMetric g a) (expMetric g (a.map (- ·)))) Multivector.one}, ‖a‖ {MetricSeries.norm a})"
    match logMetric? g u with
    | some l => t := t.check (close (expMetric g l) u 1e-9) s!"{nm}: exp(log(u)) ≠ u for a random g (err {relErr (expMetric g l) u})"
    | none => pure ()
    match sqrtMetric? g u with
    | some r => t := t.check (close (wedgedotMetric g r r) u 1e-9) s!"{nm}: √u √u ≠ u for a random g (err {relErr (wedgedotMetric g r r) u})"
    | none => pure ()
    let ch := coshMetric g a
    let sh := sinhMetric g a
    let one := MetricSeries.add (wedgedotMetric g ch ch) ((wedgedotMetric g sh sh).map (- ·))
    t := t.check (close one Multivector.one 1e-9) s!"{nm}: cosh² − sinh² ≠ 1 for a random g (err {relErr one Multivector.one})"
    t := t.check (close (MetricSeries.add ch sh) (expMetric g a) 1e-9)
      s!"{nm}: cosh + sinh ≠ exp for a random g (err {relErr (MetricSeries.add ch sh) (expMetric g a)})"
    t := t.check (close (MetricSeries.addScalar 1 (expm1Metric g a)) (expMetric g a) 1e-9)
      s!"{nm}: 1 + expm1 ≠ exp for a random g"
    -- larger elements exercise the scaling (and, for log, the square roots)
    let big := a.map (· * 8)
    let E := expMetric g big
    let Ei := expMetric g (big.map (- ·))
    -- forming E ⟑ E⁻¹ in floating point loses `κ = ‖E‖ ‖E⁻¹‖` ulps
    let κ := (1 + MetricSeries.norm E) * (1 + MetricSeries.norm Ei)
    t := t.check (relErr (wedgedotMetric g E Ei) Multivector.one ≤ 1e-12 * κ)
      s!"{nm}: exp(8a) exp(−8a) ≠ 1 for a random g (err {relErr (wedgedotMetric g E Ei) Multivector.one}, κ {κ})"
  return t

/-- `exp` commutes with the outermorphism of a congruence `g = Pᵀ D P`. -/
def congruentExp (nm : String) (V : TensorBundle) (d : Array Int) (trials : Nat) : Tests.Gen Tally := do
  let mut t : Tally := {}
  let gD : Gram Float := Gram.ofSpace V
  for _ in [0:trials] do
    let P ← randMat V.n (-1) 1
    let g := gramF (congruence P d)
    let a ← randSmall V
    let φ := outermorphism (V := V) (α := Float) P
    t := t.check (close (φ (expMetric g a)) (expMetric gD (φ a)) 1e-10) s!"{nm}: φ(exp_g a) ≠ exp(φ a) (err {relErr (φ (expMetric g a)) (expMetric gD (φ a))})"
  return t

/-- Run the suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  let mut seed := 20261105
  for (nm, V) in spaces do
    seed := seed + 1
    if V.dyadmode == 0 && !V.istangent then
      t := t.merge (Tests.Gen.run seed (induced nm V 10))
  for (nm, V, d) in [("E3", S!"+++", #[1, 1, 1]), ("S(-++)", S!"-++", #[-1, 1, 1]),
      ("M4", S!"-+++", #[-1, 1, 1, 1])] do
    seed := seed + 1
    t := t.merge (Tests.Gen.run seed (congruent nm V d 8))
    t := t.merge (Tests.Gen.run (seed + 300) (axioms nm V 6))
    t := t.merge (Tests.Gen.run (seed + 600) (congruentExp nm V d 6))
  for (nm, V) in spaces do
    seed := seed + 1
    if V.dyadmode == 0 && !V.istangent then
      t := t.merge (Tests.Gen.run (seed + 900) (composite nm V 6))
  return t

end GrassmannTests.MetricSuite
