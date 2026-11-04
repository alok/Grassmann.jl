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
  vectors, associativity, `inv` of vectors and of products of vectors, `^`.
-/
import Tests.Grassmann.Common
import Grassmann.Algebra.Metric

open Grassmann DirectSum StaticVectors
open Grassmann.Metric (Terms termsOf ofTerms addTerm vecWedgeInto gens)

namespace GrassmannTests.MetricSuite

/-- Densify. -/
@[inline] def mv {X : Type} {V : TensorBundle} {α : Type} [AbstractTensors.Coeff α] [DenseLayout X V α]
    (x : X) : Multivector V α := toMultivector x

/-- The outermorphism of the matrix `P` (`φ(eᵢ) = Σⱼ Pⱼᵢ eⱼ`) applied to a multivector. -/
def outermorphism {V : TensorBundle} (P : Array (Array Int)) (m : Multivector V Int) :
    Multivector V Int :=
  let n := V.n
  let image := fun (A : UInt64) (x : Int) => Id.run do
    -- φ(e_{a₁} ∧ … ∧ e_{aₖ}) = φ(e_{a₁}) ∧ … ∧ φ(e_{aₖ}), built right to left
    let mut t : Terms Int := ({} : Terms Int).insert 0 x
    for a in (gens A).reverse do
      t := t.fold (fun acc B y => Id.run do
        let mut acc := acc
        for j in [0:n] do
          let p := (P[j]!)[a]!
          if p != 0 then acc := vecWedgeInto j B (p * y) acc
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
  return t

end GrassmannTests.MetricSuite
