import Tests.Forms.Common
import Tests.Util.Random

/-!
# Algebraic properties of the Forms layer (property tests, SplitMix64 seeds)

Beyond the oracle's samples, over random integer and rational matrices of every size up
to 6 (exact) and random real matrices up to 8:

* the compound family: Cauchy–Binet `Λᵍ(AB) = Λᵍ A Λᵍ B`, `det(AB) = det A det B`,
  `adj(A) A = A adj(A) = det(A) I`, `tr O(A) = det(I + A)`, the outermorphism property
  `O(x ∧ y) = O(x) ∧ O(y)`, `(AB)ᵀ = BᵀAᵀ`, `Aᵀᵀ = A`;
* inverses: `A⁻¹ A = I` exactly over `ℚ`, the Moore–Penrose identities `A A⁺ A = A`;
* spectra: the closed-form characteristic polynomial equals the compound-trace one over
  `ℚ` (`n ≤ 4`, Newton's identities), the Pfaffian squares to the determinant of a
  skew-symmetric matrix, the eigen-decomposition residuals of random real matrices up to
  `8 × 8`, `p(root) ≈ 0` for the closed-form roots, `exp(A) exp(−A) ≈ I`,
  `exp(log S) ≈ S` for symmetric positive definite `S`;
* diagonal operators agree with their materialised operators (compounds, outermorphism,
  adjugate, action on multivectors);
* simplices: barycentric coordinates sum to one, and the barycentric gradients are the
  dual basis of the edges.
-/

namespace Tests.FormsTests.Props

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests

/-- A random integer matrix with entries in `[-4, 4]`. -/
def randRows (r c : Nat) : Tests.Gen (List (List Int)) := do
  let mut rows := []
  for _ in [0:r] do
    let row ← Tests.Gen.array c (Tests.Gen.int (-4) 4)
    rows := rows ++ [row.toList]
  return rows

/-- A random real matrix with entries in `[-2, 2)`. -/
def randRowsF (r c : Nat) : Tests.Gen (List (List Float)) := do
  let mut rows := []
  for _ in [0:r] do
    let row ← Tests.Gen.array c (Tests.Gen.floatIn (-2) 2)
    rows := rows ++ [row.toList]
  return rows

/-- Exact properties of one pair of random integer matrices of size `n`. -/
def exactProps (t : Tally) (n seed : Nat) : Tally := Id.run do
  let (ra, rb, xs, ys) := Tests.Gen.run seed do
    let ra ← randRows n n
    let rb ← randRows n n
    let xs ← Tests.Gen.array n (Tests.Gen.int (-3) 3)
    let ys ← Tests.Gen.array n (Tests.Gen.int (-3) 3)
    return (ra, rb, xs, ys)
  let V := En n
  let A : Endomorphism V (.chain 1) Int := endo V ra
  let B : Endomorphism V (.chain 1) Int := endo V rb
  let w := fun (s : String) => fun (_ : Unit) => s!"props n={n} seed={seed} {s}"
  let mut t := t
  for g in [0:n + 1] do
    t := t.ok (((A * B).compound g).toRows == ((A.compound g) * (B.compound g)).toRows) (w s!"Cauchy–Binet g={g}")
  t := t.ok ((A * B).det == A.det * B.det) (w "det(AB)")
  let dI : Endomorphism V (.chain 1) Int := TensorOperator.uniform A.det
  if n ≥ 2 then
    t := t.ok ((A.adjugate * A).toRows == dI.toRows) (w "adj(A) A = det I")
    t := t.ok ((A * A.adjugate).toRows == dI.toRows) (w "A adj(A) = det I")
  t := t.ok (A.outermorphism.tr == (A + AbstractTensors.UniformScaling.mk (1 : Int)).det) (w "tr O = det(I+A)")
  t := t.ok ((A * B).transpose.toRows == (B.transpose * A.transpose).toRows) (w "(AB)ᵀ = BᵀAᵀ")
  t := t.ok (A.transpose.transpose.toRows == A.toRows) (w "Aᵀᵀ = A")
  if n ≥ 2 then
    let x : Chain V 1 Int := chainOf V 1 xs.toList
    let y : Chain V 1 Int := chainOf V 1 ys.toList
    let O := A.outermorphism
    let lhs : Chain V 2 Int := O * (x ∧ y)
    let rhs : Chain V 2 Int := (A * x : Chain V 1 Int) ∧ (A * y : Chain V 1 Int)
    t := t.ok (lhs.v.toList == rhs.v.toList) (w "O(x∧y) = Ax∧Ay")
  -- exact inverse over ℚ
  let Aq := A.map fun (z : Int) => (z : Rat)
  if A.det != 0 then
    let I : Endomorphism V (.chain 1) Rat := TensorOperator.identity
    t := t.ok ((Aq.inv * Aq).toRows == I.toRows) (w "A⁻¹A = I over ℚ")
  -- Newton's identities: closed forms = compound traces
  if n ≤ 4 then
    t := t.ok (Aq.characteristic.v.toList == Aq.characteristicExact.v.toList) (w "characteristic closed = exact")
  -- Pfaffian² = det of the skew part (even n)
  if n % 2 == 0 && n ≥ 2 then
    let S : Endomorphism V (.chain 1) Rat := Aq - Aq.transpose
    let pf := getD (Endomorphism.pfaffian S).v 0
    t := t.ok (pf * pf == S.det) (w "pf² = det")
  -- diagonal operators
  let D : DiagonalMorphism V Int := ⟨Values.ofFn fun i => getD A.diagValues i.1⟩
  let Dm := D.toOperator
  for g in [0:n + 1] do
    t := t.ok ((DiagonalMorphism.compound D g).toOperator.toRows == (Dm.compound g).toRows) (w s!"diag compound {g}")
  if n ≥ 2 then
    t := t.ok ((DiagonalMorphism.adjugate D).toOperator.toRows == Dm.adjugate.toRows) (w "diag adjugate")
  t := t.ok ((DiagonalMorphism.outermorphism D).toOperator.toRows == Dm.outermorphism.toOperator.toRows)
    (w "diag outermorphism")
  return t

/-- Moore–Penrose identity `A A⁺ A = A` of a random `m × n` rational matrix of full rank. -/
def pinvProps (t : Tally) (m n seed : Nat) : Tally :=
  let ra := Tests.Gen.run seed (randRows m n)
  let A : Simplex (En n) (En m) Rat :=
    (TensorOperator.ofRows? (ra.map (·.map fun (z : Int) => (z : Rat)))).getD TensorOperator.zero
  let rank := if m < n then (A * A.transpose).det else (A.transpose * A).det
  if rank == 0 then t
  else t.ok ((A * (A.inv * A)).toRows == A.toRows) fun _ => s!"props pinv {m}×{n} seed={seed}: A A⁺ A = A"

/-- Floating-point properties of one random real matrix of size `n`. -/
def floatProps (t : Tally) (n seed : Nat) : Tally := Id.run do
  let rows := Tests.Gen.run seed (randRowsF n n)
  let V := En n
  let A : Endomorphism V (.chain 1) Float := endo V rows
  let w := fun (s : String) => fun (_ : Unit) => s!"float props n={n} seed={seed} {s}"
  let mut t := t
  -- eigen residuals
  let d := A.eigenDecomposition
  let normA := (List.range (n * n)).foldl (fun m i => max m (A.entry (i / n) (i % n)).abs) 1
  let mut worst : Float := 0
  for j in [0:n] do
    for i in [0:n] do
      let (sr, si) := (List.range n).foldl (fun (sr, si) k =>
        (sr + A.entry i k * d.vre.get! (k * n + j), si + A.entry i k * d.vim.get! (k * n + j))) ((0 : Float), (0 : Float))
      let er := sr - (d.re.get! j * d.vre.get! (i * n + j) - d.im.get! j * d.vim.get! (i * n + j))
      let ei := si - (d.re.get! j * d.vim.get! (i * n + j) + d.im.get! j * d.vre.get! (i * n + j))
      worst := max worst (Float.sqrt (er * er + ei * ei))
  t := t.ok (worst ≤ 1e-10 * normA) (w s!"eigen residual {worst}")
  -- exp(A) exp(-A) = I
  let E := A.exp * (-A).exp
  let I : Endomorphism V (.chain 1) Float := TensorOperator.identity
  let err := (List.range (n * n)).foldl (fun m i => max m (E.entry (i / n) (i % n) - I.entry (i / n) (i % n)).abs) 0
  t := t.ok (err ≤ 1e-9) (w s!"exp(A)exp(-A) = I ({err})")
  -- exp(log S) = S for S = AᵀA + I
  let S := A.transpose * A + AbstractTensors.UniformScaling.mk (1 : Float)
  match S.log with
  | .ok L =>
    let E := L.exp
    let err := (List.range (n * n)).foldl (fun m i =>
      max m ((E.entry (i / n) (i % n) - S.entry (i / n) (i % n)).abs / max 1 (S.entry (i / n) (i % n)).abs)) 0
    t := t.ok (err ≤ 1e-10) (w s!"exp(log S) = S ({err})")
  | .error e => t := t.ok false (w s!"log S: {e}")
  -- inverse
  if A.det.abs > 1e-3 then
    let E := A.inv * A
    let err := (List.range (n * n)).foldl (fun m i => max m (E.entry (i / n) (i % n) - I.entry (i / n) (i % n)).abs) 0
    t := t.ok (err ≤ 1e-8) (w s!"A⁻¹A = I ({err})")
  return t

/-- `p(z) ≈ 0` at the closed-form roots of a random monic polynomial of degree `n ≤ 4`. -/
def rootProps (t : Tally) (n seed : Nat) : Tally :=
  let a := Tests.Gen.run seed (Tests.Gen.array n (Tests.Gen.floatIn (-3) 3))
  let av : Values Float n := Values.ofFn fun i => a[i.1]!
  match Forms.Roots.monicroots? av with
  | none => t
  | some s =>
    let ok := s.toList.all fun z =>
      -- Horner in complex arithmetic: zⁿ + a_{n-1} zⁿ⁻¹ + … + a₀
      let p := (List.range n).reverse.foldl (fun (acc : JuliaBase.Complex Float) k =>
        acc * z + ⟨a[k]!, 0⟩) ⟨1, 0⟩
      let scale := 1 + a.foldl (fun m x => max m x.abs) 0
      JuliaBase.ComplexF64.abs p ≤ 1e-9 * scale * scale * scale * scale
    t.ok ok fun _ => s!"roots n={n} seed={seed}: p(root) ≈ 0 ({a})"

/-- Barycentric coordinates and gradients of a random simplex in `ℝᵈ`. -/
def simplexProps (t : Tally) (d seed : Nat) : Tally := Id.run do
  let (pts, q) := Tests.Gen.run seed do
    let pts ← (List.range (d + 1)).mapM fun _ => Tests.Gen.array d (Tests.Gen.floatIn (-2) 2)
    let q ← Tests.Gen.array d (Tests.Gen.floatIn (-1) 1)
    return (pts, q)
  let W := En (d + 1)
  let cols := pts.map fun p => chainOf W 1 (1 :: p.toList)
  let T : Simplex (En (d + 1)) W Float := (TensorOperator.ofColumnList? cols).getD TensorOperator.zero
  if T.det.abs < 1e-3 then return t
  let w := fun (s : String) => fun (_ : Unit) => s!"simplex props d={d} seed={seed} {s}"
  let mut t := t
  let lam := T.solve (chainOf W 1 (1 :: q.toList))
  let s := lam.v.toList.foldl (· + ·) 0
  t := t.ok ((s - 1).abs ≤ 1e-10) (w s!"Σλ = 1 ({s})")
  -- ∇λᵢ · (pⱼ − p₀) = δᵢⱼ − δᵢ₀
  let G := T.gradient
  let mut err : Float := 0
  for i in [0:d + 1] do
    for j in [1:d + 1] do
      let dot := (List.range d).foldl (fun acc k => acc + G.entry k i * (T.entry (k + 1) j - T.entry (k + 1) 0)) 0
      let want : Float := (if i == j then 1 else 0) - (if i == 0 then 1 else 0)
      err := max err (dot - want).abs
  t := t.ok (err ≤ 1e-9) (w s!"gradients are the dual frame ({err})")
  return t

/-- Run the property suite. -/
def suite : IO Tally := do
  let mut t := Tally.new "forms/props"
  for n in [1:7] do
    for s in [0:(if n ≤ 4 then 25 else 8)] do
      t := exactProps t n (1000 * n + s)
  for (m, n) in [(3, 2), (2, 3), (4, 2), (4, 3), (5, 3), (3, 5)] do
    for s in [0:10] do
      t := pinvProps t m n (7000 + 100 * m + 10 * n + s)
  for n in [1:9] do
    for s in [0:6] do
      t := floatProps t n (9000 + 10 * n + s)
  for n in [1:5] do
    for s in [0:50] do
      t := rootProps t n (11000 + 100 * n + s)
  for d in [1:5] do
    for s in [0:10] do
      t := simplexProps t d (13000 + 100 * d + s)
  return t

end Tests.FormsTests.Props
