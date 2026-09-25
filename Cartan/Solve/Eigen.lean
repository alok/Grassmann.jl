import Cartan.Solve.Iterative

/-!
# Symmetric and generalized symmetric eigenproblems

For finite-element modes (`A x = λ M x`, stiffness `A` and mass `M`, Adapode's
`geneigsolve`/`eigs` usage) and for small dense operators:

* `Dense.symEigen`: all eigenpairs of a dense symmetric matrix by the cyclic Jacobi method
  (rotations annihilating each off-diagonal entry in turn until the off-diagonal norm is below
  `1e-15` of the Frobenius norm): ascending eigenvalues, orthonormal eigenvectors;
* `Dense.genEigen`: `A x = λ M x` with `M` symmetric positive definite, reduced to
  `L⁻¹ A L⁻ᵀ y = λ y` with `M = L Lᵀ` and back-transformed (`x = L⁻ᵀ y`), so the eigenvectors are
  `M`-orthonormal (as Julia's `eigen(Symmetric(A), Symmetric(M))`, LAPACK `sygvd`);
* `Sparse.geneigsolve`: the `k` smallest eigenpairs above a shift `σ` of the sparse pencil by
  shift-invert Lanczos in the `M` inner product with full reorthogonalization: the operator
  `(A - σM)⁻¹ M` (one envelope factorization, `Cartan.Solve.Sparse`), Ritz values `θ` of the
  Lanczos tridiagonal (implicit QL, `Dense.tridiagEigen`) mapped back by `λ = σ + 1/θ`. The
  Krylov dimension grows until every requested pair has relative residual
  `‖A x - λ M x‖ ≤ tol ‖A x‖`.

Eigenvectors are determined up to sign (and within eigenspaces); tests compare eigenvalues and
normalized residuals, or vectors after fixing the sign of the largest component.
-/

namespace Cartan.Solve

namespace Dense

/-- All eigenpairs of a symmetric matrix (cyclic Jacobi): eigenvalues ascending and the
orthonormal eigenvectors as the columns of the second component. -/
def symEigen (A0 : Dense) (maxSweeps : Nat := 60) : FloatArray × Dense := Id.run do
  let n := A0.rows
  let mut A := A0
  let mut Vm := identity n
  let fro := Float.sqrt (A0.data.data.foldl (fun s x => s + x * x) 0)
  for _ in [0:maxSweeps] do
    let mut off := 0.0
    for p in [0:n] do
      for q in [p + 1:n] do
        let x := A.get p q
        off := off + x * x
    if Float.sqrt (2 * off) ≤ 1e-15 * fro then break
    for p in [0:n] do
      for q in [p + 1:n] do
        let apq := A.get p q
        if apq != 0 then
          let app := A.get p p
          let aqq := A.get q q
          let θ := (aqq - app) / (2 * apq)
          let t := (if θ ≥ 0 then 1 else -1) / (θ.abs + Float.sqrt (θ * θ + 1))
          let c := 1 / Float.sqrt (t * t + 1)
          let s := t * c
          -- A ← Jᵀ A J on rows/columns p, q
          let mut d := A.data
          for k in [0:n] do
            let akp := d.get! (p * n + k)
            let akq := d.get! (q * n + k)
            d := (d.set! (p * n + k) (c * akp - s * akq)).set! (q * n + k) (s * akp + c * akq)
          for k in [0:n] do
            let apk := d.get! (k * n + p)
            let aqk := d.get! (k * n + q)
            d := (d.set! (k * n + p) (c * apk - s * aqk)).set! (k * n + q) (s * apk + c * aqk)
          A := { A with data := d }
          let mut v := Vm.data
          for k in [0:n] do
            let vkp := v.get! (p * n + k)
            let vkq := v.get! (q * n + k)
            v := (v.set! (p * n + k) (c * vkp - s * vkq)).set! (q * n + k) (s * vkp + c * vkq)
          Vm := { Vm with data := v }
  -- sort ascending
  let order := (Array.range n).qsort fun i j => A.get i i < A.get j j
  let vals : FloatArray := ⟨order.map fun i => A.get i i⟩
  let vecs := ofFn n n fun r c => Vm.get r order[c]!
  return (vals, vecs)

/-- `A x = λ M x` for symmetric `A` and symmetric positive definite `M` (see the module note);
`none` if `M` is not positive definite. -/
def genEigen (A M : Dense) : Option (FloatArray × Dense) := do
  let L ← M.cholesky
  let n := A.rows
  -- C = L⁻¹ A L⁻ᵀ: solve column by column
  let Y := ofFn n n fun i j => (forwardSub L ⟨(Array.range n).map fun r => A.get r j⟩).get! i
  -- Y = L⁻¹ A; C = (L⁻¹ Yᵀ)ᵀ = L⁻¹ A L⁻ᵀ (A symmetric)
  let Yt := Y.transpose
  let C0 := ofFn n n fun i j => (forwardSub L ⟨(Array.range n).map fun r => Yt.get r j⟩).get! i
  let C := ofFn n n fun i j => (C0.get i j + C0.get j i) / 2
  let (vals, W) := C.symEigen
  let X := ofFn n n fun i j => (backSubT L ⟨(Array.range n).map fun r => W.get r j⟩).get! i
  return (vals, X)

end Dense

namespace Sparse

/-- The result of `geneigsolve`: eigenvalues ascending, `M`-orthonormal eigenvectors, the
Krylov dimension used and the largest relative residual. -/
structure GenEigen where
  /-- Eigenvalues (ascending). -/
  vals : FloatArray
  /-- Eigenvectors. -/
  vecs : Array FloatArray
  /-- Lanczos steps taken. -/
  steps : Nat
  /-- `max ‖A x - λ M x‖ / ‖A x‖`. -/
  residual : Float
  deriving Inhabited

/-- `k` smallest eigenpairs of `A x = λ M x` above the shift `σ` (see the module note): `A`
symmetric, `M` symmetric positive definite, `A - σM` factorable. -/
def geneigsolve (A M : Sparse) (k : Nat) (σ : Float := 0) (tol : Float := 1e-10) :
    Option GenEigen := Id.run do
  let n := A.rows
  let K := lincomb 1 A (-σ) M
  let some F := (K.cholesky.orElse fun _ => K.luNoPivot) | return none
  let op (v : FloatArray) : FloatArray := F.solve (M.mulVec v)
  let mdot (x y : FloatArray) : Float := Vec.dot x (M.mulVec y)
  let mut m := min n (max (2 * k + 20) 40)
  let mut best : Option GenEigen := none
  for _ in [0:6] do
    -- start vector: deterministic, not orthogonal to smooth modes
    let v0 : FloatArray := ⟨(Array.range n).map fun i =>
      1 + 0.5 * Float.sin (Float.ofNat (i + 1) * 0.618033988749895)⟩
    let nv := Float.sqrt (mdot v0 v0)
    let mut V : Array FloatArray := #[⟨v0.data.map (· / nv)⟩]
    let mut αs : FloatArray := .empty
    let mut βs : FloatArray := .empty
    let mut steps := 0
    for j in [0:m] do
      let vj := V[j]!
      let mut w := op vj
      let α := mdot w vj
      αs := αs.push α
      w := Vec.axpy (-α) vj w
      if j > 0 then w := Vec.axpy (-(βs.get! (j - 1))) V[j - 1]! w
      -- full reorthogonalization (twice)
      for _ in [0:2] do
        for i in [0:V.size] do
          let c := mdot w V[i]!
          w := Vec.axpy (-c) V[i]! w
      steps := j + 1
      let β := Float.sqrt (mdot w w)
      if j + 1 == m || β ≤ 1e-14 * (αs.get! j).abs then break
      βs := βs.push β
      V := V.push ⟨w.data.map (· / β)⟩
    let some (θs, Y) := Dense.tridiagEigen αs βs | return best
    -- the largest θ are the smallest λ above σ
    let s := θs.size
    let take := min k s
    let mut vals : FloatArray := .empty
    let mut vecs : Array FloatArray := #[]
    let mut worst := 0.0
    for r in [0:take] do
      let c := s - 1 - r
      let θ := θs.get! c
      let lam := σ + 1 / θ
      let mut x := Vec.zeros n
      for i in [0:s] do
        x := Vec.axpy (Y.get i c) V[i]! x
      let Ax := A.mulVec x
      let Mx := M.mulVec x
      let res := Sparse.vnorm (Vec.axpy (-lam) Mx Ax) / (Sparse.vnorm Ax + 1e-300)
      worst := max worst res
      vals := vals.push lam
      vecs := vecs.push x
    let out : GenEigen := ⟨vals, vecs, steps, worst⟩
    best := some out
    if worst ≤ tol || m ≥ n then return best
    m := min n (2 * m)
  return best

end Sparse

end Cartan.Solve
