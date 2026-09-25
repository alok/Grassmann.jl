import Cartan.Solve.Sparse

/-!
# Krylov solvers and the `A \ b` dispatcher

* `cg`: conjugate gradients with a Jacobi (diagonal) preconditioner, for symmetric positive
  definite systems (FEM stiffness and mass matrices);
* `bicgstab`: van der Vorst's BiCGSTAB with a Jacobi preconditioner, for general systems;
* `Sparse.solve`: Julia's `A \ b` for sparse matrices. Julia dispatches to CHOLMOD when `A` is
  symmetric positive definite and to UMFPACK otherwise; here small systems (`n ≤ 64`) go to
  dense LU with partial pivoting, symmetric ones to the RCM envelope Cholesky, others to the
  envelope LU, and a failed factorization (indefinite, tiny pivot) falls back to dense LU
  (`n ≤ 3000`) or BiCGSTAB. Every path checks its relative residual.

Vector kernels (`dot`, `axpy`) are tail-recursive Float loops.
-/

namespace Cartan.Solve

namespace Vec

/-- `Σ x[i] y[i]` (left to right). -/
def dot (x y : FloatArray) : Float := go 0 0 x.size
where
  /-- The loop. -/
  go (i : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => go (i + 1) (s + x.get! i * y.get! i) r

/-- `y + a x`. -/
def axpy (a : Float) (x y : FloatArray) : FloatArray := go y 0 y.size
where
  /-- The loop. -/
  go (y : FloatArray) (i : Nat) : Nat → FloatArray
    | 0 => y
    | r + 1 => go (y.set! i (y.get! i + a * x.get! i)) (i + 1) r

/-- `x + b y` written over a copy of `x` (the update `p = r + β p`, with `x` = `r`). -/
def xpby (x : FloatArray) (b : Float) (y : FloatArray) : FloatArray := go x 0 x.size
where
  /-- The loop. -/
  go (z : FloatArray) (i : Nat) : Nat → FloatArray
    | 0 => z
    | r + 1 => go (z.set! i (z.get! i + b * y.get! i)) (i + 1) r

/-- Entrywise product `x ⊙ y`. -/
def hadamard (x y : FloatArray) : FloatArray := go x 0 x.size
where
  /-- The loop. -/
  go (z : FloatArray) (i : Nat) : Nat → FloatArray
    | 0 => z
    | r + 1 => go (z.set! i (z.get! i * y.get! i)) (i + 1) r

/-- `x - y`. -/
def sub (x y : FloatArray) : FloatArray := axpy (-1) y x

/-- The zero vector. -/
def zeros (n : Nat) : FloatArray := ⟨Array.replicate n 0⟩

end Vec

/-- The result of an iterative solve. -/
structure IterResult where
  /-- The approximate solution. -/
  x : FloatArray
  /-- Iterations used. -/
  iters : Nat
  /-- Final relative residual `‖b - A x‖ / ‖b‖`. -/
  relres : Float
  /-- Whether the tolerance was met. -/
  converged : Bool
  deriving Inhabited

/-- Jacobi preconditioner: `1 / A[i,i]` (1 where the diagonal is zero). -/
def jacobi (A : Sparse) : FloatArray :=
  ⟨(A.diag.data).map fun d => if d == 0 then 1 else 1 / d⟩

/-- Preconditioned conjugate gradients for SPD `A` from `x₀` (default zero). -/
def cg (A : Sparse) (b : FloatArray) (tol : Float := 1e-12) (maxIter : Nat := 0)
    (x0 : Option FloatArray := none) : IterResult := Id.run do
  let n := b.size
  let maxIter := if maxIter == 0 then 10 * n + 100 else maxIter
  let Minv := jacobi A
  let nb := Sparse.vnorm b
  if nb == 0 then return ⟨Vec.zeros n, 0, 0, true⟩
  let mut x := x0.getD (Vec.zeros n)
  let mut r := Vec.sub b (A.mulVec x)
  let mut z := Vec.hadamard r Minv
  let mut p := z
  let mut rz := Vec.dot r z
  let mut it := 0
  let mut res := Sparse.vnorm r / nb
  while res > tol && it < maxIter do
    let Ap := A.mulVec p
    let pAp := Vec.dot p Ap
    if pAp == 0 then break
    let α := rz / pAp
    x := Vec.axpy α p x
    r := Vec.axpy (-α) Ap r
    res := Sparse.vnorm r / nb
    z := Vec.hadamard r Minv
    let rz' := Vec.dot r z
    p := Vec.xpby z (rz' / rz) p
    rz := rz'
    it := it + 1
  let rr := A.relResidual x b
  return ⟨x, it, rr, rr ≤ tol * 100⟩

/-- Jacobi-preconditioned BiCGSTAB (van der Vorst 1992) from `x₀` (default zero). -/
def bicgstab (A : Sparse) (b : FloatArray) (tol : Float := 1e-12) (maxIter : Nat := 0)
    (x0 : Option FloatArray := none) : IterResult := Id.run do
  let n := b.size
  let maxIter := if maxIter == 0 then 10 * n + 100 else maxIter
  let Minv := jacobi A
  let nb := Sparse.vnorm b
  if nb == 0 then return ⟨Vec.zeros n, 0, 0, true⟩
  let mut x := x0.getD (Vec.zeros n)
  let mut r := Vec.sub b (A.mulVec x)
  let rhat := r
  let mut ρ := 1.0
  let mut α := 1.0
  let mut ω := 1.0
  let mut v := Vec.zeros n
  let mut p := Vec.zeros n
  let mut it := 0
  let mut res := Sparse.vnorm r / nb
  while res > tol && it < maxIter do
    let ρ' := Vec.dot rhat r
    if ρ' == 0 then break
    let β := (ρ' / ρ) * (α / ω)
    -- p = r + β (p - ω v)
    p := Vec.xpby r β (Vec.axpy (-ω) v p)
    let phat := Vec.hadamard p Minv
    v := A.mulVec phat
    let rv := Vec.dot rhat v
    if rv == 0 then break
    α := ρ' / rv
    let s := Vec.axpy (-α) v r
    if Sparse.vnorm s / nb ≤ tol then
      x := Vec.axpy α phat x
      r := s
      res := Sparse.vnorm s / nb
      it := it + 1
      break
    let shat := Vec.hadamard s Minv
    let t := A.mulVec shat
    let tt := Vec.dot t t
    ω := if tt == 0 then 0 else Vec.dot t s / tt
    x := Vec.axpy ω shat (Vec.axpy α phat x)
    r := Vec.axpy (-ω) t s
    ρ := ρ'
    res := Sparse.vnorm r / nb
    it := it + 1
    if ω == 0 then break
  let rr := A.relResidual x b
  return ⟨x, it, rr, rr ≤ tol * 100⟩

namespace Sparse

/-- How `solve` solved a system. -/
inductive Method where
  | denseLU | cholesky | envelopeLU | bicgstab
  deriving Repr, BEq, Inhabited

/-- Julia `A \ b` (see the module note): the solution and the method used. -/
def solveWith (A : Sparse) (b : FloatArray) : FloatArray × Method :=
  let n := A.rows
  let dense (_ : Unit) := (A.toDense.solve b, Method.denseLU)
  if n ≤ 64 then dense ()
  else
    let fallback (_ : Unit) : FloatArray × Method :=
      if n ≤ 3000 then dense ()
      else ((bicgstab A b).x, .bicgstab)
    let viaLU (_ : Unit) : FloatArray × Method :=
      match A.luNoPivot with
      | some F =>
        let x := F.solve b
        if A.relResidual x b ≤ 1e-8 then (x, .envelopeLU) else fallback ()
      | none => fallback ()
    if A.isSymmetric then
      match A.cholesky with
      | some F => (F.solve b, .cholesky)
      | none => viaLU ()
    else viaLU ()

/-- Julia `A \ b` for a square sparse `A`. -/
def solve (A : Sparse) (b : FloatArray) : FloatArray := (A.solveWith b).1

end Sparse

end Cartan.Solve
