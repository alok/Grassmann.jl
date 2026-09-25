import Tests.Cartan.Common
import Cartan.Solve

/-!
# Sparse and dense solvers (`oracle/golden/cartan/element/solve.json`)

Generator `oracle/cartan/element/solve.jl` (Julia SparseArrays/LinearAlgebra): triplet assembly
and products bit for bit; direct sparse solves of a 2-D Laplacian (Cholesky) and an upwind
convection–diffusion matrix (envelope LU) to `1e-10`; dense LU factors, `\`, `det`, `inv`,
Cholesky and symmetric eigenvalues to `1e-12`; the smallest eigenvalues of the 1-D P1 pencil
(stiffness, consistent mass) and of a 2-D pencil with a variable lumped mass to `1e-9`, by
shift-invert Lanczos and by the dense generalized solver.
-/

open Lean Tests.Small Cartan JuliaBase Cartan.Solve

namespace Tests.CartanTests.SolveTests

/-- The SplitMix64 stream of `oracle/cartan/element/common.jl` (`randfloats`). -/
def randFloats (n : Nat) (seed : UInt64) (lo hi : Float) : FloatArray := Id.run do
  let mut s := seed
  let mut out := FloatArray.emptyWithCapacity n
  for _ in [0:n] do
    s := s + 0x9e3779b97f4a7c15
    let mut z := s
    z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
    z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
    z := z ^^^ (z >>> 31)
    out := out.push (lo + (hi - lo) * ((z >>> 11).toFloat * Float.ofBits 0x3CA0000000000000))
  return out

/-- The 5-point Laplacian of `oracle/cartan/element/solve.jl` (`lap2d`). -/
def lap2d (n : Nat) (conv : Float := 0) : Sparse := Id.run do
  let h := 1 / Float.ofNat (n + 1)
  let mut I := #[]
  let mut J := #[]
  let mut V : FloatArray := .empty
  for j in [0:n] do
    for i in [0:n] do
      let k := i + n * j
      I := I.push k; J := J.push k; V := V.push (4.0 + conv * h)
      if i > 0 then I := I.push k; J := J.push (k - 1); V := V.push (-1.0 - conv * h)
      if i + 1 < n then I := I.push k; J := J.push (k + 1); V := V.push (-1.0)
      if j > 0 then I := I.push k; J := J.push (k - n); V := V.push (-1.0)
      if j + 1 < n then I := I.push k; J := J.push (k + n); V := V.push (-1.0)
  return Sparse.ofTriplets (n * n) (n * n) I J V

/-- Compare to a relative tolerance (scaled by the largest expected entry). -/
def checkRel (label : String) (got want : FloatArray) (rtol : Float) : TestM Unit := do
  if got.size != want.size then
    check label false fun _ => s!"length {got.size}, expected {want.size}"
    return
  let scale := want.data.foldl (fun m x => F64.max m x.abs) 0
  let bad := (List.range got.size).find? fun i => !((got[i]! - want[i]!).abs ≤ rtol * scale)
  match bad with
  | none => check label true
  | some i => check label false fun _ => s!"[{i}] got {fmt got[i]!}, expected {fmt want[i]!}"

/-- Compare a golden CSC matrix exactly. -/
def checkCSC (label : String) (A : Sparse) (j : Json) : TestM Unit := do
  let cp ← jNats (← jField j "colptr")
  let rv ← jNats (← jField j "rowval")
  check s!"{label} colptr" (A.colPtr == cp) fun _ => s!"{A.colPtr} vs {cp}"
  check s!"{label} rowval" (A.rowIdx == rv) fun _ => s!"{A.rowIdx} vs {rv}"
  checkFloats s!"{label} nzval" A.vals (← gFloats (← jField j "nzval"))

/-- Run the checks. -/
def run : TestM Unit := do
  let g ← load "element/solve"
  -- 1. assembly
  let t ← jField g "triplets"
  let I ← jNats (← jField t "I")
  let J ← jNats (← jField t "J")
  let V ← gFloats (← jField t "V")
  let A := Sparse.ofTriplets 4 4 I J V
  checkCSC "solve sparse(I,J,V)" A (← jField t "A")
  checkFloats "solve A*x" (A.mulVec ⟨#[1, -2, 0.5, 3]⟩) (← gFloats (← jField t "Ax"))
  checkCSC "solve transpose" A.transpose (← jField t "At")
  -- 2. sparse direct solves
  let l ← jField g "lap2d"
  let n ← jNat (← jField l "n")
  let L := lap2d n
  let b ← gFloats (← jField l "b")
  let (x, meth) := L.solveWith b
  check "solve lap2d method" (meth == .cholesky) fun _ => s!"{repr meth}"
  checkRel "solve lap2d \\" x (← gFloats (← jField l "x")) 1e-10
  check "solve lap2d nnz" (L.nnz == (← jNat (← jField l "nnz")))
  check "solve lap2d rcm bandwidth" ((L.permute (Sparse.rcm L)).bandwidth ≤ n + 1) fun _ =>
    s!"{(L.permute (Sparse.rcm L)).bandwidth}"
  let cg := cg L b
  checkRel "solve lap2d cg" cg.x (← gFloats (← jField l "x")) 1e-9
  let c ← jField g "conv2d"
  let C := lap2d n 20
  let (xc, mc) := C.solveWith b
  check "solve conv2d method" (mc == .envelopeLU) fun _ => s!"{repr mc}"
  checkRel "solve conv2d \\" xc (← gFloats (← jField c "x")) 1e-10
  let bi := bicgstab C b
  checkRel "solve conv2d bicgstab" bi.x (← gFloats (← jField c "x")) 1e-8
  -- 3. dense
  let d ← jField g "dense"
  let m ← jNat (← jField d "n")
  let Ad : Dense := ⟨m, m, ← gFloats (← jField d "A")⟩
  let F := Ad.lu
  let Lf := Dense.ofFn m m fun i j => if i == j then 1 else if i > j then F.f.get i j else 0
  let Uf := Dense.ofFn m m fun i j => if i ≤ j then F.f.get i j else 0
  checkRel "solve lu L" Lf.data (← gFloats (← jField d "L")) 1e-13
  checkRel "solve lu U" Uf.data (← gFloats (← jField d "U")) 1e-13
  let p := F.piv.size.fold (init := Array.range m) fun k _ acc => acc.swapIfInBounds k F.piv[k]!
  check "solve lu p" (p == (← jNats (← jField d "p"))) fun _ => s!"{p}"
  let bd ← gFloats (← jField d "b")
  checkRel "solve dense \\" (Ad.solve bd) (← gFloats (← jField d "x")) 1e-12
  let dt ← gFloat (← jField d "det")
  check "solve det" ((Ad.det - dt).abs ≤ 1e-12 * dt.abs) fun _ => s!"{Ad.det} vs {dt}"
  checkRel "solve inv" Ad.inv.data (← gFloats (← jField d "inv")) 1e-12
  let S := (Ad.mul Ad.transpose).add (Dense.scale (Float.ofNat m) (Dense.identity m))
  match S.cholesky with
  | some Lc => checkRel "solve cholesky" Lc.data (← gFloats (← jField d "chol")) 1e-13
  | none => check "solve cholesky" false
  checkRel "solve symeig" S.symEigen.1 (← gFloats (← jField d "symeig")) 1e-13
  -- 4. generalized eigenproblems
  let e1 ← jField g "geneig1d"
  let N ← jNat (← jField e1 "N")
  let h := 1 / Float.ofNat (N + 1)
  let tri (a b : Float) : Sparse := Id.run do
    let mut I := #[]
    let mut J := #[]
    let mut V : FloatArray := .empty
    for i in [0:N] do
      I := I.push i; J := J.push i; V := V.push a
      if i + 1 < N then
        I := (I.push i).push (i + 1); J := (J.push (i + 1)).push i; V := (V.push b).push b
    return Sparse.ofTriplets N N I J V
  let K := tri (2 / h) (-1 / h)
  let Mm := tri (4 * h / 6) (h / 6)
  let want1 ← gFloats (← jField e1 "vals")
  match K.geneigsolve Mm 8 with
  | some r =>
    checkRel "solve geneigsolve 1d" r.vals want1 1e-9
    check "solve geneigsolve 1d residual" (r.residual ≤ 1e-8) fun _ => s!"{r.residual}"
  | none => check "solve geneigsolve 1d" false
  match K.toDense.genEigen Mm.toDense with
  | some (vals, _) => checkRel "solve genEigen 1d" ⟨(vals.data.extract 0 8)⟩ want1 1e-10
  | none => check "solve genEigen 1d" false
  let e2 ← jField g "geneig2d"
  let n2 ← jNat (← jField e2 "n")
  let A2 := lap2d n2
  let M2 := Sparse.diagm ⟨(Array.range (n2 * n2)).map fun k =>
    1 + Float.ofNat (k % n2 + 1) / Float.ofNat (n2 + 1)⟩
  let want2 ← gFloats (← jField e2 "vals")
  match A2.geneigsolve M2 6 with
  | some r => checkRel "solve geneigsolve 2d" r.vals want2 1e-9
  | none => check "solve geneigsolve 2d" false

end Tests.CartanTests.SolveTests
