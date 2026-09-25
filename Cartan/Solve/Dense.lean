import Grassmann

/-!
# Dense linear algebra: column-major matrices, LU with partial pivoting, Cholesky

The dense half of Julia's `LinearAlgebra` that the spectral and finite-element code needs:
`A \ b` on a `Matrix{Float64}` (LAPACK `getrf`/`getrs`: LU with partial pivoting), `cholesky`
(`potrf`), `inv`, `det`, and the symmetric tridiagonal eigenproblem used by the Lanczos solver
(`Cartan.Solve.Eigen`). Chebyshev differentiation matrices (Cartan `spectral.jl:355-361`) and
their inverses, and small FEM systems, go through here.

**Storage.** `Dense` is `rows × cols` floats in one `FloatArray`, column-major (Julia's
`Matrix{Float64}` layout): entry `(i, j)` (0-based) at `j * rows + i`.

**Algorithms.** `lu` is LAPACK's unblocked right-looking `dgetf2`: in column `k` the pivot is the
first entry of largest magnitude on or below the diagonal (`idamax`), rows are swapped, the
column below the pivot is scaled by `1/pivot` (`dscal` with the reciprocal, as `dgetf2` does when
`|pivot| ≥ sfmin`), and the trailing block gets the rank-1 update (`dger`). LAPACK's `dgetrf` on
larger matrices blocks this (and OpenBLAS reorders the updates), so results agree with Julia to
rounding, not bit for bit; the tests compare with relative tolerances. `cholesky` is the
unblocked `dpotf2` (upper/lower `L Lᵀ`, column by column).

Hot loops (`dot`, `axpy`, the rank-1 update) are tail-recursive over `Nat` indices with Float
accumulators (DESIGN.md §2).
-/

namespace Cartan.Solve

/-- A dense `rows × cols` matrix, column-major (Julia `Matrix{Float64}`). -/
structure Dense where
  /-- Number of rows. -/
  rows : Nat
  /-- Number of columns. -/
  cols : Nat
  /-- The entries, `(i, j)` at `j * rows + i`. -/
  data : FloatArray
  deriving Inhabited

namespace Dense

/-- The `r × c` zero matrix. -/
def zeros (r c : Nat) : Dense := ⟨r, c, ⟨Array.replicate (r * c) 0⟩⟩

/-- Entry `(i, j)` (0-based; `0.0` out of range). -/
@[inline] def get (A : Dense) (i j : Nat) : Float := A.data.get! (j * A.rows + i)

/-- Set entry `(i, j)` (in place when unshared). -/
@[inline] def set (A : Dense) (i j : Nat) (x : Float) : Dense :=
  { A with data := A.data.set! (j * A.rows + i) x }

/-- The matrix with entries `f i j`. -/
def ofFn (r c : Nat) (f : Nat → Nat → Float) : Dense := Id.run do
  let mut a := FloatArray.emptyWithCapacity (r * c)
  for j in [0:c] do
    for i in [0:r] do
      a := a.push (f i j)
  return ⟨r, c, a⟩

/-- The `n × n` identity. -/
def identity (n : Nat) : Dense := ofFn n n fun i j => if i == j then 1 else 0

/-- From rows given as arrays (Julia's matrix literal `[a b; c d]`). -/
def ofRows (rows : Array (Array Float)) : Dense :=
  let r := rows.size
  let c := (rows[0]?.map (·.size)).getD 0
  ofFn r c fun i j => (rows[i]!)[j]!

/-- The rows as arrays (for display and tests). -/
def toRows (A : Dense) : Array (Array Float) :=
  (Array.range A.rows).map fun i => (Array.range A.cols).map fun j => A.get i j

/-- Julia `transpose(A)` / `A'` (real). -/
def transpose (A : Dense) : Dense := ofFn A.cols A.rows fun i j => A.get j i

/-- `A * B`. -/
def mul (A B : Dense) : Dense :=
  ofFn A.rows B.cols fun i j => go A B i j 0 0 A.cols
where
  /-- `Σ_{k ≥ k₀} A[i,k] B[k,j]` (the first `r` terms). -/
  go (A B : Dense) (i j : Nat) (k : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => go A B i j (k + 1) (s + A.get i k * B.get k j) r

/-- `A * x`. -/
def mulVec (A : Dense) (x : FloatArray) : FloatArray := Id.run do
  let mut y := FloatArray.emptyWithCapacity A.rows
  for i in [0:A.rows] do
    y := y.push (rowDot A x i 0 0 A.cols)
  return y
where
  /-- `Σ_k A[i,k] x[k]`. -/
  rowDot (A : Dense) (x : FloatArray) (i k : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => rowDot A x i (k + 1) (s + A.get i k * x.get! k) r

/-- `A + B` (entrywise). -/
def add (A B : Dense) : Dense :=
  ⟨A.rows, A.cols, ⟨(Array.range A.data.size).map fun k => A.data.get! k + B.data.get! k⟩⟩

/-- `s * A`. -/
def scale (s : Float) (A : Dense) : Dense :=
  ⟨A.rows, A.cols, ⟨(Array.range A.data.size).map fun k => s * A.data.get! k⟩⟩

/-! ## LU with partial pivoting (LAPACK `dgetf2`) -/

/-- An LU factorization `P A = L U` (Julia `lu(A)`): the combined factors in one matrix (`L`
strictly below the diagonal with a unit diagonal, `U` on and above), the pivot rows `piv`
(LAPACK `ipiv`, 0-based: row `k` was swapped with row `piv[k]`), and `info` (`0`, or `k + 1` if
`U[k,k]` is exactly zero: singular). -/
structure LU where
  /-- The factors. -/
  f : Dense
  /-- Row interchanges. -/
  piv : Array Nat
  /-- `0` or the 1-based index of the first zero pivot. -/
  info : Nat
  deriving Inhabited

/-- The first index of the largest `|A[i,k]|` for `i ∈ [k, n)` (LAPACK `idamax`). -/
def pivotRow (A : Dense) (k : Nat) : Nat :=
  go (k + 1) k (A.get k k).abs (A.rows - k - 1)
where
  /-- Scan the rest of the column. -/
  go (i best : Nat) (bv : Float) : Nat → Nat
    | 0 => best
    | r + 1 =>
      let v := (A.get i k).abs
      if v > bv then go (i + 1) i v r else go (i + 1) best bv r

/-- Swap rows `a` and `b` of the whole matrix. -/
def swapRows (A : Dense) (a b : Nat) : Dense := Id.run do
  if a == b then return A
  let mut d := A.data
  for j in [0:A.cols] do
    let ia := j * A.rows + a
    let ib := j * A.rows + b
    let x := d.get! ia
    let y := d.get! ib
    d := (d.set! ia y).set! ib x
  return { A with data := d }

/-- `dgetf2` (see the module note). -/
def lu (A0 : Dense) : LU := Id.run do
  let n := min A0.rows A0.cols
  let m := A0.rows
  let mut A := A0
  let mut piv : Array Nat := #[]
  let mut info := 0
  for k in [0:n] do
    let p := pivotRow A k
    piv := piv.push p
    A := swapRows A k p
    let akk := A.get k k
    if akk != 0 then
      let r := 1 / akk
      let mut d := A.data
      for i in [k + 1:m] do
        let idx := k * m + i
        d := d.set! idx (d.get! idx * r)
      -- rank-1 update of the trailing block, column by column (`dger`)
      for j in [k + 1:A0.cols] do
        let ukj := d.get! (j * m + k)
        if ukj != 0 then
          d := axpyCol d (j * m) (k * m) (k + 1) (m - k - 1) (-ukj)
      A := { A with data := d }
    else if info == 0 then
      info := k + 1
  return ⟨A, piv, info⟩
where
  /-- `d[cj + i] += s · d[ck + i]` for `i ∈ [i₀, i₀ + r)`. -/
  axpyCol (d : FloatArray) (cj ck i : Nat) : Nat → Float → FloatArray
    | 0, _ => d
    | r + 1, s => axpyCol (d.set! (cj + i) (d.get! (cj + i) + s * d.get! (ck + i))) cj ck (i + 1) r s

/-- Solve `A x = b` from `P A = L U` (LAPACK `getrs`): apply the interchanges, then `L y = P b`
(unit lower) and `U x = y`. -/
def LU.solve (F : LU) (b : FloatArray) : FloatArray := Id.run do
  let n := F.f.rows
  let m := F.f.rows
  let mut x := b
  for k in [0:F.piv.size] do
    let p := F.piv[k]!
    if p != k then
      let t := x.get! k
      x := (x.set! k (x.get! p)).set! p t
  -- forward: L y = P b
  for j in [0:n] do
    let xj := x.get! j
    if xj != 0 then
      for i in [j + 1:n] do
        x := x.set! i (x.get! i - xj * F.f.data.get! (j * m + i))
  -- backward: U x = y (column-oriented, as `dtrsv`)
  for jj in [0:n] do
    let j := n - 1 - jj
    let xj := x.get! j / F.f.data.get! (j * m + j)
    x := x.set! j xj
    if xj != 0 then
      for i in [0:j] do
        x := x.set! i (x.get! i - xj * F.f.data.get! (j * m + i))
  return x

/-- Julia `A \ b` for a square dense `A` (LU with partial pivoting). -/
def solve (A : Dense) (b : FloatArray) : FloatArray := (lu A).solve b

/-- Julia `A \ B` for several right-hand sides (the columns of `B`). -/
def solveMat (A : Dense) (B : Dense) : Dense :=
  let F := lu A
  let cols := (Array.range B.cols).map fun j =>
    F.solve ⟨(Array.range B.rows).map fun i => B.get i j⟩
  ofFn B.rows B.cols fun i j => cols[j]!.get! i

/-- Julia `inv(A)`. -/
def inv (A : Dense) : Dense := solveMat A (identity A.rows)

/-- Julia `det(A)` via LU: the product of the pivots, negated per interchange. -/
def det (A : Dense) : Float :=
  let F := lu A
  let n := F.f.rows
  let sgn := (List.range F.piv.size).foldl (fun s k => if F.piv[k]! != k then -s else s) (1 : Float)
  (List.range n).foldl (fun p k => p * F.f.get k k) sgn

/-! ## Cholesky (LAPACK `dpotf2`, lower) -/

/-- The lower Cholesky factor `L` with `A = L Lᵀ` of a symmetric positive definite matrix
(Julia `cholesky(A).L`); `none` when a pivot is not positive (Julia `PosDefException`). -/
def cholesky (A : Dense) : Option Dense := Id.run do
  let n := A.rows
  let mut L := zeros n n
  for j in [0:n] do
    let s := sumSq L j 0 0 j
    let d := A.get j j - s
    if !(d > 0) then return none
    let ljj := Float.sqrt d
    L := L.set j j ljj
    for i in [j + 1:n] do
      let t := A.get i j - cross L i j 0 0 j
      L := L.set i j (t / ljj)
  return some L
where
  /-- `Σ_{k<r} L[j,k]²`. -/
  sumSq (L : Dense) (j k : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => let x := L.get j k; sumSq L j (k + 1) (s + x * x) r
  /-- `Σ_{k<r} L[i,k] L[j,k]`. -/
  cross (L : Dense) (i j k : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => cross L i j (k + 1) (s + L.get i k * L.get j k) r

/-- Solve `L y = b` (lower triangular). -/
def forwardSub (L : Dense) (b : FloatArray) : FloatArray := Id.run do
  let n := L.rows
  let mut y := b
  for i in [0:n] do
    let s := dotRow L y i 0 0 i
    y := y.set! i ((y.get! i - s) / L.get i i)
  return y
where
  /-- `Σ_{k<r} L[i,k] y[k]`. -/
  dotRow (L : Dense) (y : FloatArray) (i k : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => dotRow L y i (k + 1) (s + L.get i k * y.get! k) r

/-- Solve `Lᵀ x = y` (`L` lower triangular). -/
def backSubT (L : Dense) (y : FloatArray) : FloatArray := Id.run do
  let n := L.rows
  let mut x := y
  for ii in [0:n] do
    let i := n - 1 - ii
    let s := dotCol L x i (i + 1) 0 (n - i - 1)
    x := x.set! i ((x.get! i - s) / L.get i i)
  return x
where
  /-- `Σ_{k>i} L[k,i] x[k]`. -/
  dotCol (L : Dense) (x : FloatArray) (i k : Nat) (s : Float) : Nat → Float
    | 0 => s
    | r + 1 => dotCol L x i (k + 1) (s + L.get k i * x.get! k) r

/-! ## Symmetric tridiagonal eigenproblem (implicit QL, EISPACK `tql2`) -/

/-- Eigenvalues (ascending) and orthonormal eigenvectors (the columns of `z`, `n × n`) of the
symmetric tridiagonal matrix with diagonal `d` and off-diagonal `e` (`e[i]` couples `i, i+1`),
by the implicit QL iteration with Wilkinson shifts (EISPACK `tql2`, Numerical Recipes `tqli`);
`none` if an eigenvalue fails to converge in 60 iterations. -/
def tridiagEigen (d0 e0 : FloatArray) : Option (FloatArray × Dense) := Id.run do
  let n := d0.size
  let mut d := d0
  let mut e := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    e := e.push (if i + 1 < n then e0.get! i else 0)
  let mut z := identity n
  for l in [0:n] do
    let mut iter := 0
    let mut done := false
    while !done do
      -- find a small subdiagonal element
      let mut mm := l
      while mm + 1 < n do
        let dd := (d.get! mm).abs + (d.get! (mm + 1)).abs
        if (e.get! mm).abs ≤ 2.220446049250313e-16 * dd then break
        mm := mm + 1
      if mm == l then
        done := true
      else
        if iter == 60 then return none
        iter := iter + 1
        let mut g := (d.get! (l + 1) - d.get! l) / (2 * e.get! l)
        let mut r := Float.sqrt (g * g + 1)
        g := d.get! mm - d.get! l + e.get! l / (g + (if g ≥ 0 then r.abs else -r.abs))
        let mut s := 1.0
        let mut c := 1.0
        let mut p := 0.0
        let mut i := mm
        let mut underflow := false
        while i > l do
          i := i - 1
          let f := s * e.get! i
          let b := c * e.get! i
          r := Float.sqrt (f * f + g * g)
          e := e.set! (i + 1) r
          if r == 0 then
            d := d.set! (i + 1) (d.get! (i + 1) - p)
            e := e.set! mm 0
            underflow := true
            break
          s := f / r
          c := g / r
          let gg := d.get! (i + 1) - p
          r := (d.get! i - gg) * s + 2 * c * b
          p := s * r
          d := d.set! (i + 1) (gg + p)
          g := c * r - b
          -- rotate the eigenvectors
          let mut zd := z.data
          for k in [0:n] do
            let ik1 := (i + 1) * n + k
            let ik := i * n + k
            let fz := zd.get! ik1
            let zik := zd.get! ik
            zd := (zd.set! ik1 (s * zik + c * fz)).set! ik (c * zik - s * fz)
          z := { z with data := zd }
        if !underflow then
          d := d.set! l (d.get! l - p)
          e := (e.set! l g).set! mm 0
  -- sort ascending (selection sort, moving the vectors along)
  for i in [0:n] do
    let mut k := i
    let mut p := d.get! i
    for j in [i + 1:n] do
      if d.get! j < p then
        k := j
        p := d.get! j
    if k != i then
      d := (d.set! k (d.get! i)).set! i p
      let mut zd := z.data
      for r in [0:n] do
        let a := zd.get! (i * n + r)
        zd := (zd.set! (i * n + r) (zd.get! (k * n + r))).set! (k * n + r) a
      z := { z with data := zd }
  return some (d, z)

end Dense

end Cartan.Solve
