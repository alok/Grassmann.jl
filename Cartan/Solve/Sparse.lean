import Cartan.Solve.Dense

/-!
# Sparse matrices (CSC) and direct solvers

Julia's `SparseMatrixCSC{Float64,Int}` for finite-element assembly (Adapode `assemble*`, Cartan
`element.jl`: `sparse(t)`, `adjacency`, `incidence`): compressed sparse columns, built from
triplets with duplicates summed, and `A \ b`.

**Construction.** `ofTriplets m n I J V` is Julia `sparse(I, J, V, m, n)` (0-based indices here):
entries are sorted by column, rows ascending within a column, and duplicates are summed in their
input order, `((v₁ + v₂) + v₃)`, which is the order of SparseArrays' `sparse!` (a counting sort
into rows that combines repeated columns as it meets them, then a transpose). Structural zeros are
kept (Julia drops nothing either). `mulVec` accumulates column by column like Julia's
`mul!(y, A, x)`, so assembly and products agree with Julia bit for bit.

**Direct solves.** Julia calls CHOLMOD (symmetric positive definite) or UMFPACK (general); here:
* a fill-reducing **reverse Cuthill–McKee** ordering of the symmetrized pattern (a BFS from a
  pseudo-peripheral node, neighbours by increasing degree), which makes finite-element matrices
  banded;
* an **envelope (profile) Cholesky** `P A Pᵀ = L Lᵀ` for symmetric positive definite matrices
  (row-oriented bordering: row `i` of `L` spans its first structural nonzero to the diagonal);
* an **envelope LU without pivoting** for general matrices with a symmetric pattern (FEM
  convection, SUPG), which fails over to dense LU with partial pivoting (small systems) or to
  preconditioned BiCGSTAB (`Cartan.Solve.Iterative`) when a pivot is tiny.
The solutions agree with Julia's to rounding (the tests compare relative residuals and
solutions with tolerances, never bits: CHOLMOD/UMFPACK use supernodal kernels and their own
orderings).
-/

namespace Cartan.Solve

/-- Julia `SparseMatrixCSC{Float64,Int}` (0-based): column `j` holds the entries
`colPtr[j] … colPtr[j+1]-1` of `rowIdx`/`vals`, rows ascending. -/
structure Sparse where
  /-- Number of rows. -/
  rows : Nat
  /-- Number of columns. -/
  cols : Nat
  /-- Column starts (`cols + 1` entries). -/
  colPtr : Array Nat
  /-- Row of each stored entry. -/
  rowIdx : Array Nat
  /-- Value of each stored entry. -/
  vals : FloatArray
  deriving Inhabited

namespace Sparse

/-- Number of stored entries (Julia `nnz`). -/
@[inline] def nnz (A : Sparse) : Nat := A.vals.size

/-- The `m × n` matrix with no stored entries (Julia `spzeros(m, n)`). -/
def zeros (m n : Nat) : Sparse := ⟨m, n, Array.replicate (n + 1) 0, #[], .empty⟩

/-- Julia `sparse(I, J, V, m, n)` (0-based `I`, `J`; see the module note). Triplets outside the
`m × n` range are dropped. -/
def ofTriplets (m n : Nat) (I J : Array Nat) (V : FloatArray) : Sparse := Id.run do
  let t := min I.size (min J.size V.size)
  -- keep the in-range triplets, in input order
  let mut keep : Array Nat := #[]
  for k in [0:t] do
    if I[k]! < m && J[k]! < n then keep := keep.push k
  -- stable counting sort by row, then stable counting sort by column: (col, row, input order)
  let byRow := countingSort keep (fun k => I[k]!) m
  let byCol := countingSort byRow (fun k => J[k]!) n
  -- merge duplicates (same column and row are now adjacent, in input order)
  let mut colPtr : Array Nat := Array.replicate (n + 1) 0
  let mut rowIdx : Array Nat := #[]
  let mut vals : FloatArray := .empty
  let mut lastCol := n
  let mut lastRow := m
  for k in byCol do
    let r := I[k]!
    let c := J[k]!
    let v := V.get! k
    if c == lastCol && r == lastRow then
      let q := vals.size - 1
      vals := vals.set! q (vals.get! q + v)
    else
      rowIdx := rowIdx.push r
      vals := vals.push v
      colPtr := colPtr.set! (c + 1) (colPtr[c + 1]! + 1)
      lastCol := c
      lastRow := r
  for j in [0:n] do
    colPtr := colPtr.set! (j + 1) (colPtr[j + 1]! + colPtr[j]!)
  return ⟨m, n, colPtr, rowIdx, vals⟩
where
  /-- Stable counting sort of `ks` by `key` (values `< b`). -/
  countingSort (ks : Array Nat) (key : Nat → Nat) (b : Nat) : Array Nat := Id.run do
    let mut cnt : Array Nat := Array.replicate (b + 1) 0
    for k in ks do
      let x := key k
      cnt := cnt.set! (x + 1) (cnt[x + 1]! + 1)
    for i in [0:b] do
      cnt := cnt.set! (i + 1) (cnt[i + 1]! + cnt[i]!)
    let mut out : Array Nat := Array.replicate ks.size 0
    for k in ks do
      let x := key k
      out := out.set! cnt[x]! k
      cnt := cnt.set! x (cnt[x]! + 1)
    return out

/-- Entry `(i, j)` (`0.0` when not stored). -/
def get (A : Sparse) (i j : Nat) : Float := Id.run do
  if j ≥ A.cols then return 0
  for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
    if A.rowIdx[k]! == i then return A.vals.get! k
  return 0

/-- The stored triplets `(row, col, value)` in storage order. -/
def triplets (A : Sparse) : Array (Nat × Nat × Float) := Id.run do
  let mut out := #[]
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      out := out.push (A.rowIdx[k]!, j, A.vals.get! k)
  return out

/-- Julia `Matrix(A)`. -/
def toDense (A : Sparse) : Dense := Id.run do
  let mut D := Dense.zeros A.rows A.cols
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      D := D.set A.rowIdx[k]! j (A.vals.get! k)
  return D

/-- Julia `sparse(D)` of a dense matrix (entries equal to `0.0` are not stored). -/
def ofDense (D : Dense) : Sparse := Id.run do
  let mut I := #[]
  let mut J := #[]
  let mut V : FloatArray := .empty
  for j in [0:D.cols] do
    for i in [0:D.rows] do
      let x := D.get i j
      if x != 0 then
        I := I.push i; J := J.push j; V := V.push x
  return ofTriplets D.rows D.cols I J V

/-- `y += A x` column by column with fused multiply-adds (Julia `mul!(y, A, x, 1, 1)`:
`C[i] = muladd(nzv[k], x[j], C[i])`, `SparseArrays/src/linalg.jl:174`, an `fmadd` on aarch64). -/
def mulVecAdd (A : Sparse) (x y : FloatArray) : FloatArray := Id.run do
  let mut y := y
  for j in [0:A.cols] do
    let xj := x.get! j
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let i := A.rowIdx[k]!
      y := y.set! i (Float.fma (A.vals.get! k) xj (y.get! i))
  return y

/-- Julia `A * x`. -/
def mulVec (A : Sparse) (x : FloatArray) : FloatArray :=
  A.mulVecAdd x ⟨Array.replicate A.rows 0⟩

/-- Julia `transpose(A)` (materialized, rows ascending in each column). -/
def transpose (A : Sparse) : Sparse := Id.run do
  let mut I := #[]
  let mut J := #[]
  let mut V : FloatArray := .empty
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      I := I.push j; J := J.push A.rowIdx[k]!; V := V.push (A.vals.get! k)
  return ofTriplets A.cols A.rows I J V

/-- `a A + b B` (Julia `a*A + b*B`; the union of the patterns). -/
def lincomb (a : Float) (A : Sparse) (b : Float) (B : Sparse) : Sparse := Id.run do
  let mut I := #[]
  let mut J := #[]
  let mut V : FloatArray := .empty
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      I := I.push A.rowIdx[k]!; J := J.push j; V := V.push (a * A.vals.get! k)
  for j in [0:B.cols] do
    for k in [B.colPtr[j]!:B.colPtr[j + 1]!] do
      I := I.push B.rowIdx[k]!; J := J.push j; V := V.push (b * B.vals.get! k)
  return ofTriplets (max A.rows B.rows) (max A.cols B.cols) I J V

instance : Add Sparse := ⟨fun A B => lincomb 1 A 1 B⟩
instance : Sub Sparse := ⟨fun A B => lincomb 1 A (-1) B⟩
instance : HMul Float Sparse Sparse := ⟨fun s A => { A with vals := ⟨A.vals.data.map (s * ·)⟩ }⟩

/-- Julia `spdiagm(0 => d)`. -/
def diagm (d : FloatArray) : Sparse :=
  let n := d.size
  ofTriplets n n (Array.range n) (Array.range n) d

/-- Julia `diag(A)`. -/
def diag (A : Sparse) : FloatArray := ⟨(Array.range (min A.rows A.cols)).map fun i => A.get i i⟩

/-- Whether the stored pattern and values are symmetric (`A == transpose(A)`). -/
def isSymmetric (A : Sparse) : Bool :=
  A.rows == A.cols &&
    (let T := A.transpose
     T.colPtr == A.colPtr && T.rowIdx == A.rowIdx && T.vals.data == A.vals.data)

/-! ## Orderings -/

/-- The neighbours of every node in the symmetrized pattern of a square matrix (diagonal
excluded), ascending. -/
def adjacencyLists (A : Sparse) : Array (Array Nat) := Id.run do
  let n := A.rows
  let mut adj : Array (Array Nat) := Array.replicate n #[]
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let i := A.rowIdx[k]!
      if i != j then
        adj := adj.modify i (·.push j)
        adj := adj.modify j (·.push i)
  return adj.map fun a => (a.qsort (· < ·)).toList.eraseDups.toArray

/-- A BFS from `s` over the unvisited nodes: the visit order (neighbours by increasing
degree) and the last level. -/
def bfsLevels (adj : Array (Array Nat)) (deg : Array Nat) (s : Nat) (visited : Array Bool) :
    Array Nat × Array Nat × Array Bool := Id.run do
  let mut vis := visited.set! s true
  let mut order := #[s]
  let mut level := #[s]
  let mut last := #[s]
  while !level.isEmpty do
    let mut next := #[]
    for v in level do
      let ns := (adj[v]!.filter fun w => !vis[w]!).qsort fun a b => deg[a]! < deg[b]! || (deg[a]! == deg[b]! && a < b)
      for w in ns do
        if !vis[w]! then
          vis := vis.set! w true
          next := next.push w
          order := order.push w
    if !next.isEmpty then last := next
    level := next
  return (order, last, vis)

/-- Reverse Cuthill–McKee ordering of a square matrix's symmetrized pattern: `perm[k]` is the
old index of the node placed at position `k`. Each connected component starts from a
pseudo-peripheral node (repeated BFS from a minimum-degree node of the last level). -/
def rcm (A : Sparse) : Array Nat := Id.run do
  let n := A.rows
  let adj := adjacencyLists A
  let deg := adj.map (·.size)
  let mut visited := Array.replicate n false
  let mut order : Array Nat := #[]
  for s0 in [0:n] do
    if !visited[s0]! then
      -- pseudo-peripheral start
      let mut s := s0
      let mut ecc := 0
      for _ in [0:8] do
        let (o, last, _) := bfsLevels adj deg s visited
        let e := o.size
        let cand := last.foldl (fun b v => if deg[v]! < deg[b]! then v else b) last[0]!
        if cand == s || (ecc > 0 && e ≤ ecc) then break
        ecc := e
        s := cand
      let (o, _, vis) := bfsLevels adj deg s visited
      visited := vis
      order := order ++ o
  return order.reverse

/-- The inverse of a permutation (`inv[perm[k]] = k`). -/
def invPerm (perm : Array Nat) : Array Nat := Id.run do
  let mut inv := Array.replicate perm.size 0
  for k in [0:perm.size] do
    inv := inv.set! perm[k]! k
  return inv

/-- `P A Pᵀ` for `perm` (row/column `perm[k]` of `A` becomes `k`). -/
def permute (A : Sparse) (perm : Array Nat) : Sparse := Id.run do
  let inv := invPerm perm
  let mut I := #[]
  let mut J := #[]
  let mut V : FloatArray := .empty
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      I := I.push inv[A.rowIdx[k]!]!; J := J.push inv[j]!; V := V.push (A.vals.get! k)
  return ofTriplets A.rows A.cols I J V

/-- The bandwidth `max |i - j|` over the stored entries. -/
def bandwidth (A : Sparse) : Nat := Id.run do
  let mut b := 0
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let i := A.rowIdx[k]!
      b := max b (if i > j then i - j else j - i)
  return b

end Sparse

/-! ## Envelope factorizations -/

/-- A profile (envelope) matrix: row `i` stores the entries `first[i] … i` of its lower part
(`lower`, offsets `lstart`), column `i` the entries `first[i] … i` of its upper part (`upper`,
offsets `ustart`; unused for Cholesky). -/
structure Envelope where
  /-- Size. -/
  n : Nat
  /-- First structural nonzero of row/column `i` (symmetrized). -/
  first : Array Nat
  /-- Offset of row `i` in `lower` (`n + 1` entries). -/
  lstart : Array Nat
  /-- Lower rows (`L[i, first[i] … i]`). -/
  lower : FloatArray
  /-- Upper columns (`U[first[j] … j, j]`). -/
  upper : FloatArray
  deriving Inhabited

namespace Envelope

/-- `L[i, j]` for `first[i] ≤ j ≤ i`. -/
@[inline] def lget (E : Envelope) (i j : Nat) : Float := E.lower.get! (E.lstart[i]! + (j - E.first[i]!))

/-- `U[i, j]` for `first[j] ≤ i ≤ j`. -/
@[inline] def uget (E : Envelope) (i j : Nat) : Float := E.upper.get! (E.lstart[j]! + (i - E.first[j]!))

/-- The envelope of a square matrix (already permuted), with the lower triangle scattered into
`lower` and the upper triangle into `upper`. -/
def ofSparse (A : Sparse) : Envelope := Id.run do
  let n := A.rows
  let mut first := Array.range n
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let i := A.rowIdx[k]!
      if i > j then first := first.set! i (min first[i]! j)
      else if j > i then first := first.set! j (min first[j]! i)
  let mut lstart := Array.replicate (n + 1) 0
  for i in [0:n] do
    lstart := lstart.set! (i + 1) (lstart[i]! + (i - first[i]! + 1))
  let total := lstart[n]!
  let mut lower : FloatArray := ⟨Array.replicate total 0⟩
  let mut upper : FloatArray := ⟨Array.replicate total 0⟩
  for j in [0:A.cols] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      let i := A.rowIdx[k]!
      let v := A.vals.get! k
      if i ≥ j then
        let q := lstart[i]! + (j - first[i]!)
        lower := lower.set! q (lower.get! q + v)
      if i ≤ j then
        let q := lstart[j]! + (i - first[j]!)
        upper := upper.set! q (upper.get! q + v)
  return ⟨n, first, lstart, lower, upper⟩

/-- `Σ_{k ∈ [lo, hi)} x[a₀ + k - fa] y[b₀ + k - fb]` over two envelope rows (the shared part of
row `i` and row/column `j`). -/
def rowDot (x y : FloatArray) (ax ay : Nat) (k : Nat) (s : Float) : Nat → Float
  | 0 => s
  | r + 1 => rowDot x y ax ay (k + 1) (s + x.get! (ax + k) * y.get! (ay + k)) r

/-- In-place envelope Cholesky of the lower part (`L Lᵀ`); `none` at a non-positive pivot. -/
def cholesky (E0 : Envelope) : Option Envelope := Id.run do
  let mut E := E0
  for i in [0:E.n] do
    let fi := E.first[i]!
    let si := E.lstart[i]!
    for j in [fi:i] do
      let fj := E.first[j]!
      let sj := E.lstart[j]!
      let lo := max fi fj
      let s := rowDot E.lower E.lower (si + lo - fi) (sj + lo - fj) 0 0 (j - lo)
      let q := si + (j - fi)
      E := { E with lower := E.lower.set! q ((E.lower.get! q - s) / E.lower.get! (sj + (j - fj))) }
    let s := rowDot E.lower E.lower si si 0 0 (i - fi)
    let q := si + (i - fi)
    let d := E.lower.get! q - s
    if !(d > 0) then return none
    E := { E with lower := E.lower.set! q (Float.sqrt d) }
  return some E

/-- Solve `L Lᵀ x = b` with a Cholesky envelope. -/
def cholSolve (E : Envelope) (b : FloatArray) : FloatArray := Id.run do
  let n := E.n
  let mut y := b
  for i in [0:n] do
    let fi := E.first[i]!
    let si := E.lstart[i]!
    let s := rowDot E.lower y si fi 0 0 (i - fi)
    y := y.set! i ((y.get! i - s) / E.lower.get! (si + (i - fi)))
  for ii in [0:n] do
    let i := n - 1 - ii
    let fi := E.first[i]!
    let si := E.lstart[i]!
    let xi := y.get! i / E.lower.get! (si + (i - fi))
    y := y.set! i xi
    for k in [fi:i] do
      y := y.set! k (y.get! k - E.lower.get! (si + (k - fi)) * xi)
  return y

/-- In-place envelope LU without pivoting (`L` unit lower in `lower`, `U` in `upper`); `none`
when a pivot is below `tol · max|A|`. -/
def lu (E0 : Envelope) (tol : Float := 1e-14) : Option Envelope := Id.run do
  let mut E := E0
  let scale := E.lower.data.foldl (fun m x => if x.abs > m then x.abs else m) 0
  let scale := E.upper.data.foldl (fun m x => if x.abs > m then x.abs else m) scale
  for i in [0:E.n] do
    let fi := E.first[i]!
    let si := E.lstart[i]!
    -- row i of L: L[i,j] = (A[i,j] - Σ_k L[i,k] U[k,j]) / U[j,j]
    for j in [fi:i] do
      let fj := E.first[j]!
      let sj := E.lstart[j]!
      let lo := max fi fj
      let s := rowDot E.lower E.upper (si + lo - fi) (sj + lo - fj) 0 0 (j - lo)
      let q := si + (j - fi)
      E := { E with lower := E.lower.set! q ((E.lower.get! q - s) / E.upper.get! (sj + (j - fj))) }
    -- column i of U: U[j,i] = A[j,i] - Σ_k L[j,k] U[k,i]
    for j in [fi:i + 1] do
      let fj := E.first[j]!
      let sj := E.lstart[j]!
      let lo := max fi fj
      let s := rowDot E.lower E.upper (sj + lo - fj) (si + lo - fi) 0 0 (j - lo)
      let q := si + (j - fi)
      E := { E with upper := E.upper.set! q (E.upper.get! q - s) }
    if !((E.upper.get! (si + (i - fi))).abs > tol * scale) then return none
  -- the unit diagonal of L
  for i in [0:E.n] do
    let q := E.lstart[i]! + (i - E.first[i]!)
    E := { E with lower := E.lower.set! q 1 }
  return some E

/-- Solve `L U x = b` with an LU envelope. -/
def luSolve (E : Envelope) (b : FloatArray) : FloatArray := Id.run do
  let n := E.n
  let mut y := b
  for i in [0:n] do
    let fi := E.first[i]!
    let si := E.lstart[i]!
    let s := rowDot E.lower y si fi 0 0 (i - fi)
    y := y.set! i (y.get! i - s)
  for ii in [0:n] do
    let j := n - 1 - ii
    let fj := E.first[j]!
    let sj := E.lstart[j]!
    let xj := y.get! j / E.upper.get! (sj + (j - fj))
    y := y.set! j xj
    for k in [fj:j] do
      y := y.set! k (y.get! k - E.upper.get! (sj + (k - fj)) * xj)
  return y

end Envelope

/-! ## Factorizations with an ordering -/

/-- A factored sparse matrix: the ordering, and the envelope factors. -/
structure Factor where
  /-- `perm[k]` = old index at position `k`. -/
  perm : Array Nat
  /-- The factors of `P A Pᵀ`. -/
  env : Envelope
  /-- Cholesky (`true`) or LU. -/
  chol : Bool
  deriving Inhabited

namespace Factor

/-- Solve `A x = b`. -/
def solve (F : Factor) (b : FloatArray) : FloatArray := Id.run do
  let n := F.perm.size
  let pb : FloatArray := ⟨(Array.range n).map fun k => b.get! F.perm[k]!⟩
  let px := if F.chol then F.env.cholSolve pb else F.env.luSolve pb
  let mut x : FloatArray := ⟨Array.replicate n 0⟩
  for k in [0:n] do
    x := x.set! F.perm[k]! (px.get! k)
  return x

end Factor

namespace Sparse

/-- Julia `cholesky(A)` of a symmetric positive definite sparse matrix (RCM + envelope). -/
def cholesky (A : Sparse) : Option Factor :=
  let p := rcm A
  (Envelope.ofSparse (A.permute p)).cholesky.map fun E => ⟨p, E, true⟩

/-- Julia `lu(A)` without pivoting (RCM + envelope); `none` at a tiny pivot. -/
def luNoPivot (A : Sparse) : Option Factor :=
  let p := rcm A
  (Envelope.ofSparse (A.permute p)).lu.map fun E => ⟨p, E, false⟩

/-- Euclidean norm of a vector. -/
def vnorm (x : FloatArray) : Float := Float.sqrt (x.data.foldl (fun s v => s + v * v) 0)

/-- `‖b - A x‖ / ‖b‖` (relative residual; `‖A x‖` if `b = 0`). -/
def relResidual (A : Sparse) (x b : FloatArray) : Float :=
  let r := A.mulVec x
  let d : FloatArray := ⟨(Array.range b.size).map fun i => b.get! i - r.get! i⟩
  let nb := vnorm b
  if nb == 0 then vnorm d else vnorm d / nb

end Sparse

end Cartan.Solve
