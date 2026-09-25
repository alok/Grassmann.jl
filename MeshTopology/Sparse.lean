/-!
# Sparse matrices

The small part of Julia's `SparseArrays` that MeshTopology.jl uses (`element.jl`): building a
`SparseMatrixCSC` from triplets with duplicates summed, transposes, sums and differences, row
sums, row scaling, and column scans. Entries are 1-based, as in Julia. Only nonzero values are
stored (Julia may keep explicit zeros; every comparison here is on dense values).
-/

namespace MeshTopology

/-- A compressed-sparse-column integer matrix (Julia `SparseMatrixCSC{Int,Int}`). -/
structure SparseInt where
  /-- Rows. -/
  m : Nat
  /-- Columns. -/
  n : Nat
  /-- Column `j` (0-based) holds entries `colPtr[j] ..< colPtr[j+1]`. -/
  colPtr : Array Nat
  /-- 1-based row of each stored entry, ascending within a column. -/
  rowVal : Array Nat
  /-- Value of each stored entry (nonzero). -/
  nzVal : Array Int
  deriving Inhabited, Repr

namespace SparseInt

/-- Julia `sparse(I, J, V, m, n)`: duplicates are summed; zero sums are dropped. Indices are
1-based; out-of-range triplets are ignored. -/
def ofTriplets (m n : Nat) (I J : Array Nat) (V : Array Int) : SparseInt := Id.run do
  -- bucket by column, then sort rows within each column
  let mut cols : Array (Array (Nat × Int)) := Array.replicate n #[]
  for h : k in [0:I.size] do
    let i := I[k]
    let j := J[k]!
    if 0 < i && i ≤ m && 0 < j && j ≤ n then
      cols := cols.modify (j - 1) (·.push (i, V[k]!))
  let mut colPtr : Array Nat := #[0]
  let mut rowVal : Array Nat := #[]
  let mut nzVal : Array Int := #[]
  for c in cols do
    let sorted := c.qsort (fun a b => a.1 < b.1)
    let mut cur : Option (Nat × Int) := none
    for (i, v) in sorted do
      match cur with
      | some (ci, cv) =>
        if ci == i then cur := some (ci, cv + v)
        else
          if cv != 0 then
            rowVal := rowVal.push ci
            nzVal := nzVal.push cv
          cur := some (i, v)
      | none => cur := some (i, v)
    if let some (ci, cv) := cur then
      if cv != 0 then
        rowVal := rowVal.push ci
        nzVal := nzVal.push cv
    colPtr := colPtr.push rowVal.size
  return ⟨m, n, colPtr, rowVal, nzVal⟩

/-- The stored triplets `(i, j, v)` (1-based), column-major. -/
def triplets (A : SparseInt) : Array (Nat × Nat × Int) := Id.run do
  let mut out := #[]
  for j in [0:A.n] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      out := out.push (A.rowVal[k]!, j + 1, A.nzVal[k]!)
  return out

/-- Julia `transpose(A)` (materialized). -/
def transpose (A : SparseInt) : SparseInt :=
  let t := A.triplets
  ofTriplets A.n A.m (t.map (·.2.1)) (t.map (·.1)) (t.map (·.2.2))

/-- `A + s * B` (same shape). -/
def addScaled (A B : SparseInt) (s : Int) : SparseInt :=
  let a := A.triplets
  let b := B.triplets
  ofTriplets A.m A.n (a.map (·.1) ++ b.map (·.1)) (a.map (·.2.1) ++ b.map (·.2.1))
    (a.map (·.2.2) ++ b.map fun x => s * x.2.2)

instance : Add SparseInt := ⟨fun A B => A.addScaled B 1⟩
instance : Sub SparseInt := ⟨fun A B => A.addScaled B (-1)⟩

/-- Entry `A[i, j]` (1-based; `0` if not stored). -/
def get (A : SparseInt) (i j : Nat) : Int := Id.run do
  if j == 0 || j > A.n then return 0
  for k in [A.colPtr[j - 1]!:A.colPtr[j]!] do
    if A.rowVal[k]! == i then return A.nzVal[k]!
  return 0

/-- Dense column-major entries (Julia `Matrix(A)`). -/
def toDense (A : SparseInt) : Array Int := Id.run do
  let mut out := Array.replicate (A.m * A.n) 0
  for (i, j, v) in A.triplets do
    out := out.set! (i - 1 + (j - 1) * A.m) v
  return out

/-- Julia `A * ones(n)`: the row sums. -/
def rowSums (A : SparseInt) : Array Int :=
  A.triplets.foldl (fun acc (i, _, v) => acc.modify (i - 1) (· + v)) (Array.replicate A.m 0)

/-- The rows of column `j` (1-based) with a positive entry, ascending (Julia
`findall(>(0), A[:, j])`). -/
def positiveRows (A : SparseInt) (j : Nat) : Array Nat := Id.run do
  let mut out := #[]
  if j == 0 || j > A.n then return out
  for k in [A.colPtr[j - 1]!:A.colPtr[j]!] do
    if A.nzVal[k]! > 0 then out := out.push A.rowVal[k]!
  return out

/-- Number of stored entries. -/
def nnz (A : SparseInt) : Nat := A.nzVal.size

end SparseInt

/-- A compressed-sparse-column `Float64` matrix: the pattern of a `SparseInt` with unboxed
values (Julia `SparseMatrixCSC{Float64,Int}`). -/
structure SparseFloat where
  /-- Rows. -/
  m : Nat
  /-- Columns. -/
  n : Nat
  /-- Column pointers (as `SparseInt.colPtr`). -/
  colPtr : Array Nat
  /-- 1-based rows. -/
  rowVal : Array Nat
  /-- Values. -/
  nzVal : FloatArray
  deriving Inhabited

namespace SparseFloat

/-- Julia `Diagonal(w) * A`: scale row `i` by `w[i]` (1-based rows). -/
def scaleRows (w : FloatArray) (A : SparseInt) : SparseFloat :=
  let vals := (Array.range A.nnz).foldl (fun (acc : FloatArray) k =>
    acc.push (w[A.rowVal[k]! - 1]! * Float.ofInt A.nzVal[k]!)) (FloatArray.emptyWithCapacity A.nnz)
  ⟨A.m, A.n, A.colPtr, A.rowVal, vals⟩

/-- Dense column-major entries. -/
def toDense (A : SparseFloat) : FloatArray := Id.run do
  let mut out := FloatArray.mk (Array.replicate (A.m * A.n) 0.0)
  for j in [0:A.n] do
    for k in [A.colPtr[j]!:A.colPtr[j + 1]!] do
      out := out.set! (A.rowVal[k]! - 1 + j * A.m) A.nzVal[k]!
  return out

end SparseFloat

end MeshTopology
