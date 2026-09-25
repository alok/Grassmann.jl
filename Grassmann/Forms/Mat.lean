/-
Dense column-major matrices over packed coefficients: the storage of every
linear-map type of `Grassmann.Forms` (port-notes/grassmann-forms.md §3.2, §8.1).

Julia stores a linear map `Λ^g V → Λ^h W` as a nested `Chain{V,g,Chain{W,h,T}}`:
an outer chain indexed by the domain blades (the columns) whose coefficients are
the column images (`forms.jl:555-561`, `multivectors.jl:99`), an isbits
tuple-of-tuples. Here the same data is one flat column-major buffer
`Values α (r * c)` (a bare `FloatArray` at `α = Float`, no boxing), and the
nested-chain view is a cheap column extraction (`Mat.col`).

Entry `(i, j)` (row `i` = codomain component, column `j` = domain blade, both
0-based) lives at `j * r + i`: Julia's `A[i+1, j+1] = A.v[j+1].v[i+1]`.

The multiply-accumulate loops follow Julia's evaluation order exactly, so
`Float` results are bit-identical: the generated `matmul` (`forms.jl:957-968`)
computes `out[i] = A[i,1]*x[1] + A[i,2]*x[2] + …` as a left fold that *starts
from the first product* (Julia's `+(a, b, c…)`), with the matrix entry on the
left. The loops are tail-recursive with explicit accumulators and are
`@[specialize]`d on the coefficient class (DESIGN.md §2 rules 2-3), so at
`Float` they compile to unboxed `FloatArray` code.
-/
import Grassmann.Types.Dims

namespace Grassmann.Forms

open StaticVectors AbstractTensors

/-- `j * r + i < r * c` for `i < r`, `j < c`: column-major positions are in range. -/
theorem colMajor_lt {r c i j : Nat} (hi : i < r) (hj : j < c) : j * r + i < r * c := by
  have h1 : j * r + i < (j + 1) * r := by rw [Nat.succ_mul]; omega
  have h2 : (j + 1) * r ≤ c * r := Nat.mul_le_mul_right r hj
  rw [Nat.mul_comm r c]; omega

/-- `C(n, 1) = n`. -/
theorem binomial_one (n : Nat) : Leibniz.binomial n 1 = n := by simp [Leibniz.binomial]

/-- The grade-1 layout of an `n`-generator space has `n` entries. -/
theorem chainOne_size (n : Nat) : (DirectSum.Layout.chain 1).size n = n := binomial_one n

/-- A position below `r * c` forces `0 < r`. -/
theorem pos_of_lt_mul {r c t : Nat} (h : t < r * c) : 0 < r :=
  Nat.pos_of_ne_zero fun hr => by rw [hr, Nat.zero_mul] at h; exact absurd h (Nat.not_lt_zero _)

/-- The column of a column-major position below `r * c` is below `c`. -/
theorem div_lt_of_lt_mul {r c t : Nat} (h : t < r * c) : t / r < c :=
  (Nat.div_lt_iff_lt_mul (pos_of_lt_mul h)).2 (Nat.lt_of_lt_of_eq h (Nat.mul_comm r c))

/-- A dense `r × c` matrix, column-major (rows = codomain components, columns
= domain blades). -/
structure Mat (r c : Nat) (α : Type) [Coeff α] where
  /-- The entries in column-major order: `(i, j)` at `j * r + i`. -/
  v : Values α (r * c)

namespace Mat

variable {r c k : Nat} {α : Type} [Coeff α]

/-! ## Raw access -/

/-- Checked read of raw packed storage (zero out of range; never taken when
the sizes are right, so the branch is perfectly predicted). -/
@[inline] def rd (a : Packed.Arr α) (i : Nat) : α :=
  if h : i < Packed.size a then Packed.get a ⟨i, h⟩ else Coeff.zero

/-- Package raw storage of the right size (the loops push exactly `k` entries;
the fallback is unreachable). -/
@[inline] def finish {k : Nat} (res : Packed.Arr α) : Values α k :=
  if h : Packed.size res = k then ⟨res, h⟩ else zeroValues k

/-- Entry `(i, j)` (0-based; Julia `A[i+1, j+1]`). -/
@[inline] def get (A : Mat r c α) (i : Fin r) (j : Fin c) : α :=
  A.v.get ⟨j.1 * r + i.1, colMajor_lt i.2 j.2⟩

/-- Entry `(i, j)`, zero when out of range. -/
@[inline] def getD (A : Mat r c α) (i j : Nat) : α :=
  if i < r ∧ j < c then rd A.v.data (j * r + i) else Coeff.zero

/-- Push the entries `i, …, r-1` of column `j` (`g i j`) onto `out`. -/
@[specialize] def fillCol (g : Nat → Nat → α) (r j : Nat) (i : Nat) (out : Packed.Arr α) : Packed.Arr α :=
  if i < r then fillCol g r j (i + 1) (Packed.push out (g i j)) else out
termination_by r - i

/-- Push the columns `j, …, c-1` (column-major) onto `out`. -/
@[specialize] def fillCols (g : Nat → Nat → α) (r c : Nat) (j : Nat) (out : Packed.Arr α) : Packed.Arr α :=
  if j < c then fillCols g r c (j + 1) (fillCol g r j 0 out) else out
termination_by c - j

/-- Build from the entries (Julia `[f(i,j) for i=1:r, j=1:c]`), column by column. -/
@[inline] def ofFn (f : Fin r → Fin c → α) : Mat r c α :=
  ⟨finish (fillCols (fun i j => if h : i < r ∧ j < c then f ⟨i, h.1⟩ ⟨j, h.2⟩ else Coeff.zero) r c 0
    (Packed.mkEmpty (r * c)))⟩

/-- The zero matrix. -/
@[inline] def zero : Mat r c α := ⟨zeroValues _⟩

/-- The identity (ones on the diagonal `i = j`, also when `r ≠ c`). -/
@[inline] def identity : Mat r c α := ofFn fun i j => if i.1 = j.1 then Coeff.one else Coeff.zero

/-- A diagonal matrix. -/
@[inline] def diagonal {n : Nat} (d : Values α n) : Mat n n α :=
  ofFn fun i j => if i.1 = j.1 then d.get i else Coeff.zero

/-- Push the columns `j, …, c-1`, each computed once by `f`. -/
@[specialize] def colsLoop (f : Fin c → Values α r) (j : Nat) (out : Packed.Arr α) : Packed.Arr α :=
  if h : j < c then
    let col := (f ⟨j, h⟩).data
    colsLoop f (j + 1) (fillCol (fun i _ => rd col i) r j 0 out)
  else out
termination_by c - j

/-- Build from columns given as coefficient vectors (Julia `hcat`); each column is
computed once. -/
@[inline] def ofCols (f : Fin c → Values α r) : Mat r c α :=
  ⟨finish (colsLoop f 0 (Packed.mkEmpty (r * c)))⟩

/-- Build from a list of rows (Julia's row-wise matrix literal `[1 2; 3 4]`), if
the shape is right. -/
def ofRows? (rows : List (List α)) : Option (Mat r c α) :=
  if rows.length == r && rows.all (·.length == c) then
    some (ofFn fun i j => (rows[i.1]?.bind (·[j.1]?)).getD Coeff.zero)
  else none

/-- Column `j` as a coefficient vector (Julia `A[j]`, the `j`-th column chain). -/
@[inline] def col (A : Mat r c α) (j : Fin c) : Values α r :=
  Values.ofFn fun i => A.get i j

/-- Row `i` as a coefficient vector (Julia `transpose_row`, `forms.jl:302`). -/
@[inline] def row (A : Mat r c α) (i : Fin r) : Values α c :=
  Values.ofFn fun j => A.get i j

/-- The rows as lists (for tests and display). -/
def toRows (A : Mat r c α) : List (List α) :=
  (List.finRange r).map fun i => (List.finRange c).map fun j => A.get i j

/-- The columns as lists. -/
def toCols (A : Mat r c α) : List (List α) :=
  (List.finRange c).map fun j => (List.finRange r).map fun i => A.get i j

/-- Reinterpret the shape along equalities (identity at runtime). -/
@[inline] def cast {r' c' : Nat} (hr : r = r') (hc : c = c') (A : Mat r c α) : Mat r' c' α :=
  ⟨A.v.cast (by rw [hr, hc])⟩

/-! ## Elementwise operations -/

/-- Map the entries (Julia `map(f, T)`, `forms.jl:1126`). -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (A : Mat r c α) : Mat r c β := ⟨A.v.map f⟩

/-- Combine two matrices entrywise. -/
@[inline] def zipWith (f : α → α → α) (A B : Mat r c α) : Mat r c α := ⟨Values.zipWith f A.v B.v⟩

instance : Add (Mat r c α) := ⟨fun A B => ⟨A.v + B.v⟩⟩
instance : Sub (Mat r c α) := ⟨fun A B => ⟨A.v - B.v⟩⟩
instance : Neg (Mat r c α) := ⟨fun A => ⟨-A.v⟩⟩
instance : HMul α (Mat r c α) (Mat r c α) := ⟨fun s A => ⟨A.v.map (s * ·)⟩⟩
instance : HMul (Mat r c α) α (Mat r c α) := ⟨fun A s => ⟨A.v.map (· * s)⟩⟩
instance [Div α] : HDiv (Mat r c α) α (Mat r c α) := ⟨fun A s => ⟨A.v.map (· / s)⟩⟩
instance : Inhabited (Mat r c α) := ⟨zero⟩
instance [BEq α] : BEq (Mat r c α) := ⟨fun A B => A.v == B.v⟩

/-- Whether every entry is exactly zero. -/
@[inline] def isZero (A : Mat r c α) : Bool := A.v.all Coeff.isZero

/-! ## Products (Julia `matmul`, `forms.jl:954-968`) -/

/-- The strided dot kernel: `acc + Σ_{t<k} f(a[pa + t·sa]) * b[pb + t·sb]`, a left
fold (the `a` factor on the left). Every product of this module is an instance
of it. -/
@[specialize] def sdot (f : α → α) (a b : Packed.Arr α) (sa sb : Nat) :
    (k : Nat) → (pa pb : Nat) → (acc : α) → α
  | 0, _, _, acc => acc
  | k + 1, pa, pb, acc => sdot f a b sa sb k (pa + sa) (pb + sb) (acc + f (rd a pa) * rd b pb)

/-- `Σ_{t<n} f(a[pa + t·sa]) * b[pb + t·sb]` in Julia's order: the first
product, then the others added left to right (Julia `+(x₁, x₂, …)`); zero for
`n = 0`. -/
@[inline] def sdot0 (f : α → α) (a b : Packed.Arr α) (sa sb n pa pb : Nat) : α :=
  match n with
  | 0 => Coeff.zero
  | n + 1 => sdot f a b sa sb n (pa + sa) (pb + sb) (f (rd a pa) * rd b pb)

/-- Push `g i` for `i = i₀, …, n-1` onto `out`. -/
@[specialize] def pushLoop (g : Nat → α) (n : Nat) (i : Nat) (out : Packed.Arr α) : Packed.Arr α :=
  if i < n then pushLoop g n (i + 1) (Packed.push out (g i)) else out
termination_by n - i

/-! ### Unrolled small products (`2 × 2`, `3 × 3`, `4 × 4`) -/

/-- `A x` for an `2 × 2` matrix, unrolled (Julia's order: the first product, then
the others added left to right). -/
@[inline] def mulVec2 (a x : Packed.Arr α) : Packed.Arr α :=
  let x0 := rd x 0
  let x1 := rd x 1
  Packed.push (Packed.push (Packed.mkEmpty 2) ((rd a 0 * x0 + rd a 2 * x1))) ((rd a 1 * x0 + rd a 3 * x1))

/-- `A x` for an `3 × 3` matrix, unrolled (Julia's order: the first product, then
the others added left to right). -/
@[inline] def mulVec3 (a x : Packed.Arr α) : Packed.Arr α :=
  let x0 := rd x 0
  let x1 := rd x 1
  let x2 := rd x 2
  Packed.push (Packed.push (Packed.push (Packed.mkEmpty 3) (((rd a 0 * x0 + rd a 3 * x1) + rd a 6 * x2))) (((rd a 1 * x0 + rd a 4 * x1) + rd a 7 * x2))) (((rd a 2 * x0 + rd a 5 * x1) + rd a 8 * x2))

/-- `A x` for an `4 × 4` matrix, unrolled (Julia's order: the first product, then
the others added left to right). -/
@[inline] def mulVec4 (a x : Packed.Arr α) : Packed.Arr α :=
  let x0 := rd x 0
  let x1 := rd x 1
  let x2 := rd x 2
  let x3 := rd x 3
  Packed.push (Packed.push (Packed.push (Packed.push (Packed.mkEmpty 4) ((((rd a 0 * x0 + rd a 4 * x1) + rd a 8 * x2) + rd a 12 * x3))) ((((rd a 1 * x0 + rd a 5 * x1) + rd a 9 * x2) + rd a 13 * x3))) ((((rd a 2 * x0 + rd a 6 * x1) + rd a 10 * x2) + rd a 14 * x3))) ((((rd a 3 * x0 + rd a 7 * x1) + rd a 11 * x2) + rd a 15 * x3))

/-- `A B` of `2 × 2` matrices, unrolled (each entry in Julia's order). -/
@[inline] def mul2 (a b : Packed.Arr α) : Packed.Arr α :=
  let a0 := rd a 0
  let a1 := rd a 1
  let a2 := rd a 2
  let a3 := rd a 3
  Packed.push (Packed.push (Packed.push (Packed.push (Packed.mkEmpty 4) ((a0 * rd b 0 + a2 * rd b 1))) ((a1 * rd b 0 + a3 * rd b 1))) ((a0 * rd b 2 + a2 * rd b 3))) ((a1 * rd b 2 + a3 * rd b 3))

/-- `A B` of `3 × 3` matrices, unrolled (each entry in Julia's order). -/
@[inline] def mul3 (a b : Packed.Arr α) : Packed.Arr α :=
  let a0 := rd a 0
  let a1 := rd a 1
  let a2 := rd a 2
  let a3 := rd a 3
  let a4 := rd a 4
  let a5 := rd a 5
  let a6 := rd a 6
  let a7 := rd a 7
  let a8 := rd a 8
  Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.mkEmpty 9) (((a0 * rd b 0 + a3 * rd b 1) + a6 * rd b 2))) (((a1 * rd b 0 + a4 * rd b 1) + a7 * rd b 2))) (((a2 * rd b 0 + a5 * rd b 1) + a8 * rd b 2))) (((a0 * rd b 3 + a3 * rd b 4) + a6 * rd b 5))) (((a1 * rd b 3 + a4 * rd b 4) + a7 * rd b 5))) (((a2 * rd b 3 + a5 * rd b 4) + a8 * rd b 5))) (((a0 * rd b 6 + a3 * rd b 7) + a6 * rd b 8))) (((a1 * rd b 6 + a4 * rd b 7) + a7 * rd b 8))) (((a2 * rd b 6 + a5 * rd b 7) + a8 * rd b 8))

/-- `A B` of `4 × 4` matrices, unrolled (each entry in Julia's order). -/
@[inline] def mul4 (a b : Packed.Arr α) : Packed.Arr α :=
  let a0 := rd a 0
  let a1 := rd a 1
  let a2 := rd a 2
  let a3 := rd a 3
  let a4 := rd a 4
  let a5 := rd a 5
  let a6 := rd a 6
  let a7 := rd a 7
  let a8 := rd a 8
  let a9 := rd a 9
  let a10 := rd a 10
  let a11 := rd a 11
  let a12 := rd a 12
  let a13 := rd a 13
  let a14 := rd a 14
  let a15 := rd a 15
  Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.push (Packed.mkEmpty 16) ((((a0 * rd b 0 + a4 * rd b 1) + a8 * rd b 2) + a12 * rd b 3))) ((((a1 * rd b 0 + a5 * rd b 1) + a9 * rd b 2) + a13 * rd b 3))) ((((a2 * rd b 0 + a6 * rd b 1) + a10 * rd b 2) + a14 * rd b 3))) ((((a3 * rd b 0 + a7 * rd b 1) + a11 * rd b 2) + a15 * rd b 3))) ((((a0 * rd b 4 + a4 * rd b 5) + a8 * rd b 6) + a12 * rd b 7))) ((((a1 * rd b 4 + a5 * rd b 5) + a9 * rd b 6) + a13 * rd b 7))) ((((a2 * rd b 4 + a6 * rd b 5) + a10 * rd b 6) + a14 * rd b 7))) ((((a3 * rd b 4 + a7 * rd b 5) + a11 * rd b 6) + a15 * rd b 7))) ((((a0 * rd b 8 + a4 * rd b 9) + a8 * rd b 10) + a12 * rd b 11))) ((((a1 * rd b 8 + a5 * rd b 9) + a9 * rd b 10) + a13 * rd b 11))) ((((a2 * rd b 8 + a6 * rd b 9) + a10 * rd b 10) + a14 * rd b 11))) ((((a3 * rd b 8 + a7 * rd b 9) + a11 * rd b 10) + a15 * rd b 11))) ((((a0 * rd b 12 + a4 * rd b 13) + a8 * rd b 14) + a12 * rd b 15))) ((((a1 * rd b 12 + a5 * rd b 13) + a9 * rd b 14) + a13 * rd b 15))) ((((a2 * rd b 12 + a6 * rd b 13) + a10 * rd b 14) + a14 * rd b 15))) ((((a3 * rd b 12 + a7 * rd b 13) + a11 * rd b 14) + a15 * rd b 15))

/-- Matrix-vector product `A x` (Julia `matmul(value(A), value(x))`,
`forms.jl:957-959`): `out[i] = A[i,1] x[1] + A[i,2] x[2] + …`, metric-free. -/
@[inline] def mulVec (A : Mat r c α) (x : Values α c) : Values α r :=
  let a := A.v.data
  let xd := x.data
  if r = c then
    if r = 3 then finish (mulVec3 a xd)
    else if r = 2 then finish (mulVec2 a xd)
    else if r = 4 then finish (mulVec4 a xd)
    else finish (pushLoop (fun i => sdot0 id a xd r 1 c i 0) r 0 (Packed.mkEmpty r))
  else finish (pushLoop (fun i => sdot0 id a xd r 1 c i 0) r 0 (Packed.mkEmpty r))

/-- Row-vector times matrix, `out[j] = Σ_i f(x[i]) A[i,j]` (Julia
`contraction(a::Chain, b::Chain{V,G,<:Chain})` = `value(a) ⋅ value(col_j)`,
`forms.jl:940`, with `f = conj`). -/
@[inline] def vecMulWith (f : α → α) (x : Values α r) (A : Mat r c α) : Values α c :=
  let a := A.v.data
  let xd := x.data
  finish (pushLoop (fun j => sdot0 f xd a 1 1 r 0 (j * r)) c 0 (Packed.mkEmpty c))

/-- Matrix product `A B` (Julia's operator composition `A ⋅ B`, columns
`matmul(A, B[j])`, `forms.jl:941, 948-950`). -/
@[inline] def mul (A : Mat r c α) (B : Mat c k α) : Mat r k α :=
  let a := A.v.data
  let b := B.v.data
  if r = c ∧ c = k then
    if r = 3 then ⟨finish (mul3 a b)⟩
    else if r = 2 then ⟨finish (mul2 a b)⟩
    else if r = 4 then ⟨finish (mul4 a b)⟩
    else ⟨finish (fillCols (fun i j => sdot0 id a b r 1 c i (j * c)) r k 0 (Packed.mkEmpty (r * k)))⟩
  else ⟨finish (fillCols (fun i j => sdot0 id a b r 1 c i (j * c)) r k 0 (Packed.mkEmpty (r * k)))⟩

/-- The transpose (Julia `_transpose`, `forms.jl:305-308`). -/
@[inline] def transpose (A : Mat r c α) : Mat c r α :=
  let a := A.v.data
  ⟨finish (fillCols (fun i j => rd a (i * r + j)) c r 0 (Packed.mkEmpty (r * c)))⟩

/-- The sum of the diagonal `Σ_{i<min(r,c)} A[i,i]`, a left fold from the first
entry (Julia `tr`, `forms.jl:314-316`: `sum(Values(m[1][1], …))`). -/
def trace (A : Mat r c α) : α :=
  let m := min r c
  if m = 0 then Coeff.zero
  else go A.v.data m 1 (rd A.v.data 0)
where
  /-- `acc + Σ_{i' ∈ [i, m)} A[i',i']`. -/
  @[specialize] go (a : Packed.Arr α) (m : Nat) (i : Nat) (acc : α) : α :=
    if i < m then go a m (i + 1) (acc + rd a (i * r + i)) else acc
  termination_by m - i

/-- The diagonal entries `A[i,i]`, `i < min(r, c)` (Julia `diag`, `forms.jl:638-656`). -/
@[inline] def diag (A : Mat r c α) : Values α (min r c) :=
  Values.ofFn fun i => rd A.v.data (i.1 * r + i.1)

/-- Add `s` to the diagonal (Julia `T + s*I`, `forms.jl:1143-1153`). -/
@[inline] def addDiag (A : Mat r c α) (s : α) : Mat r c α :=
  ofFn fun i j => if i.1 = j.1 then A.get i j + s else A.get i j

/-- The Frobenius pairing Julia computes for `A : B` (`forms.jl:936`):
`sum(value(a) .⋅ value(b))`, i.e. the column dots `Σ_i f(A[i,j]) B[i,j]`
(`f = conj` for Julia's `⋅` on coefficient vectors) summed left to right. -/
def frobenius (f : α → α) (A B : Mat r c α) : α :=
  let a := A.v.data
  let b := B.v.data
  match c with
  | 0 => Coeff.zero
  | c + 1 => (List.range c).foldl (fun acc j => acc + sdot0 f a b 1 1 r ((j + 1) * r) ((j + 1) * r))
      (sdot0 f a b 1 1 r 0 0)

/-- Julia `LinearAlgebra.diagm`-style block embedding: `A` placed at row offset
`ro` and column offset `co` inside a zero `R × C` matrix. -/
def embed {R C : Nat} (A : Mat r c α) (ro co : Nat) (out : Mat R C α) : Mat R C α :=
  Mat.ofFn fun i j =>
    if ro ≤ i.1 ∧ i.1 < ro + r ∧ co ≤ j.1 ∧ j.1 < co + c then A.getD (i.1 - ro) (j.1 - co)
    else out.get i j

end Mat

end Grassmann.Forms
