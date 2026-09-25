/-!
# MeshTopology basics

Combinatorial helpers shared by every topology type of MeshTopology.jl
(`src/MeshTopology.jl`, `src/lagrange.jl`, `src/element.jl`), plus the pieces of Grassmann and
Leibniz that MeshTopology borrows without importing (port-notes/meshtopology.md §4.1, Q1):

* `choose`, `simplexNumber`, `lagrangeSimplex`, `centerSimplex`, `facetSimplex`,
  `edgeSimplex` (LG:21-50);
* `combinations` / `combo`: lexicographic `k`-subsets (Leibniz `combinations`, Grassmann `combo`);
* `indexParity`: Leibniz `indexparity!`, an adjacent-swap sort returning the swap parity;
* `boundarySigns`: the coefficients of `∂` of a pseudoscalar, in lexicographic order;
* `CrossRange` (MT:48-63), the antipodal map of a closed periodic axis;
* `IdxVec`: Julia's `OneTo(n)`-or-`Vector{Int}` index vectors;
* column-major linear indexing.

All ids are Julia's 1-based `Int`s; `0` is the "none" sentinel.
-/

namespace MeshTopology

/-! ## Binomials and simplex numbers -/

/-- Binomial coefficient by Pascal's rule, structural in both arguments (Julia `binomial` on
nonnegative arguments: `choose n k = 0` for `k > n`). Only used at small arguments. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt (by omega : n < k),
      choose_eq_zero_of_lt (by omega : n < k + 1)]

@[simp] theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

@[simp] theorem choose_one_right : ∀ n, choose n 1 = n
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_one_right n, choose_zero_right]; omega

/-- `choose n 2 = n(n-1)/2`, as a division-free identity. -/
theorem two_mul_choose_two : ∀ n, 2 * choose n 2 = n * (n - 1)
  | 0 => rfl
  | n + 1 => by
    rw [choose_succ_succ, choose_one_right, Nat.mul_add, two_mul_choose_two n]
    cases n with
    | zero => rfl
    | succ n => simp only [Nat.add_sub_cancel]; rw [Nat.mul_comm (n + 1 + 1) (n + 1)]; grind

/-- Julia `simplexnumber(N, n) = binomial(n+N-1, N)`, the `n`-th `N`-simplex number (LG:21). -/
def simplexNumber (N n : Nat) : Nat := choose (n + N - 1) N

/-- Julia `lagrangesimplex(N, M)`: nodes per element of a degree-`M` Lagrange simplex with `N`
corners, `binomial(M+N-1, N-1)` (LG:47). -/
def lagrangeSimplex (N M : Nat) : Nat := simplexNumber (N - 1) (M + 1)

/-- Julia `centersimplex(N, M)`: interior nodes of a degree-`M` simplex with `N` corners,
`binomial(M-1, N-1)` for `M ≥ 1` (LG:48). -/
def centerSimplex (N M : Nat) : Nat := choose (M - 1) (N - 1)

/-- Julia `facetsimplex(N, M) = centersimplex(N-1, M)` (LG:49). -/
def facetSimplex (N M : Nat) : Nat := centerSimplex (N - 1) M

/-- Julia `edgesimplex(N, M) = M-1` (LG:50). -/
def edgeSimplex (_N M : Nat) : Nat := M - 1

example : (List.range 5).map (lagrangeSimplex 3 ·.succ) = [3, 6, 10, 15, 21] := by decide
example : (List.range 5).map (lagrangeSimplex 4 ·.succ) = [4, 10, 20, 35, 56] := by decide
example : (List.range 5).map (centerSimplex 3 ·.succ) = [0, 0, 1, 3, 6] := by decide
example : (List.range 5).map (centerSimplex 4 ·.succ) = [0, 0, 0, 1, 4] := by decide
example : (List.range 5).map (facetSimplex 4 ·.succ) = [0, 0, 1, 3, 6] := by decide

/-! ## Subsets and parity (Leibniz / Grassmann helpers) -/

/-- All `k`-subsets of positions `0..n-1` in lexicographic order, each ascending. -/
def combinationsIdx (n k : Nat) : Array (Array Nat) :=
  go 0 k #[] #[]
where
  /-- Extend `pre` with `k` more positions `≥ start`. -/
  go (start k : Nat) (pre : Array Nat) (acc : Array (Array Nat)) : Array (Array Nat) :=
    match k with
    | 0 => acc.push pre
    | k + 1 =>
      (List.range (n - start)).foldl (fun acc j =>
        let p := start + j
        if p + k < n then go (p + 1) k (pre.push p) acc else acc) acc
  termination_by k
  decreasing_by omega

/-- Leibniz `combinations(v, k)` (= Combinatorics.jl): the `k`-subsets of the entries of `v`
taken in lexicographic order of positions. -/
def combinations {α : Type} [Inhabited α] (v : Array α) (k : Nat) : Array (Array α) :=
  (combinationsIdx v.size k).map (·.map (v[·]!))

/-- Grassmann `combo(n, g)`: the `g`-subsets of `1:n` in lexicographic order. -/
def combo (n g : Nat) : Array (Array Nat) := (combinationsIdx n g).map (·.map (· + 1))

/-- One step of Leibniz `indexparity!`: gnome sort with adjacent swaps. -/
def indexParityLoop (fuel : Nat) (v : Array Int) (k : Nat) (t : Bool) : Bool × Array Int :=
  match fuel with
  | 0 => (t, v)
  | fuel + 1 =>
    if h : k + 1 < v.size then
      if v[k] > v[k + 1] then
        indexParityLoop fuel (v.swap k (k + 1)) (if k ≠ 0 then k - 1 else k) (!t)
      else indexParityLoop fuel v (k + 1) t
    else (t, v)

/-- Leibniz `indexparity!(ind)` (Leibniz `src/indices.jl:216`): sorts `ind` by adjacent swaps
(equal neighbours are left in place) and returns `(odd number of swaps, sorted)`. -/
def indexParity (v : Array Int) : Bool × Array Int :=
  indexParityLoop ((v.size + 1) * (v.size + 1)) v 0 false

/-- The coefficients of `∂` of the unit pseudoscalar of dimension `M`, in lexicographic order
of the `(M-1)`-subsets: `(-1)^(M-j)` for `j = 1..M` (Grassmann `value(∂(Submanifold(M)(I)))`). -/
def boundarySigns (M : Nat) : Array Int :=
  (Array.range M).map fun j => if (M - 1 - j) % 2 == 0 then 1 else -1

/-! ## CrossRange -/

/-- Julia `crossrange(n) = Int((isodd(n) ? n+1 : n)/2)-1` (MT:55): the half-turn shift of a
closed periodic axis with `n` points (`n ≥ 1`). -/
def crossShift (n : Nat) : Nat := (if n % 2 == 1 then n + 1 else n) / 2 - 1

/-- Julia `CrossRange(n)[i] = i ≤ m ? i+m : i-m` with `m = crossrange(n)` (MT:63). For odd `n`
this is the antipodal map `i ↦ i + (n-1)/2 (mod n-1)` of the closed periodic grid `1..n`. -/
@[inline] def crossGet (n : Nat) (i : Int) : Int :=
  let m := (crossShift n : Int)
  if i ≤ m then i + m else i - m

/-! ## Index vectors -/

/-- Julia's integer index vectors: `OneTo(n)` (the identity `1..n`) or an explicit `Vector{Int}`.
The distinction is observable in Julia (dispatch, `getimage`, `isdisconnected`, type strings), so
it is kept. -/
inductive IdxVec where
  /-- `Base.OneTo(n)`. -/
  | oneTo (n : Nat)
  /-- An explicit `Vector{Int}`. -/
  | arr (a : Array Nat)
  deriving Inhabited, Repr, BEq

namespace IdxVec

/-- Length. -/
@[inline] def size : IdxVec → Nat
  | oneTo n => n
  | arr a => a.size

/-- Julia `v[i+1]` (0-based position `i`); `0` out of range. -/
@[inline] def get (v : IdxVec) (i : Nat) : Nat :=
  match v with
  | oneTo n => if i < n then i + 1 else 0
  | arr a => a[i]?.getD 0

/-- Julia `v[i]` for a 1-based position `i`; `0` out of range. -/
@[inline] def get1 (v : IdxVec) (i : Nat) : Nat := v.get (i - 1)

/-- The entries as an array (Julia `collect`). -/
def toArray : IdxVec → Array Nat
  | oneTo n => (Array.range n).map (· + 1)
  | arr a => a

/-- `true` for `OneTo`. -/
@[inline] def isOneTo : IdxVec → Bool
  | oneTo _ => true
  | arr _ => false

/-- Materialize as an explicit vector (Julia `collect`, used by `refine`). -/
@[inline] def collect (v : IdxVec) : IdxVec := arr v.toArray

/-- Julia `v == w` (elementwise equality, whatever the representation). -/
def eqv (v w : IdxVec) : Bool :=
  match v, w with
  | oneTo n, oneTo m => n == m
  | _, _ => v.toArray == w.toArray

/-- Julia type name of the vector (`Base.OneTo{Int64}` or `Vector{Int64}`). -/
def typeString : IdxVec → String
  | oneTo _ => "Base.OneTo{Int64}"
  | arr _ => "Vector{Int64}"

/-- Julia `maximum` (0 when empty). -/
def maximum : IdxVec → Nat
  | oneTo n => n
  | arr a => a.foldl max 0

end IdxVec

/-- Julia `vertices` of a list of elements (element.jl:34-47): the distinct ids in order of first
appearance; `OneTo(n)` exactly when the largest id equals the number of distinct ids. -/
def verticesOf (ids : Array Nat) : IdxVec := Id.run do
  let mx := ids.foldl max 0
  let mut seen : Array Bool := Array.replicate (mx + 1) false
  let mut out : Array Nat := #[]
  for k in ids do
    if !seen[k]! then
      seen := seen.set! k true
      out := out.push k
  return if mx == out.size then .oneTo out.size else .arr out

/-- Julia `verticesinv(n, ind)` (MT:444-451): the inverse of the vertex list `ind` as a
length-`n` vector (`out[ind[k]] = k`, `0` elsewhere). `OneTo` inputs pass through unchanged, as
does everything when `isc` (the topology is a cover). -/
def verticesInv (n : Nat) (ind : IdxVec) (isc : Bool := false) : IdxVec :=
  if isc then ind else
  match ind with
  | .oneTo _ => ind
  | .arr a => .arr <| (a.foldl (fun (acc : Array Nat × Nat) v =>
      (acc.1.set! (v - 1) (acc.2 + 1), acc.2 + 1)) (Array.replicate n 0, 0)).1

/-! ## Column-major indexing -/

/-- Column-major linear index (1-based) of the 1-based multi-index `idx` in a grid of sizes `s`
(Julia `LinearIndices(s)[idx...]`), without bounds checks. -/
def linearIndex {N : Nat} (s : Vector Nat N) (idx : Vector Int N) : Int := Id.run do
  let mut acc : Int := 0
  let mut stride : Int := 1
  for h : k in [0:N] do
    acc := acc + (idx[k]'h.2.1 - 1) * stride
    stride := stride * (s[k]'h.2.1 : Int)
  return acc + 1

/-- The 1-based multi-index of the 1-based column-major linear index `l` (Julia
`CartesianIndices(s)[l]`). -/
def cartesianIndex {N : Nat} (s : Vector Nat N) (l : Nat) : Vector Nat N :=
  Vector.ofFn fun k : Fin N =>
    let stride := (List.range k.1).foldl (fun acc j => acc * s[j]!) 1
    (l - 1) / stride % s[k] + 1

/-- Product of the grid sizes (Julia `prod(size)`). -/
@[inline] def gridLength {N : Nat} (s : Vector Nat N) : Nat := s.foldl (· * ·) 1

end MeshTopology
