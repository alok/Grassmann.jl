import MeshTopology.Quotient
import MeshTopology.Lagrange

/-!
# Theorems

Kernel-checked facts that pin down the index conventions (port-notes/meshtopology.md §8.7):

* **Ghost resolution lands in the grid.** A one-layer ghost index beyond a glued face is mapped
  onto the target axis inside `1..s`, for every combination of low/high source and target faces
  (`ghostCoord_mem`), and `resolveAt` really puts that coordinate on the target axis
  (`resolveAt_target`). This is the property the Q11 typo broke.
* **CrossRange is the half-turn** of a closed periodic axis of odd length: an involution on
  `1..n-1` that maps `1..n` into itself.
* **Lagrange node counts.** `3 + 3(M-1) + centerSimplex 3 M = lagrangeSimplex 3 M` and the
  tetrahedral analogue, for every degree; they make the typed element getters `getVec`, which
  return `Vector Nat (lagrangeSimplex d M)`, typecheck with no runtime cast.
* **Discontinuous numbering is a bijection** `Fin te × Fin N ≃ Fin (N·te)`.
-/

namespace MeshTopology

open QuotientTopology

/-! ## Ghost resolution -/

/-- A one-layer ghost (`0` or `1` beyond a low face, `n` or `n+1` beyond a high face) resolves to
a coordinate inside the target axis `1..s₂`. -/
theorem ghostCoord_mem {low targetLow : Bool} {i n s2 : Int} (hs : 2 ≤ s2)
    (hi : if low then i = 0 ∨ i = 1 else i = n ∨ i = n + 1) :
    1 ≤ ghostCoord low targetLow i n s2 ∧ ghostCoord low targetLow i n s2 ≤ s2 := by
  cases low <;> cases targetLow <;> simp only [ghostCoord, Bool.false_eq_true, ↓reduceIte] at hi ⊢ <;>
    omega

/-- The one-pass `placeGhost` builds exactly the reference vector: the transversal map applied
to the coordinates other than axis `a`, with `x` inserted at axis `a2`. -/
theorem QuotientTopology.placeGhost_eq {N : Nat} (maps : ProductTopology (N - 1))
    (idx : Vector Int N) (a a2 : Fin N) (x : Int) :
    placeGhost maps idx a a2 x =
      ((maps.get (idx.eraseIdx a.1)).insertIdx a2.1 x (by have := a2.2; omega)).cast
        (by have := a.2; omega) := by
  apply Vector.ext
  intro k hk
  simp only [placeGhost, placeGhost.placeGhostCoord, Vector.getElem_ofFn, Vector.getElem_cast,
    Vector.getElem_insertIdx, ProductTopology.get]
  by_cases h1 : k < a2.1
  · by_cases h3 : k < a.1 <;> simp [h1, h3, Vector.getElem_eraseIdx]
  · by_cases h2 : k = a2.1
    · simp [h2]
    · have hk1 : k - 1 + 1 = k := by omega
      by_cases h3 : k - 1 < a.1 <;> simp [h1, h2, h3, Vector.getElem_eraseIdx, hk1]

/-- The fast `resolveAt` equals its reference form. -/
theorem QuotientTopology.resolveAt_eq_ref {N : Nat} (m : QuotientTopology N) (a : Fin N)
    (idx : Vector Int N) (q11 : Bool) : m.resolveAt a idx q11 = m.resolveAtRef a idx q11 := by
  unfold resolveAt resolveAtRef
  simp [placeGhost_eq]

/-- `resolveAt` puts `ghostCoord` on the target face's axis. -/
theorem QuotientTopology.resolveAt_target {N : Nat} (m : QuotientTopology N) (a : Fin N)
    (idx : Vector Int N) (g : Glue N)
    (hg : m.glue[if idx[a] < 2 then lowFace a else highFace a] = some g) :
    (m.resolveAt a idx)[(faceAxis g.target).1]'(faceAxis g.target).2 =
      ghostCoord (decide (idx[a] < 2)) (decide (g.target.1 % 2 = 0)) idx[a] m.size[a]
        m.size[faceAxis g.target] := by
  rw [resolveAt_eq_ref]
  unfold resolveAtRef
  simp only [hg]
  simp [Vector.getElem_cast, Vector.getElem_insertIdx_self]

/-- Hence a one-layer ghost beyond a glued face resolves inside the target axis whenever that
axis has at least two points. -/
theorem QuotientTopology.resolveAt_target_mem {N : Nat} (m : QuotientTopology N) (a : Fin N)
    (idx : Vector Int N) (g : Glue N)
    (hg : m.glue[if idx[a] < 2 then lowFace a else highFace a] = some g)
    (hs : 2 ≤ m.size[faceAxis g.target])
    (hi : idx[a] = 0 ∨ idx[a] = 1 ∨ idx[a] = m.size[a] ∨ idx[a] = m.size[a] + 1) (hn : 2 ≤ m.size[a]) :
    1 ≤ (m.resolveAt a idx)[(faceAxis g.target).1]'(faceAxis g.target).2 ∧
      (m.resolveAt a idx)[(faceAxis g.target).1]'(faceAxis g.target).2 ≤ m.size[faceAxis g.target] := by
  rw [m.resolveAt_target a idx g hg]
  refine ghostCoord_mem ?_ ?_
  · exact_mod_cast hs
  by_cases h : idx[a] < 2
  · rw [decide_eq_true h]; simp only [↓reduceIte]; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ↓reduceIte]; omega

/-! ## CrossRange -/

/-- `CrossRange(n)` maps `1..n` into `1..n`. -/
theorem crossGet_mem {n : Nat} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ n) :
    1 ≤ crossGet n i ∧ crossGet n i ≤ n := by
  simp only [crossGet, crossShift]
  split <;> split <;> omega

/-- For odd `n`, `CrossRange(n)` is an involution on `1..n-1`: the half-turn of the closed
periodic axis whose points `1` and `n` coincide. -/
theorem crossGet_crossGet {n : Nat} (hn : n % 2 = 1) {i : Int} (h1 : 1 ≤ i) (h2 : i < n) :
    crossGet n (crossGet n i) = i := by
  simp only [crossGet, crossShift, hn, beq_self_eq_true, ↓reduceIte]
  split <;> split <;> omega

/-- …and it sends the seam point `n` to its twin `1`. -/
theorem crossGet_crossGet_last {n : Nat} (hn : n % 2 = 1) (h : 3 ≤ n) :
    crossGet n (crossGet n n) = 1 := by
  simp only [crossGet, crossShift, hn, beq_self_eq_true, ↓reduceIte]
  split <;> split <;> omega

/-! ## Lagrange node counts -/

/-- Pascal's rule at `k = 2`. -/
theorem choose_succ_two (M : Nat) : choose (M + 1) 2 = M + choose M 2 := by
  rw [choose_succ_succ, choose_one_right]

/-- Pascal's rule at `k = 3`. -/
theorem choose_succ_three (M : Nat) : choose (M + 1) 3 = choose M 2 + choose M 3 :=
  choose_succ_succ M 2

/-- Triangles: 3 corners, `3(M-1)` edge nodes and `centerSimplex 3 M` cell nodes make
`lagrangeSimplex 3 M = (M+1)(M+2)/2` nodes per element. -/
theorem lagrange_triangle_count (M : Nat) :
    3 + 3 * M + centerSimplex 3 (M + 1) = lagrangeSimplex 3 (M + 1) := by
  show 3 + 3 * M + choose M 2 = choose (M + 1 + 1 + 2 - 1) 2
  have h : M + 1 + 1 + 2 - 1 = M + 3 := by omega
  rw [h, choose_succ_two, choose_succ_two, choose_succ_two]
  omega

/-- Tetrahedra: 4 corners, `6(M-1)` edge nodes, `4·facetSimplex 4 M` facet nodes and
`centerSimplex 4 M` cell nodes make `lagrangeSimplex 4 M` nodes per element. -/
theorem lagrange_tetrahedron_count (M : Nat) :
    4 + 6 * M + 4 * facetSimplex 4 (M + 1) + centerSimplex 4 (M + 1) = lagrangeSimplex 4 (M + 1) := by
  show 4 + 6 * M + 4 * choose M 2 + choose M 3 = choose (M + 1 + 1 + 3 - 1) 3
  have h : M + 1 + 1 + 3 - 1 = M + 4 := by omega
  rw [h, choose_succ_three, choose_succ_three, choose_succ_three, choose_succ_three,
    choose_succ_two, choose_succ_two, choose_succ_two]
  omega

/-- Segments: 2 corners and `M-1` interior nodes. -/
theorem lagrange_edge_count (M : Nat) : 2 + M = lagrangeSimplex 2 (M + 1) := by
  show 2 + M = choose (M + 1 + 1 + 1 - 1) 1
  rw [choose_one_right]; omega

namespace LagrangeTriangles

variable {M : Nat}

/-- Julia `m[i]` with its length in the type: the node list of subspace element `i` of a
degree-`M+1` triangle mesh as a `Vector Nat (lagrangeSimplex 3 (M+1))` (equal to `get`, checked
by the property tests). -/
def getVec (m : LagrangeTriangles (M + 1)) (i : Nat) : Vector Nat (lagrangeSimplex 3 (M + 1)) :=
  let ind := m.t.getFacet i
  let bt := 3 * (ind - 1)
  let np := m.t.totalNodes
  let ne := m.ei.totalNodes
  let cs := centerSimplex 3 (M + 1)
  let v (j : Nat) : Nat := m.t.conn[bt + j]!
  -- local edge j runs from vertex (j+1) % 3 to (j+2) % 3 (v₂→v₃, v₃→v₁, v₁→v₂)
  (Vector.ofFn (n := 3 + 3 * M + cs) fun q =>
    if q.1 < 3 then v q.1
    else if q.1 < 3 + 3 * M then
      let r := q.1 - 3
      let j := r / M
      let k := r % M
      let up := v ((j + 1) % 3) < v ((j + 2) % 3)
      np + M * (m.ei.conn[bt + j]! - 1) + (if up then k + 1 else M - k)
    else np + M * ne + cs * (ind - 1) + (q.1 - 3 - 3 * M) + 1).cast (lagrange_triangle_count M)

end LagrangeTriangles

namespace LagrangeTetrahedra

variable {M : Nat}

/-- Julia `m[i]` with its length in the type (see `LagrangeTriangles.getVec`). -/
def getVec (m : LagrangeTetrahedra (M + 1)) (i : Nat) : Vector Nat (lagrangeSimplex 4 (M + 1)) :=
  let ind := m.t.getFacet i
  let np := m.t.totalNodes
  let ne := m.ei.totalNodes
  let nf := m.fi.totalNodes
  let fs := facetSimplex 4 (M + 1)
  let cs := centerSimplex 4 (M + 1)
  let e0 := 4 + 6 * M
  let f0 := e0 + 4 * fs
  (Vector.ofFn (n := 4 + 6 * M + 4 * fs + cs) fun q =>
    if q.1 < 4 then m.t.conn[4 * (ind - 1) + q.1]!
    else if q.1 < e0 then
      let r := q.1 - 4
      np + M * m.ei.conn[6 * (ind - 1) + r % 6]! - (M - (r / 6 + 1))
    else if q.1 < f0 then
      let r := q.1 - e0
      np + M * ne + fs * m.fi.conn[4 * (ind - 1) + r % 4]! - (fs - (r / 4 + 1))
    else np + M * ne + fs * nf + cs * (ind - 1) + (q.1 - f0) + 1).cast (lagrange_tetrahedron_count M)

end LagrangeTetrahedra

/-! ## Discontinuous numbering -/

/-- Local node `j` of element `e` owns discontinuous node `N·e + j` (0-based; Julia `d[e+1][j+1]
= N·e + j + 1`, MT:561). -/
def discIndex {N te : Nat} (e : Fin te) (j : Fin N) : Fin (N * te) := ⟨N * e.1 + j.1, flat_index_lt e.2 j.2⟩

/-- The owner and local position of a discontinuous node. -/
def discUnindex {N te : Nat} (x : Fin (N * te)) : Fin te × Fin N :=
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => by have := x.2; simp [h] at this
  (⟨x.1 / N, Nat.div_lt_of_lt_mul x.2⟩, ⟨x.1 % N, Nat.mod_lt _ hN⟩)

/-- `discUnindex` inverts `discIndex`. -/
theorem discUnindex_discIndex {N te : Nat} (e : Fin te) (j : Fin N) :
    discUnindex (discIndex e j) = (e, j) := by
  have hj := j.2
  have h1 : (N * e.1 + j.1) / N = e.1 := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]
  have h2 : (N * e.1 + j.1) % N = j.1 := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  apply Prod.ext <;> apply Fin.ext <;> simp [discUnindex, discIndex, h1, h2]

/-- `discIndex` inverts `discUnindex`: the numbering is a bijection. -/
theorem discIndex_discUnindex {N te : Nat} (x : Fin (N * te)) :
    discIndex (discUnindex x).1 (discUnindex x).2 = x := by
  simp only [discIndex, discUnindex]
  exact Fin.ext (Nat.div_add_mod x.1 N)

/-- `DiscontinuousTopology.get` on a full topology is `discIndex` (1-based). -/
theorem DiscontinuousTopology.get_full {N : Nat} (d : DiscontinuousTopology N) (h : d.t.isFull = true)
    (e : Fin d.totalElements) (j : Fin N) :
    (d.get (e.1 + 1))[j.1]'j.2 = (discIndex e j).1 + 1 := by
  simp only [get, SimplexTopology.getFacet, h, Bool.or_true, ↓reduceIte, Vector.getElem_ofFn,
    discIndex, Nat.add_sub_cancel]
  omega

end MeshTopology
