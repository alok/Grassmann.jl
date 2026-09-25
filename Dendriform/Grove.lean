import Dendriform.Axioms
import Dendriform.TotalGrove

/-!
# Groves: degree-indexed formal sums of trees

Julia's `Grove` (DF/Dendriform.jl:43-47) is a `size × degr` matrix of Loday names, one
tree per row, rows ordered and possibly repeated. Here `Grove n` is an ordered multiset
(`List Tree`) of trees **of degree `n`**, the degree being a type index whose proof
obligations are erased at runtime. The operations carry Loday's degree laws in their
types:

* `x ⊣ y`, `x ⊢ y`, `x + y : Grove (a + b)` for `x : Grove a`, `y : Grove b`;
* `x * y : Grove (a * b)` (Loday's product is multiplicative on degrees);
* `x ∪ y : Grove n` (canonical union, Julia `∪`, DF/arithmetic.jl:14-29).

These are the bilinear extensions of the tree operations, in Julia's row order, **without**
Julia's grove-level shortcuts for empty and degree-0 operands; `Dendriform.Julia` layers
those on top (on groves whose degree is only known at runtime) for oracle parity.

The dendriform axioms of `Dendriform.Axioms` lift to groves (`Grove.dashv_dashv`, …), as
equivalences `≅` (equal as multisets, Julia's `Grove ==`, DF/Dendriform.jl:147).
-/

namespace Dendriform

open List

/-! ## Bilinear extensions -/

/-- The `x`-major bilinear extension of a tree operation to formal sums. -/
def bil (f : Tree → Tree → List Tree) (X Y : List Tree) : List Tree :=
  X.flatMap fun x => Y.flatMap (f x)

section Bil

variable {f g f' g' : Tree → Tree → List Tree} {X Y Z X' Y' : List Tree}

theorem bil_perm_left (h : X.Perm X') : (bil f X Y).Perm (bil f X' Y) := h.flatMap_right _

theorem bil_perm_right (h : Y.Perm Y') : (bil f X Y).Perm (bil f X Y') :=
  perm_flatMap_congr fun _ _ => h.flatMap_right _

/-- Julia's `+` is `y`-major; as a multiset it is the `x`-major extension. -/
theorem sumL_perm (X Y : List Tree) : (sumL X Y).Perm (bil Tree.sum X Y) :=
  flatMap_swap_perm Y X fun y x => Tree.sum x y

/-- A tree-level identity `(x ∘ y) ∙ z ≅ x ∙' (y ∘' z)` lifts to formal sums. -/
theorem bil_assoc_of
    (h : ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z, ((f x y).flatMap (g · z)).Perm ((f' y z).flatMap (g' x))) :
    (bil g (bil f X Y) Z).Perm (bil g' X (bil f' Y Z)) := by
  simp only [bil, flatMap_assoc]
  refine perm_flatMap_congr fun x hx => perm_flatMap_congr fun y hy => ?_
  refine (flatMap_swap_perm (f x y) Z (fun s z => g s z)).trans ?_
  exact perm_flatMap_congr fun z hz => h x hx y hy z hz

end Bil

/-- Associativity of Julia's grove sum, for all groves (including leaves). -/
theorem sumL_assoc (X Y Z : List Tree) : (sumL (sumL X Y) Z).Perm (sumL X (sumL Y Z)) := by
  refine (sumL_perm _ _).trans ((bil_perm_left (sumL_perm X Y)).trans ?_)
  refine (bil_assoc_of fun x _ y _ z _ => Tree.sum_assoc x y z).trans ?_
  exact (bil_perm_right (sumL_perm Y Z).symm).trans (sumL_perm _ _).symm

/-- Dendriform axiom 1 on formal sums of trees of positive degree. -/
theorem dashvL_dashvL {X Y Z : List Tree} (hX : ∀ x ∈ X, x ≠ .leaf) (hY : ∀ y ∈ Y, y ≠ .leaf)
    (hZ : ∀ z ∈ Z, z ≠ .leaf) : (dashvL (dashvL X Y) Z).Perm (dashvL X (sumL Y Z)) :=
  (bil_assoc_of fun x hx y hy z hz => Tree.dashv_dashv x y z (hX x hx) (hY y hy) (hZ z hz)).trans
    (bil_perm_right (sumL_perm Y Z).symm)

/-- Dendriform axiom 2 on formal sums of trees of positive degree. -/
theorem dashvL_vdashL {X Y Z : List Tree} (hX : ∀ x ∈ X, x ≠ .leaf) (hY : ∀ y ∈ Y, y ≠ .leaf)
    (hZ : ∀ z ∈ Z, z ≠ .leaf) : (dashvL (vdashL X Y) Z).Perm (vdashL X (dashvL Y Z)) :=
  bil_assoc_of fun x hx y hy z hz => Tree.vdash_dashv' x y z (hX x hx) (hY y hy) (hZ z hz)

/-- Dendriform axiom 3 on formal sums of trees of positive degree. -/
theorem vdashL_sumL {X Y Z : List Tree} (hX : ∀ x ∈ X, x ≠ .leaf)
    (hZ : ∀ z ∈ Z, z ≠ .leaf) : (vdashL (sumL X Y) Z).Perm (vdashL X (vdashL Y Z)) :=
  (bil_perm_left (sumL_perm X Y)).trans
    (bil_assoc_of fun x hx y _ z hz => Tree.sum_vdash x y z (hX x hx) (hZ z hz))

/-- `σ` reverses Julia's grove sum. -/
theorem σ_sumL (X Y : List Tree) :
    ((sumL X Y).map Tree.σ).Perm (sumL (Y.map Tree.σ) (X.map Tree.σ)) := by
  simp only [sumL, map_flatMap, flatMap_map]
  refine (perm_flatMap_congr fun y _ => perm_flatMap_congr fun x _ => Tree.σ_sum x y).trans ?_
  exact flatMap_swap_perm Y X fun y x => Tree.sum y.σ x.σ

/-! ## The grove type -/

/-- A grove of degree `n`: an ordered multiset of planar binary trees of degree `n`
(Julia `Grove`, DF/Dendriform.jl:43-47; the rows of `Y`). -/
structure Grove (n : Nat) where
  /-- the trees, in Julia's row order (repetitions allowed) -/
  rows : List Tree
  /-- every row has degree `n` (erased at runtime) -/
  deg_rows : ∀ t ∈ rows, t.deg = n

namespace Grove

variable {a b c n : Nat}

@[ext] theorem ext {x y : Grove n} (h : x.rows = y.rows) : x = y := by
  cases x; cases y; cases h; rfl

instance : DecidableEq (Grove n) := fun x y =>
  if h : x.rows = y.rows then isTrue (ext h) else isFalse fun e => h (e ▸ rfl)

/-- The empty grove of degree `n` (the zero of the formal sums; Julia `Grove(n, 0)`). -/
def zero : Grove n := ⟨[], by simp⟩

instance : EmptyCollection (Grove n) := ⟨zero⟩
instance : Inhabited (Grove n) := ⟨zero⟩

/-- Julia `size`: the number of rows. -/
def size (g : Grove n) : Nat := g.rows.length

/-- The one-row grove of a tree (Julia `Grove(t::PBTree)`, DF/Dendriform.jl:123). -/
def ofTree (t : PBTree n) : Grove n := ⟨[t.1], by simp [t.2]⟩

instance : Coe (PBTree n) (Grove n) := ⟨ofTree⟩

/-- A grove from a list of trees, if all have degree `n`. -/
def ofList? (n : Nat) (ts : List Tree) : Option (Grove n) :=
  if h : ∀ t ∈ ts, t.deg = n then some ⟨ts, h⟩ else none

/-- A grove from Loday names (Julia `Grove(g::Matrix)`, DF/Dendriform.jl:114). -/
def ofNames? (n : Nat) (names : List (List Nat)) : Option (Grove n) := do
  ofList? n (← names.mapM Tree.ofName?)

/-- The total grove `Y_d` of all trees of degree `d` in canonical order (Julia `Grove(d)`
for `d ≥ 1`, DF/Dendriform.jl:124; `Y_0 = {|}`). -/
def total (d : Nat) : Grove d :=
  ⟨(totalGrove d).trees.toList, fun t h => (totalGrove d).deg_trees t (by simpa using h)⟩

/-- Julia `Grove(d, s)` (DF/Dendriform.jl:135): the trees whose tree index `i` has bit
`i - 1` set in `s`, ascending. -/
def ofIndex (d s : Nat) : Grove d := ⟨rowsOfIndex d s, fun _ h => deg_of_mem_rowsOfIndex h⟩

/-- Julia `groveindex(g)` (DF/morphism.jl:122-137): `Σ 2^(i-1)` over the rows' tree indices,
**with multiplicity** (quirk: duplicate rows corrupt it). -/
def index (g : Grove n) : Nat := groveIndexOf g.rows

/-- Julia `grovebit(g)` as a bitset (DF/morphism.jl:96-108): duplicates collapse. -/
def bits (g : Grove n) : Nat := groveBitsOf g.rows

/-- Julia `treeindex(g)` (DF/morphism.jl:70-82): the tree index of every row. -/
def treeIndices (g : Grove n) : List Nat := g.rows.map Tree.treeIndex

/-- The canonical representative: rows sorted by tree index, duplicates removed (what
Julia's `∪` returns). -/
def canonical (g : Grove n) : Grove n := ofIndex n g.bits

/-- Julia `grovesort!(g)` (DF/Dendriform.jl:184-187), without mutation: rows sorted by
tree integer, stably, duplicates kept. -/
def sort (g : Grove n) : Grove n :=
  ⟨g.rows.mergeSort fun s t => s.treeInteger ≤ t.treeInteger,
    fun t h => g.deg_rows t ((List.mergeSort_perm _ _).mem_iff.mp h)⟩

/-- Julia `x < y` on groves (DF/morphism.jl:346): grove-index order. -/
def indexLt {m : Nat} (x : Grove n) (y : Grove m) : Bool := x.index < y.index

/-- Julia `x ≤ y` on groves (DF/morphism.jl:348): grove-index order. -/
def indexLe {m : Nat} (x : Grove n) (y : Grove m) : Bool := x.index ≤ y.index

/-- Julia `GroveError(g)` (DF/morphism.jl:60): zeros iff the rows are sorted. -/
def error (g : Grove n) : List Int := groveError g.rows

/-- Multiset equality, Julia `Grove == Grove` (DF/Dendriform.jl:147), across degrees. -/
def Equiv (x : Grove a) (y : Grove b) : Prop := x.rows.Perm y.rows

@[inherit_doc] scoped infix:50 " ≅ " => Grove.Equiv

instance (x : Grove a) (y : Grove b) : Decidable (x ≅ y) :=
  inferInstanceAs (Decidable (x.rows.Perm y.rows))

/-- Same-degree multiset equality as Lean's `≈`. -/
instance : HasEquiv (Grove n) := ⟨Equiv⟩

theorem Equiv.refl (x : Grove a) : x ≅ x := List.Perm.refl _
theorem Equiv.symm {x : Grove a} {y : Grove b} (h : x ≅ y) : y ≅ x := List.Perm.symm h
theorem Equiv.trans {x : Grove a} {y : Grove b} {z : Grove c} (h₁ : x ≅ y) (h₂ : y ≅ z) :
    x ≅ z := List.Perm.trans h₁ h₂

/-! ### Operations -/

/-- Julia `x ⊣ y` on groves (DF/arithmetic.jl:130-139): degrees add. -/
def dashv (x : Grove a) (y : Grove b) : Grove (a + b) :=
  ⟨dashvL x.rows y.rows, fun _ h => deg_of_mem_dashvL x.deg_rows y.deg_rows h⟩

/-- Julia `x ⊢ y` on groves (DF/arithmetic.jl:196-205): degrees add. -/
def vdash (x : Grove a) (y : Grove b) : Grove (a + b) :=
  ⟨vdashL x.rows y.rows, fun _ h => deg_of_mem_vdashL x.deg_rows y.deg_rows h⟩

/-- Julia `x + y` on groves (DF/arithmetic.jl:226-239): degrees add. -/
def add (x : Grove a) (y : Grove b) : Grove (a + b) :=
  ⟨sumL x.rows y.rows, fun _ h => deg_of_mem_sumL x.deg_rows y.deg_rows h⟩

/-- Julia `x * y` on groves (DF/arithmetic.jl:252-266): degrees multiply. -/
def mul (x : Grove a) (y : Grove b) : Grove (a * b) :=
  ⟨mulL x.rows y.rows, fun _ h => deg_of_mem_mulL x.deg_rows y.deg_rows h⟩

/-- Julia `σ(g)` (DF/Dendriform.jl:216-217): mirror every row. -/
def σ (g : Grove n) : Grove n :=
  ⟨g.rows.map Tree.σ, fun t h => by
    simp only [List.mem_map] at h
    obtain ⟨s, hs, rfl⟩ := h
    simp [g.deg_rows s hs]⟩

/-- Julia `∪(x, y...)` (DF/arithmetic.jl:14-29): the canonical union (OR of the grove
bitsets), together with the number of rows that collapsed (Julia logs
`@info "$s duplicate(s) in grove union"`). -/
def unionCount (gs : List (Grove n)) : Grove n × Nat :=
  let u := ofIndex n (gs.foldl (fun acc g => acc ||| g.bits) 0)
  (u, (gs.foldl (fun acc g => acc + g.size) 0) - u.size)

/-- The canonical union of two groves (Julia `x ∪ y`). -/
def union (x y : Grove n) : Grove n := (unionCount [x, y]).1

instance : HAdd (Grove a) (Grove b) (Grove (a + b)) := ⟨add⟩
instance : HMul (Grove a) (Grove b) (Grove (a * b)) := ⟨mul⟩
instance : Union (Grove n) := ⟨union⟩

/-- Julia `⊣` (comparison precedence in Julia, so below `+`/`∪` here as well). -/
scoped infixl:55 " ⊣ " => Grove.dashv
/-- Julia `⊢`. -/
scoped infixl:55 " ⊢ " => Grove.vdash

@[simp] theorem rows_add (x : Grove a) (y : Grove b) : (x + y).rows = sumL x.rows y.rows := rfl
@[simp] theorem rows_mul (x : Grove a) (y : Grove b) : (x * y).rows = mulL x.rows y.rows := rfl
@[simp] theorem rows_dashv (x : Grove a) (y : Grove b) : (x ⊣ y).rows = dashvL x.rows y.rows := rfl
@[simp] theorem rows_vdash (x : Grove a) (y : Grove b) : (x ⊢ y).rows = vdashL x.rows y.rows := rfl

/-! ### The dendriform axioms for groves -/

theorem ne_leaf_of_pos (g : Grove n) (hn : 0 < n) : ∀ t ∈ g.rows, t ≠ .leaf :=
  fun t ht => Tree.deg_pos_iff.mp (by rw [g.deg_rows t ht]; exact hn)

/-- `(x ⊣ y) ⊣ z ≈ x ⊣ (y + z)` for groves of positive degree. -/
theorem dashv_dashv (x : Grove a) (y : Grove b) (z : Grove c) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : (x ⊣ y) ⊣ z ≅ x ⊣ (y + z) :=
  dashvL_dashvL (x.ne_leaf_of_pos ha) (y.ne_leaf_of_pos hb) (z.ne_leaf_of_pos hc)

/-- `(x ⊢ y) ⊣ z ≈ x ⊢ (y ⊣ z)` for groves of positive degree. -/
theorem vdash_dashv (x : Grove a) (y : Grove b) (z : Grove c) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : (x ⊢ y) ⊣ z ≅ x ⊢ (y ⊣ z) :=
  dashvL_vdashL (x.ne_leaf_of_pos ha) (y.ne_leaf_of_pos hb) (z.ne_leaf_of_pos hc)

/-- `(x + y) ⊢ z ≈ x ⊢ (y ⊢ z)` for groves of positive degree. -/
theorem add_vdash (x : Grove a) (y : Grove b) (z : Grove c) (ha : 0 < a) (hc : 0 < c) :
    (x + y) ⊢ z ≅ x ⊢ (y ⊢ z) :=
  vdashL_sumL (x.ne_leaf_of_pos ha) (z.ne_leaf_of_pos hc)

/-- Associativity of the grove sum: `(x + y) + z ≈ x + (y + z)`. -/
theorem add_assoc (x : Grove a) (y : Grove b) (z : Grove c) : (x + y) + z ≅ x + (y + z) :=
  sumL_assoc x.rows y.rows z.rows

/-- `σ(x + y) ≈ σ(y) + σ(x)` (DF test/runtests.jl:56). -/
theorem σ_add (x : Grove a) (y : Grove b) : (x + y).σ ≅ y.σ + x.σ := σ_sumL x.rows y.rows

end Grove

/-- A grove whose degree is known only at runtime: Julia's `Grove` with its `degr` field. -/
abbrev SomeGrove := (n : Nat) × Grove n

/-- Julia `Grove(s::BitVector)` (DF/Dendriform.jl:127): the degree is recovered from the
Catalan length of the bit vector (`CnInv`), `none` if it is not a Catalan number. -/
def SomeGrove.ofBits? (bits : List Bool) : Option SomeGrove :=
  (catalanInv? bits.length).map fun d =>
    ⟨d, Grove.ofIndex d (bits.zipIdx.foldl (fun acc (b, i) => if b then acc ||| 2 ^ i else acc) 0)⟩

/-! ## Julia's grove-level conventions -/

namespace Julia

/-- Julia `Grove(0)` = `Υ(0)`: the zero grove, a `0 × 1` matrix of degree 0 (the value of
every degree-0 shortcut below). -/
def zero : SomeGrove := ⟨0, Grove.zero⟩

/-- Julia `isempty(x.Y)`: no rows, or no columns (degree 0). -/
def isEmpty (g : SomeGrove) : Bool := g.1 == 0 || g.2.rows.isEmpty

/-- Julia `Grove ⊣ Grove` (DF/arithmetic.jl:130-139) with its shortcuts `x.degr == 0 → 0`
and `y.degr == 0 → x`. Julia throws `MethodError` when a positive-degree operand has no
rows (`vcat()` of nothing); that case is an `Except.error`. -/
def dashv (x y : SomeGrove) : Except String SomeGrove :=
  if x.1 == 0 then .ok zero
  else if y.1 == 0 then .ok x
  else if x.2.rows.isEmpty || y.2.rows.isEmpty then .error "MethodError"
  else .ok ⟨x.1 + y.1, x.2.dashv y.2⟩

/-- Julia `Grove ⊢ Grove` (DF/arithmetic.jl:196-205) with its shortcuts `y.degr == 0 → 0`
and `x.degr == 0 → y`. -/
def vdash (x y : SomeGrove) : Except String SomeGrove :=
  if y.1 == 0 then .ok zero
  else if x.1 == 0 then .ok y
  else if x.2.rows.isEmpty || y.2.rows.isEmpty then .error "MethodError"
  else .ok ⟨x.1 + y.1, x.2.vdash y.2⟩

/-- Julia `Grove + Grove` (DF/arithmetic.jl:226-228): an empty operand (no rows *or*
degree 0) is returned as the unit, so Julia's zero grove doubles as `|` (quirk #12). -/
def add (x y : SomeGrove) : SomeGrove :=
  if isEmpty x then y else if isEmpty y then x else ⟨x.1 + y.1, x.2 + y.2⟩

/-- Julia `Grove * Grove` (DF/arithmetic.jl:258-266): `x.degr == 0 → 0`, `x.degr == 1 → y`,
and a degree-0 right operand yields the zero grove. -/
def mul (x y : SomeGrove) : Except String SomeGrove :=
  if x.1 == 0 then .ok zero
  else if x.1 == 1 then .ok y
  else if x.2.rows.isEmpty then .error "MethodError"
  else if y.1 == 0 then .ok zero
  else if y.2.rows.isEmpty then .error "MethodError"
  else .ok ⟨x.1 * y.1, x.2 * y.2⟩

/-- Julia `Grove(d)` (DF/Dendriform.jl:124): the total grove, except that degree 0 is the
zero grove `Υ(0)`. -/
def total (d : Nat) : SomeGrove := if d == 0 then zero else ⟨d, Grove.total d⟩

/-- Julia `Grove == Grove` (DF/Dendriform.jl:147): same degree, same size, same sorted rows
(Julia sorts both operands in place; this is pure). -/
def eq (x y : SomeGrove) : Bool :=
  x.1 == y.1 && x.2.size == y.2.size && decide (Grove.Equiv x.2 y.2)

end Julia

end Dendriform
