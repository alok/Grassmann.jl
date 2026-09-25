import Cartan.Show

/-!
# Kernel-checked facts about fields

* **Sizes by construction.** Every field carries `data.size = width F * card m` as a proof field,
  established once per combinator (`size_buildFlat`, `size_zipFloats`, …, in the defining
  modules), so no field of the wrong length can exist (Julia's inner constructor does not check,
  port notes §3.2).
* **Re-gluing and re-basing keep the points.** `card` of a re-glued grid is the grid's `card`
  (`rfl` lemmas below), which is why re-glued fields reuse their fibers unchanged.
* **Reading back what was built.** For fibers whose flat encoding is lawful (`LawfulFlatFiber`:
  reading the element just pushed returns it, and pushing leaves earlier elements alone), the
  fiber at `i` of `ofFn m f` is `f i`. The functor laws of `map` and `zipWith`, and the values of
  `const`, `tabulate` and the scalar maps, follow pointwise (port notes §8.7 item 6).
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-! ## Lawful flat encodings -/

/-- A flat encoding that reads back what it wrote. -/
class LawfulFlatFiber (F : Type) [FlatFiber F] : Prop where
  /-- Reading the element just pushed returns it. -/
  read_push_self (a : FloatArray) (x : F) : (FlatFiber.read (FlatFiber.push a x) a.size : F) = x
  /-- Pushing leaves the elements stored before it unchanged. -/
  read_push_lt (a : FloatArray) (x : F) (off : Nat) (h : off + FlatFiber.width F ≤ a.size) :
    (FlatFiber.read (FlatFiber.push a x) off : F) = FlatFiber.read a off

/-- `FloatArray.get!` of the element just pushed. -/
theorem _root_.FloatArray.get!_push_self (a : FloatArray) (x : Float) : (a.push x).get! a.size = x := by
  cases a with | mk ds =>
  simp [FloatArray.push, FloatArray.get!, FloatArray.size]

/-- `FloatArray.get!` below the pushed element. -/
theorem _root_.FloatArray.get!_push_lt (a : FloatArray) (x : Float) (i : Nat) (h : i < a.size) :
    (a.push x).get! i = a.get! i := by
  cases a with | mk ds =>
  simp only [FloatArray.size] at h
  have h' : i < (ds.push x).size := by simp; omega
  simp [FloatArray.push, FloatArray.get!, h, getElem!_pos (ds.push x) i h', Array.getElem_push_lt h]

instance : LawfulFlatFiber Float where
  read_push_self a x := by
    show (a.push x).get! a.size = x
    exact FloatArray.get!_push_self a x
  read_push_lt a x off h := by
    show (a.push x).get! off = a.get! off
    exact FloatArray.get!_push_lt a x off (by simp [FlatFiber.width] at h; omega)

instance : LawfulFlatFiber (Complex Float) where
  read_push_self a z := by
    show Complex.mk (((a.push z.re).push z.im).get! a.size) (((a.push z.re).push z.im).get! (a.size + 1)) = z
    have h1 : a.size < (a.push z.re).size := by simp
    rw [FloatArray.get!_push_lt _ _ _ h1, FloatArray.get!_push_self]
    have h2 : a.size + 1 = (a.push z.re).size := by simp
    rw [h2, FloatArray.get!_push_self]
  read_push_lt a z off h := by
    show Complex.mk (((a.push z.re).push z.im).get! off) (((a.push z.re).push z.im).get! (off + 1)) =
      Complex.mk (a.get! off) (a.get! (off + 1))
    simp only [FlatFiber.width] at h
    have h1 : off < (a.push z.re).size := by simp; omega
    have h2 : off + 1 < (a.push z.re).size := by simp; omega
    rw [FloatArray.get!_push_lt _ _ _ h1, FloatArray.get!_push_lt _ _ _ h2,
      FloatArray.get!_push_lt _ _ _ (by omega), FloatArray.get!_push_lt _ _ _ (by omega)]

/-! ## Reading back built arrays -/

section Build

variable {F : Type} [FlatFiber F] [LawfulFlatFiber F]

/-- Building more elements leaves an element already stored unchanged. -/
theorem read_buildLoop_prefix (f : Nat → F) : ∀ (k i : Nat) (acc : FloatArray) (off : Nat),
    off + FlatFiber.width F ≤ acc.size →
      (FlatFiber.read (buildLoop f k i acc) off : F) = FlatFiber.read acc off
  | 0, _, _, _, _ => rfl
  | k + 1, i, acc, off, h => by
    rw [buildLoop, read_buildLoop_prefix f k (i + 1) _ off (by rw [FlatFiber.size_push]; omega),
      LawfulFlatFiber.read_push_lt acc (f i) off h]

/-- The element `j` of a built array is `f j` (the array started at `base`). -/
theorem read_buildLoop (f : Nat → F) (base : Nat) : ∀ (k i : Nat) (acc : FloatArray) (j : Nat),
    acc.size = base + i * FlatFiber.width F → i ≤ j → j < i + k →
      (FlatFiber.read (buildLoop f k i acc) (base + j * FlatFiber.width F) : F) = f j
  | 0, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | k + 1, i, acc, j, hs, h1, h2 => by
    rw [buildLoop]
    by_cases hj : j = i
    · subst hj
      rw [read_buildLoop_prefix f k (j + 1) _ _ (by rw [FlatFiber.size_push, hs]; exact Nat.le_refl _),
        ← hs, LawfulFlatFiber.read_push_self]
    · exact read_buildLoop f base k (i + 1) _ j
        (by rw [FlatFiber.size_push, hs, Nat.succ_mul, Nat.add_assoc]) (by omega) (by omega)

/-- The element `j < n` of `buildFlat n f` is `f j`. -/
theorem read_buildFlat (n : Nat) (f : Nat → F) (j : Nat) (h : j < n) :
    (FlatFiber.read (buildFlat n f) (j * FlatFiber.width F) : F) = f j := by
  have := read_buildLoop f 0 n 0 (FloatArray.emptyWithCapacity (n * FlatFiber.width F)) j
    (by simp [FloatArray.emptyWithCapacity, FloatArray.size]) (Nat.zero_le _) (by omega)
  simpa [buildFlat] using this

end Build

/-! ## Lawful static vectors and Grassmann elements -/

section Vectors

variable {α : Type} [Packed α] [Inhabited α] [FlatFiber α] [LawfulFlatFiber α]

omit [LawfulFlatFiber α] in
/-- `pushValues` is `buildLoop` of the entries. -/
theorem pushValues_eq {n : Nat} (v : Values α n) : ∀ (k i : Nat) (a : FloatArray),
    pushValues v k i a = buildLoop (v.get! ·) k i a
  | 0, _, _ => rfl
  | k + 1, i, a => by rw [pushValues, buildLoop, pushValues_eq v k (i + 1)]

omit [FlatFiber α] [LawfulFlatFiber α] in
/-- `Values.get!` in range is `get`. -/
theorem Values.get!_eq_get {n : Nat} (v : Values α n) (i : Fin n) : v.get! i.1 = v.get i := by
  simp [Values.get!, Packed.get!, Values.get, v.size_eq, i.2]

/-- Reading back pushed static vectors. -/
theorem read_pushValues_self {n : Nat} (a : FloatArray) (v : Values α n) :
    (readValues n (pushValues v n 0 a) a.size : Values α n) = v := by
  apply Values.ext
  intro i
  simp only [readValues, Values.get_ofFn]
  rw [pushValues_eq, read_buildLoop (v.get! ·) a.size n 0 a i.1 (by simp) (Nat.zero_le _) (by omega),
    Values.get!_eq_get]

/-- Pushed static vectors leave earlier elements alone. -/
theorem read_pushValues_lt {n : Nat} (a : FloatArray) (v : Values α n) (off : Nat)
    (h : off + n * FlatFiber.width α ≤ a.size) :
    (readValues n (pushValues v n 0 a) off : Values α n) = readValues n a off := by
  apply Values.ext
  intro i
  simp only [readValues, Values.get_ofFn]
  rw [pushValues_eq, read_buildLoop_prefix]
  have : i.1 * FlatFiber.width α + FlatFiber.width α ≤ n * FlatFiber.width α := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ i.2
  omega

instance {n : Nat} : LawfulFlatFiber (Values α n) where
  read_push_self a v := read_pushValues_self a v
  read_push_lt a v off h := read_pushValues_lt a v off h

end Vectors

section Grassmann

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α] [FlatFiber α] [LawfulFlatFiber α]

instance : LawfulFlatFiber (Chain V G α) where
  read_push_self a c := by
    show Chain.mk (readValues _ (pushValues c.v _ 0 a) a.size) = c
    rw [read_pushValues_self]
  read_push_lt a c off h := by
    show Chain.mk (readValues _ (pushValues c.v _ 0 a) off) = Chain.mk (readValues _ a off)
    rw [read_pushValues_lt a c.v off h]

instance : LawfulFlatFiber (Half V p α) where
  read_push_self a c := by
    show Half.mk (readValues _ (pushValues c.v _ 0 a) a.size) = c
    rw [read_pushValues_self]
  read_push_lt a c off h := by
    show Half.mk (readValues _ (pushValues c.v _ 0 a) off) = Half.mk (readValues _ a off)
    rw [read_pushValues_lt a c.v off h]

instance : LawfulFlatFiber (Multivector V α) where
  read_push_self a c := by
    show Multivector.mk (readValues _ (pushValues c.v _ 0 a) a.size) = c
    rw [read_pushValues_self]
  read_push_lt a c off h := by
    show Multivector.mk (readValues _ (pushValues c.v _ 0 a) off) = Multivector.mk (readValues _ a off)
    rw [read_pushValues_lt a c.v off h]

end Grassmann

instance {N : Nat} : LawfulFlatFiber (AffinePoint N) where
  read_push_self a q := by
    show AffinePoint.mk (readValues _ (pushValues q.coords _ 0 a) a.size) = q
    rw [read_pushValues_self]
  read_push_lt a q off h := by
    show AffinePoint.mk (readValues _ (pushValues q.coords _ 0 a) off) =
      AffinePoint.mk (readValues _ a off)
    rw [read_pushValues_lt a q.coords off h]

/-! ## Fields -/

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {F F' F'' : Type}
  [FlatFiber F] [FlatFiber F'] [FlatFiber F'']

/-- The fibers of a field built from a function. -/
@[simp] theorem get_ofFn [LawfulFlatFiber F] (f : Nat → F) (i : Nat) (h : i < card m) :
    (ofFn m f).get i = f i :=
  read_buildFlat (card m) f i h

/-- Julia `broadcast(f, t)` applies `f` at every point. -/
@[simp] theorem get_map [LawfulFlatFiber F'] (f : F → F') (t : TensorField m F) (i : Nat)
    (h : i < card m) : (t.map f).get i = f (t.get i) := get_ofFn _ i h

/-- Pointwise binary operations combine the fibers at every point. -/
@[simp] theorem get_zipWith [LawfulFlatFiber F''] (f : F → F' → F'') (a : TensorField m F)
    (b : TensorField m F') (i : Nat) (h : i < card m) :
    (zipWith f a b).get i = f (a.get i) (b.get i) := get_ofFn _ i h

/-- The constant field. -/
@[simp] theorem get_const [LawfulFlatFiber F] (x : F) (i : Nat) (h : i < card m) :
    (const m x).get i = x := get_ofFn _ i h

/-- Functor law: mapping the identity keeps every fiber. -/
theorem map_id [LawfulFlatFiber F] (t : TensorField m F) (i : Nat) (h : i < card m) :
    (t.map id).get i = t.get i := by simp [h]

/-- Functor law: mapping twice is mapping the composite. -/
theorem map_map [LawfulFlatFiber F'] [LawfulFlatFiber F''] (f : F → F') (g : F' → F'')
    (t : TensorField m F) (i : Nat) (h : i < card m) :
    ((t.map f).map g).get i = (t.map (g ∘ f)).get i := by simp [h]

/-- A commutative fiber operation gives a commutative field operation. -/
theorem zipWith_comm [LawfulFlatFiber F'] (f : F → F → F') (hf : ∀ x y, f x y = f y x)
    (a b : TensorField m F) (i : Nat) (h : i < card m) :
    (zipWith f a b).get i = (zipWith f b a).get i := by simp [h, hf]

section Coordinates

variable {P G : Type} [Coordinates M P G]

/-- Julia `TensorField(dom, fun)`: the fiber at `i` is `fun` of the coordinate at `i`. -/
@[simp] theorem get_tabulate [LawfulFlatFiber F] (f : Coordinate P G → F) (i : Nat) (h : i < card m) :
    (tabulate m f).get i = f (FrameBundle.coordinate m i) := get_ofFn _ i h

/-- Julia `f.(t)`: the fiber at `i` is `f` of the local tensor at `i`. -/
@[simp] theorem get_mapLocal [LawfulFlatFiber F'] (f : LocalTensor (Coordinate P G) F → F')
    (t : TensorField m F) (i : Nat) (h : i < card m) :
    (t.mapLocal f).get i = f (t.localAt i) := get_ofFn _ i h

end Coordinates

/-- Julia `sin(t)` is `sin` at every point. -/
theorem get_sin [Analytic F] [LawfulFlatFiber F] (t : TensorField m F) (i : Nat) (h : i < card m) :
    t.sin.get i = Analytic.sin (t.get i) := get_map _ t i h

end TensorField

/-! ## Bases -/

namespace GridBundle

variable {N : Nat} {P G : Type}

/-- Re-gluing keeps the points. -/
@[simp] theorem card_withTop (b : GridBundle N P G) (t : QuotientTopology N) (h : t.size = b.space.size) :
    card (b.withTop t h) = card b := rfl

/-- The torus keeps the points. -/
@[simp] theorem card_torus (b : GridBundle N P G) : card b.torus = card b := rfl

/-- The open grid of a product space has its points. -/
@[simp] theorem card_ofSpace (ps : ProductSpace N) : card (ofSpace ps) = ps.length := rfl

/-- The grid of a 1-D vector has its elements. -/
theorem card_ofAxis (a : Axis) : card (ofAxis a) = a.length := by
  simp [ofAxis, FrameBundle.card, ProductSpace.length, ProductSpace.size, ProductSpace.ofAxes,
    MeshTopology.gridLength]

end GridBundle

end Cartan
