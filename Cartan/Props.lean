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
  reading the element just pushed or written returns it, and pushing or writing leaves the other
  elements alone), the fiber at `i` of `ofFn m f` is `f i`. The functor laws of `map` and `zipWith`, and the values of
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
  /-- Reading the element just written (in range) returns it. -/
  read_write_self (a : FloatArray) (off : Nat) (x : F) (h : off + FlatFiber.width F ≤ a.size) :
    (FlatFiber.read (FlatFiber.write a off x) off : F) = x
  /-- Writing leaves the elements that do not overlap it unchanged. -/
  read_write_other (a : FloatArray) (off off' : Nat) (x : F)
    (h : off + FlatFiber.width F ≤ off' ∨ off' + FlatFiber.width F ≤ off) :
    (FlatFiber.read (FlatFiber.write a off x) off' : F) = FlatFiber.read a off'

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
  read_write_self a off x h := by
    show (a.set! off x).get! off = x
    exact FloatArray.get!_set!_self a off x (by simp [FlatFiber.width] at h; omega)
  read_write_other a off off' x h := by
    show (a.set! off x).get! off' = a.get! off'
    exact FloatArray.get!_set!_ne a off off' x (by simp [FlatFiber.width] at h; omega)

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
  read_write_self a off z h := by
    show Complex.mk (((a.set! off z.re).set! (off + 1) z.im).get! off)
      (((a.set! off z.re).set! (off + 1) z.im).get! (off + 1)) = z
    simp only [FlatFiber.width] at h
    rw [FloatArray.get!_set!_ne _ (off + 1) off _ (by omega),
      FloatArray.get!_set!_self _ off _ (by omega),
      FloatArray.get!_set!_self _ (off + 1) _ (by rw [FloatArray.size_set!']; omega)]
  read_write_other a off off' z h := by
    show Complex.mk (((a.set! off z.re).set! (off + 1) z.im).get! off')
      (((a.set! off z.re).set! (off + 1) z.im).get! (off' + 1)) =
      Complex.mk (a.get! off') (a.get! (off' + 1))
    simp only [FlatFiber.width] at h
    rw [FloatArray.get!_set!_ne _ (off + 1) off' _ (by omega),
      FloatArray.get!_set!_ne _ off off' _ (by omega),
      FloatArray.get!_set!_ne _ (off + 1) (off' + 1) _ (by omega),
      FloatArray.get!_set!_ne _ off (off' + 1) _ (by omega)]

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

/-- Writing more fibers above an element leaves it unchanged. -/
theorem read_fillLoop_below (f : Nat → F) : ∀ (k i off : Nat) (a : FloatArray) (off' : Nat),
    off' + FlatFiber.width F ≤ off →
      (FlatFiber.read (fillLoop f k i off a) off' : F) = FlatFiber.read a off'
  | 0, _, _, _, _, _ => rfl
  | k + 1, i, off, a, off', h => by
    rw [fillLoop, read_fillLoop_below f k (i + 1) _ _ off' (by omega),
      LawfulFlatFiber.read_write_other a off off' _ (Or.inr h)]

/-- The element `j` of a filled array is `f j` (element `i` written at `i·w`). -/
theorem read_fillLoop (f : Nat → F) : ∀ (k i : Nat) (a : FloatArray) (j : Nat),
    (i + k) * FlatFiber.width F ≤ a.size → i ≤ j → j < i + k →
      (FlatFiber.read (fillLoop f k i (i * FlatFiber.width F) a)
        (j * FlatFiber.width F) : F) = f j
  | 0, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | k + 1, i, a, j, hs, h1, h2 => by
    rw [fillLoop]
    by_cases hij : i = j
    · subst hij
      have hle : (i + 1) * FlatFiber.width F ≤ (i + (k + 1)) * FlatFiber.width F :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hle
      rw [read_fillLoop_below f k (i + 1) _ _ _ (Nat.le_refl _),
        LawfulFlatFiber.read_write_self a _ _ (by omega)]
    · have := read_fillLoop f k (i + 1) (FlatFiber.write a (i * FlatFiber.width F) (f i)) j
        (by rw [FlatFiber.size_write, show i + 1 + k = i + (k + 1) by omega]; exact hs)
        (by omega) (by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this

/-- The element `j < n` of `buildFlat n f` is `f j`. -/
theorem read_buildFlat (n : Nat) (f : Nat → F) (j : Nat) (h : j < n) :
    (FlatFiber.read (buildFlat n f) (j * FlatFiber.width F) : F) = f j := by
  have := read_fillLoop f n 0 (Flat.zeros (FlatFiber.width F * n)) j
    (by rw [Flat.size_zeros, Nat.zero_add, Nat.mul_comm]; exact Nat.le_refl _) (Nat.zero_le _)
    (by omega)
  rw [Nat.zero_mul] at this
  exact this

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

/-- A write loop leaves the elements disjoint from every written entry alone. -/
theorem read_writeValues_other {n : Nat} (v : Values α n) (off : Nat) :
    ∀ (k j : Nat) (a : FloatArray) (off' : Nat),
      (∀ i, j ≤ i → i < j + k → off + i * FlatFiber.width α + FlatFiber.width α ≤ off' ∨
        off' + FlatFiber.width α ≤ off + i * FlatFiber.width α) →
      (FlatFiber.read (writeValues v off k j a) off' : α) = FlatFiber.read a off'
  | 0, _, _, _, _ => rfl
  | k + 1, j, a, off', h => by
    rw [writeValues, read_writeValues_other v off k (j + 1) _ off'
        (fun i h1 h2 => h i (by omega) (by omega)),
      LawfulFlatFiber.read_write_other a _ off' _ (h j (Nat.le_refl _) (by omega))]

/-- A write loop stores entry `i` at `off + i·w`. -/
theorem read_writeValues {n : Nat} (v : Values α n) (off : Nat) :
    ∀ (k j : Nat) (a : FloatArray) (i : Nat),
      off + (j + k) * FlatFiber.width α ≤ a.size → j ≤ i → i < j + k →
      (FlatFiber.read (writeValues v off k j a) (off + i * FlatFiber.width α) : α) = v.get! i
  | 0, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | k + 1, j, a, i, hs, h1, h2 => by
    rw [writeValues]
    by_cases hij : j = i
    · subst hij
      have hw : ∀ i', j + 1 ≤ i' → j * FlatFiber.width α + FlatFiber.width α ≤
          i' * FlatFiber.width α := by
        intro i' hi'
        have := Nat.mul_le_mul_right (FlatFiber.width α) hi'
        rwa [Nat.add_mul, Nat.one_mul] at this
      have hdis : ∀ i', j + 1 ≤ i' → i' < j + 1 + k →
          off + i' * FlatFiber.width α + FlatFiber.width α ≤ off + j * FlatFiber.width α ∨
          off + j * FlatFiber.width α + FlatFiber.width α ≤ off + i' * FlatFiber.width α :=
        fun i' h1' _ => Or.inr (by have := hw i' h1'; omega)
      have hsz : off + j * FlatFiber.width α + FlatFiber.width α ≤ a.size := by
        have := hw (j + (k + 1)) (by omega); omega
      rw [read_writeValues_other v off k (j + 1) _ _ hdis, LawfulFlatFiber.read_write_self a _ _ hsz]
    · exact read_writeValues v off k (j + 1) _ i
        (by rw [FlatFiber.size_write, show j + 1 + k = j + (k + 1) by omega]; exact hs)
        (by omega) (by omega)

/-- Reading back written static vectors. -/
theorem read_writeValues_self {n : Nat} (a : FloatArray) (off : Nat) (v : Values α n)
    (h : off + n * FlatFiber.width α ≤ a.size) :
    (readValues n (writeValues v off n 0 a) off : Values α n) = v := by
  apply Values.ext
  intro i
  simp only [readValues, Values.get_ofFn]
  rw [read_writeValues v off n 0 a i.1 (by rw [Nat.zero_add]; exact h) (Nat.zero_le _) (by omega),
    Values.get!_eq_get]

/-- Written static vectors leave the elements that do not overlap them alone. -/
theorem read_writeValues_disjoint {n : Nat} (a : FloatArray) (off off' : Nat) (v : Values α n)
    (h : off + n * FlatFiber.width α ≤ off' ∨ off' + n * FlatFiber.width α ≤ off) :
    (readValues n (writeValues v off n 0 a) off' : Values α n) = readValues n a off' := by
  apply Values.ext
  intro i
  simp only [readValues, Values.get_ofFn]
  have hd : ∀ i', 0 ≤ i' → i' < 0 + n →
      off + i' * FlatFiber.width α + FlatFiber.width α ≤ off' + i.1 * FlatFiber.width α ∨
      off' + i.1 * FlatFiber.width α + FlatFiber.width α ≤ off + i' * FlatFiber.width α := by
    intro i' _ h2
    have h3 : (i' + 1) * FlatFiber.width α ≤ n * FlatFiber.width α :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (i.1 + 1) * FlatFiber.width α ≤ n * FlatFiber.width α :=
      Nat.mul_le_mul_right _ i.2
    rw [Nat.add_mul, Nat.one_mul] at h3 h4
    omega
  rw [read_writeValues_other v off n 0 a _ hd]

instance {n : Nat} : LawfulFlatFiber (Values α n) where
  read_push_self a v := read_pushValues_self a v
  read_push_lt a v off h := read_pushValues_lt a v off h
  read_write_self a off v h := read_writeValues_self a off v h
  read_write_other a off off' v h := read_writeValues_disjoint a off off' v h

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
  read_write_self a off c h := by
    show Chain.mk (readValues _ (writeValues c.v off _ 0 a) off) = c
    rw [read_writeValues_self a off c.v h]
  read_write_other a off off' c h := by
    show Chain.mk (readValues _ (writeValues c.v off _ 0 a) off') = Chain.mk (readValues _ a off')
    rw [read_writeValues_disjoint a off off' c.v h]

instance : LawfulFlatFiber (Half V p α) where
  read_push_self a c := by
    show Half.mk (readValues _ (pushValues c.v _ 0 a) a.size) = c
    rw [read_pushValues_self]
  read_push_lt a c off h := by
    show Half.mk (readValues _ (pushValues c.v _ 0 a) off) = Half.mk (readValues _ a off)
    rw [read_pushValues_lt a c.v off h]
  read_write_self a off c h := by
    show Half.mk (readValues _ (writeValues c.v off _ 0 a) off) = c
    rw [read_writeValues_self a off c.v h]
  read_write_other a off off' c h := by
    show Half.mk (readValues _ (writeValues c.v off _ 0 a) off') = Half.mk (readValues _ a off')
    rw [read_writeValues_disjoint a off off' c.v h]

instance : LawfulFlatFiber (Multivector V α) where
  read_push_self a c := by
    show Multivector.mk (readValues _ (pushValues c.v _ 0 a) a.size) = c
    rw [read_pushValues_self]
  read_push_lt a c off h := by
    show Multivector.mk (readValues _ (pushValues c.v _ 0 a) off) = Multivector.mk (readValues _ a off)
    rw [read_pushValues_lt a c.v off h]
  read_write_self a off c h := by
    show Multivector.mk (readValues _ (writeValues c.v off _ 0 a) off) = c
    rw [read_writeValues_self a off c.v h]
  read_write_other a off off' c h := by
    show Multivector.mk (readValues _ (writeValues c.v off _ 0 a) off') = Multivector.mk (readValues _ a off')
    rw [read_writeValues_disjoint a off off' c.v h]

end Grassmann

instance {N : Nat} : LawfulFlatFiber (AffinePoint N) where
  read_push_self a q := by
    show AffinePoint.mk (readValues _ (pushValues q.coords _ 0 a) a.size) = q
    rw [read_pushValues_self]
  read_push_lt a q off h := by
    show AffinePoint.mk (readValues _ (pushValues q.coords _ 0 a) off) =
      AffinePoint.mk (readValues _ a off)
    rw [read_pushValues_lt a q.coords off h]
  read_write_self a off q h := by
    show AffinePoint.mk (readValues _ (writeValues q.coords off _ 0 a) off) = q
    rw [read_writeValues_self a off q.coords h]
  read_write_other a off off' q h := by
    show AffinePoint.mk (readValues _ (writeValues q.coords off _ 0 a) off') =
      AffinePoint.mk (readValues _ a off')
    rw [read_writeValues_disjoint a off off' q.coords h]

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
    (h : i < card m) : (t.map f).get i = f (t.get i) := by
  rw [map_eq]; exact get_ofFn _ i h

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
    (tabulate m f).get i = f (FrameBundle.coordinate m i) := by
  rw [tabulate_eq]; exact get_ofFn _ i h

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
