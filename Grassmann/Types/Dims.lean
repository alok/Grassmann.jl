/-
Storage sizes and layout conversions for the typed element containers
(DESIGN.md §4.2; port-notes/grassmann-types.md §3.3-3.4).

Every dense container stores its coefficients in one of DirectSum's
`Layout`s (Julia's storage orders, `Leibniz.indexbasis`/`spinindex`/
`antiindex`/`basisindex`):

| container | layout | size |
|---|---|---|
| `Chain V G α` | `.chain G` | `binomial n G` |
| `Half V false α` (`Spinor`) | `.even` | `2^(n-1)` (`1` when `n = 0`) |
| `Half V true α` (`CoSpinor`) | `.odd` | `2^(n-1)` (`0` when `n = 0`) |
| `Multivector V α` | `.full` | `2^n` |

The sizes are defined *through* `Layout.size`, so the storage type of every
container is definitionally the storage type the kernels (`DirectSum.Ops`
plans) read and write, and no cast is needed at runtime or in proofs.
`Leibniz.binomial` is structural (kernel-reducible): `decide` evaluates the
sizes of small spaces.
-/
import DirectSum.Core
import StaticVectors
import AbstractTensors

namespace Grassmann

open DirectSum StaticVectors AbstractTensors

/-- The layout of a half-algebra container: even grades (`Spinor`, `false`) or
odd grades (`CoSpinor`, `true`). -/
@[inline] def halfLayout (odd : Bool) : Layout := if odd then .odd else .even

/-- Storage size of `Half V odd α` in an `n`-generator space: `2^(n-1)`, except
that for `n = 0` the even half holds the scalar (`1`) and the odd half is empty
(DESIGN §4.2 `halfDim`). -/
def halfDim (n : Nat) (odd : Bool) : Nat := (halfLayout odd).size n

/-- The even half is stored in the `.even` layout. -/
@[simp] theorem halfLayout_false : halfLayout false = .even := rfl
/-- The odd half is stored in the `.odd` layout. -/
@[simp] theorem halfLayout_true : halfLayout true = .odd := rfl

/-- A half of an `(n+1)`-generator space has `2^n` coefficients. -/
theorem halfDim_succ (n : Nat) (odd : Bool) : halfDim (n + 1) odd = 2 ^ n := by
  cases odd <;> simp [halfDim, halfLayout, Layout.size]

/-- For `n = 0` the even half is the scalar. -/
theorem halfDim_zero_false : halfDim 0 false = 1 := rfl
/-- For `n = 0` the odd half is empty. -/
theorem halfDim_zero_true : halfDim 0 true = 0 := rfl

/-- The chain storage size is the layout size (definitionally). -/
theorem chain_size (n G : Nat) : (Layout.chain G).size n = Leibniz.binomial n G := rfl

/-- The full storage size is `2^n` (definitionally). -/
theorem full_size (n : Nat) : Layout.full.size n = 2 ^ n := rfl

example : halfDim 3 false = 4 ∧ halfDim 3 true = 4 ∧ halfDim 0 true = 0 := by decide
example : Leibniz.binomial 5 2 = 10 ∧ Leibniz.binomial 3 4 = 0 := by decide

/-! ## Zero vectors and layout conversion -/

variable {α : Type} [Coeff α]

/-- The zero vector of any length. -/
@[inline] def zeroValues (n : Nat) : Values α n := Values.replicate Coeff.zero

/-- Read entry `i`, or zero when `i` is out of range (runtime-checked read). -/
@[inline] def getD {n : Nat} (x : Values α n) (i : Nat) : α :=
  if h : i < n then x.get ⟨i, h⟩ else Coeff.zero

/-- The blades of layout `l` in storage order, as an array (for `n ≤ 12` a
memoized table read). -/
@[inline] def layoutBlades (n : Nat) (l : Layout) : Array UInt64 := l.blades n

/-- Encode a small layout (`g ≤ 8`) into `0..11` for O(1) flat-array cache indexing. -/
private def layoutSlot : Layout → Option Nat
  | .full => some 0
  | .even => some 1
  | .odd => some 2
  | .chain g => if g ≤ 8 then some (3 + g) else none

/-- Number of cached `(n, la, lc)` entries in the flat table (`n ∈ 0..8`, 12 layouts each). -/
private def flatPermSlots : Nat := 9 * 12 * 12

/-- Index map of `convertLayout n la lc`: entry `i` holds `la.rank n b` when `la` stores
`b = (lc.blades n)[i]!`, else `la.size n` (out of range for `getD`, so it yields `Coeff.zero`). -/
def layoutPermSpec (n : Nat) (la lc : Layout) : Array Nat :=
  let bs := lc.blades n
  Array.ofFn fun (i : Fin (lc.size n)) =>
    let b := bs[i.1]!
    if la.contains n b then la.rank n b else la.size n

theorem size_layoutPermSpec (n : Nat) (la lc : Layout) :
    (layoutPermSpec n la lc).size = lc.size n := by
  simp [layoutPermSpec]

private unsafe def flatPermCacheImpl : IO.Ref (Array (Option (Array Nat))) :=
  unsafeBaseIO (IO.mkRef (Array.replicate flatPermSlots none))

@[implemented_by flatPermCacheImpl]
private opaque flatPermCache : IO.Ref (Array (Option (Array Nat)))

private unsafe def bigPermCacheImpl : IO.Ref (Array ((Nat × Layout × Layout) × Array Nat)) :=
  unsafeBaseIO (IO.mkRef #[])

@[implemented_by bigPermCacheImpl]
private opaque bigPermCache : IO.Ref (Array ((Nat × Layout × Layout) × Array Nat))

private unsafe def layoutPermCached (n : Nat) (la lc : Layout) : Array Nat := unsafeBaseIO do
  if n ≤ 8 then
    match layoutSlot la, layoutSlot lc with
    | some a, some c =>
      let idx := (n * 12 + a) * 12 + c
      let arr ← flatPermCache.get
      match arr[idx]! with
      | some p => return p
      | none =>
        let p := layoutPermSpec n la lc
        flatPermCache.modify fun m => m.set! idx (some p)
        return p
    | _, _ => return layoutPermSpec n la lc
  else
    let key := (n, la, lc)
    let arr ← bigPermCache.get
    match arr.find? (fun kv => kv.1 == key) with
    | some (_, p) => return p
    | none =>
      let p := layoutPermSpec n la lc
      bigPermCache.modify (·.push (key, p))
      return p

/-- Cached index permutation table for `convertLayout n la lc` (referentially transparent;
logically equal to `layoutPermSpec`). -/
@[implemented_by layoutPermCached]
def layoutPerm (n : Nat) (la lc : Layout) : Array Nat :=
  layoutPermSpec n la lc

theorem size_layoutPerm (n : Nat) (la lc : Layout) : (layoutPerm n la lc).size = lc.size n :=
  size_layoutPermSpec n la lc

/-- Tail-recursive loop reading `src` through index map `perm` into a fresh packed array. -/
@[specialize] def applyPermLoop {α : Type} [Coeff α]
    (perm : Array Nat) (src : Packed.Arr α) (i : Nat) :
    (rem : Nat) → i + rem = perm.size → Packed.Arr α → Packed.Arr α
  | 0, _, acc => acc
  | rem + 1, h, acc =>
    let idx := perm[i]'(by omega)
    let v := if hs : idx < Packed.size src then Packed.get src ⟨idx, hs⟩ else Coeff.zero
    applyPermLoop perm src (i + 1) rem (by omega) (Packed.push acc v)

theorem applyPermLoop_eq {α : Type} [Coeff α] (perm : Array Nat) (src : Packed.Arr α) :
    ∀ (rem i : Nat) (h : i + rem = perm.size) (acc : Packed.Arr α),
      applyPermLoop perm src i rem h acc =
        Packed.ofFn.go perm.size
          (fun j => if hs : perm[j.1] < Packed.size src then Packed.get src ⟨perm[j.1], hs⟩ else Coeff.zero)
          rem (by omega) acc
  | 0, _, _, _ => rfl
  | rem + 1, i, h, acc => by
    have hi : perm.size - (rem + 1) = i := by omega
    simp only [applyPermLoop, Packed.ofFn.go, hi]
    exact applyPermLoop_eq perm src rem (i + 1) (by omega) _

/-- Fast layout conversion backed by cached `(n, la, lc)` index maps (`@[csimp]` target of
`convertLayout`). Specializes to an unboxed tail-recursive loop at `Float` without recomputing
`Layout.size`, `contains`, or `rank`. -/
@[inline, specialize] def convertLayoutFast (n : Nat) (la lc : Layout) (x : Values α (la.size n)) :
    Values α (lc.size n) :=
  let perm := layoutPerm n la lc
  ⟨applyPermLoop perm x.data 0 perm.size (Nat.zero_add _) (Packed.mkEmpty perm.size),
    by rw [applyPermLoop_eq, Packed.size_ofFn_go, Packed.size_mkEmpty, Nat.zero_add, size_layoutPerm]⟩

/-- Re-index a coefficient vector from layout `la` into layout `lc`: every blade
of `lc` takes its coefficient in `x` when `la` stores it, and zero otherwise
(blades of `la` that `lc` lacks are dropped). This is Julia's container
conversion (`Multivector(t::Chain)`, `Spinor(t::Chain)`, grade projection
`m(g)`, `even(m)`, ...; grassmann-types.md §4.2), for every pair of layouts. -/
def convertLayout (n : Nat) (la lc : Layout) (x : Values α (la.size n)) : Values α (lc.size n) :=
  let bs := lc.blades n
  Values.ofFn fun i =>
    let b := bs[i.1]!
    if la.contains n b then getD x (la.rank n b) else Coeff.zero

private theorem packed_get_congr {a b : Packed.Arr α} (h : a = b) (i : Nat) (ha : i < Packed.size a) :
    Packed.get a ⟨i, ha⟩ = Packed.get b ⟨i, h ▸ ha⟩ := by
  subst h; rfl

@[csimp] theorem convertLayout_eq_fast : @convertLayout = @convertLayoutFast := by
  funext α _ n la lc x
  apply Values.ext
  intro i
  simp only [convertLayout, convertLayoutFast, Values.ofFn, Values.get]
  let perm := layoutPerm n la lc
  let f : Fin perm.size → α := fun j =>
    if hs : perm[j.1] < Packed.size x.data then Packed.get x.data ⟨perm[j.1], hs⟩ else Coeff.zero
  have hgo : applyPermLoop perm x.data 0 perm.size (Nat.zero_add _) (Packed.mkEmpty perm.size) =
      Packed.ofFn perm.size f :=
    applyPermLoop_eq perm x.data perm.size 0 (Nat.zero_add _) (Packed.mkEmpty perm.size)
  have hi : i.1 < perm.size := (size_layoutPerm n la lc).symm ▸ i.2
  have h1 : Packed.get (applyPermLoop perm x.data 0 perm.size (Nat.zero_add _) (Packed.mkEmpty perm.size))
      ⟨i.1, by rw [hgo, Packed.size_ofFn perm.size f]; exact hi⟩ =
      f ⟨i.1, hi⟩ := by
    rw [packed_get_congr hgo i.1 _]
    exact Packed.get_ofFn perm.size f ⟨i.1, by rw [Packed.size_ofFn]; exact hi⟩
  rw [Packed.get_ofFn, h1]
  have hp : perm[i.1]'(by rw [size_layoutPerm]; exact i.2) =
      if la.contains n (lc.blades n)[i.1]! then la.rank n (lc.blades n)[i.1]! else la.size n := by
    simp [perm, layoutPerm, layoutPermSpec]
  simp only [f, hp, getD, Values.get]
  by_cases hc : la.contains n (lc.blades n)[i.1]!
  · simp only [hc, ↓reduceIte]
    by_cases hr : la.rank n (lc.blades n)[i.1]! < la.size n
    · rw [dite_eq_left hr, dite_eq_left (by rw [x.size_eq]; exact hr)]
    · rw [dite_eq_right hr, dite_eq_right (by rw [x.size_eq]; exact hr)]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [dite_eq_right (by rw [x.size_eq]; omega)]

end Grassmann
