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
import DirectSum
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

@[simp] theorem halfLayout_false : halfLayout false = .even := rfl
@[simp] theorem halfLayout_true : halfLayout true = .odd := rfl

theorem halfDim_succ (n : Nat) (odd : Bool) : halfDim (n + 1) odd = 2 ^ n := by
  cases odd <;> simp [halfDim, halfLayout, Layout.size]

theorem halfDim_zero_false : halfDim 0 false = 1 := rfl
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

end Grassmann
