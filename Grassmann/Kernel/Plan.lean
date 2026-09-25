/-
Interpreted multiply-accumulate plans (DESIGN.md §5.3, the fallback kernels).

A `Plan` is DirectSum's `plan₂`/`plan₁` (`DirectSum.Ops`) in **gather** form:
the entries are grouped by result position (stably, so every output sums its
contributions in DirectSum's operand order), and output `c` is

  `out[c] = Σ_{t ∈ row c} coef t · x[ia t] · y[ib t]`    (binary)
  `out[c] = Σ_{t ∈ row c} coef t · x[ia t]`              (unary)

in the storage positions of the operand and result layouts. Coefficients are
exact `Rat`s; the plan classifies them once (`code`: `+1`, `-1` or general) so
that the common `±1` entries cost one add/subtract and no conversion, and only
general coefficients (diagonal metrics, conformal `½`) go through
`Coeff.ofRat`.

The interpreter follows DESIGN.md §2 rules 2-3: tail-recursive `USize` loops,
one explicit accumulator of the coefficient type per output (an unboxed
register at `α = Float`), `@[specialize]`d on the coefficient class; the result
is pushed into a fresh packed buffer (`FloatArray` at `Float`) of the exact
size, so there is no read-modify-write of the output.
-/
import Grassmann.Types.Dims

namespace Grassmann.Kernel

open DirectSum StaticVectors AbstractTensors

/-- A compiled multiply-accumulate plan in gather form (structure of arrays):
the entries of output `c` are `rowStart[c] ≤ t < rowStart[c+1]`. -/
structure Plan where
  /-- Position in the first operand, per entry. -/
  ia : Array UInt32 := #[]
  /-- Position in the second operand (`0` in unary plans), per entry. -/
  ib : Array UInt32 := #[]
  /-- Coefficient class per entry: `0` is `+1`, `1` is `-1`, `2` is general (`coef`). -/
  code : ByteArray := .empty
  /-- The exact coefficient of every entry. -/
  coef : Array Rat := #[]
  /-- Row boundaries: one more than the number of outputs. -/
  rowStart : Array UInt32 := #[0]
  /-- Contributions dropped because they carry a repeated tangent generator
  (a coefficient that is itself a blade of `loworder(V)`, which a scalar
  `Coeff` cannot hold). Always `0` outside tangent spaces. -/
  nested : Nat := 0
  deriving Inhabited

namespace Plan

/-- Number of multiply-accumulate entries. -/
@[inline] def size (p : Plan) : Nat := p.ia.size

/-- Number of outputs. -/
@[inline] def outputs (p : Plan) : Nat := p.rowStart.size - 1

/-- The plan with the given entries `(ia, ib, coef)` per output position, in
order (zero coefficients are dropped). -/
def ofRows (rows : Array (Array (Nat × Nat × Rat))) (nested : Nat := 0) : Plan :=
  rows.foldl (init := { nested }) fun p row =>
    let p := row.foldl (init := p) fun p (a, b, r) =>
      if r == 0 then p else
      { p with
        ia := p.ia.push a.toUInt32, ib := p.ib.push b.toUInt32
        code := p.code.push (if r == 1 then 0 else if r == -1 then 1 else 2)
        coef := p.coef.push r }
    { p with rowStart := p.rowStart.push p.ia.size.toUInt32 }

/-- The entries `(ia, ib, ic, coef)` of a plan, in order. -/
def entries (p : Plan) : Array (Nat × Nat × Nat × Rat) := Id.run do
  let mut out := #[]
  for c in [0:p.outputs] do
    for t in [p.rowStart[c]!.toNat:p.rowStart[c + 1]!.toNat] do
      out := out.push (p.ia[t]!.toNat, p.ib[t]!.toNat, c, p.coef[t]!)
  return out

variable {α : Type} [Coeff α]

/-- The plan's per-entry arrays all have `p.size` entries (checked once per
evaluation; it holds for every plan built by `ofRows`). -/
def Aligned (p : Plan) : Prop :=
  p.ib.size = p.ia.size ∧ p.code.size = p.ia.size ∧ p.coef.size = p.ia.size

instance (p : Plan) : Decidable p.Aligned := by unfold Aligned; exact inferInstance

/-- Checked read of raw packed storage (zero out of range). -/
@[inline] def rd (a : Packed.Arr α) (i : Nat) : α :=
  if h : i < Packed.size a then Packed.get a ⟨i, h⟩ else Coeff.zero

/-- Accumulate `v` into `o` with the coefficient of entry `t`. -/
@[inline] def acc (p : Plan) (ha : p.Aligned) (t : Nat) (ht : t < p.ia.size) (o v : α) : α :=
  let c := p.code[t]'(by have := ha.2.1; omega)
  if c == 0 then o + v
  else if c == 1 then o - v
  else o + Coeff.ofRat (p.coef[t]'(by have := ha.2.2; omega)) * v

/-- One output of a binary plan: the entries `t, …, e-1`, accumulated into `o`
(bounds proved once per row: no per-entry checks on the plan arrays). -/
@[specialize] def row₂ (p : Plan) (ha : p.Aligned) (x y : Packed.Arr α) (e : Nat) (he : e ≤ p.ia.size)
    (t : Nat) (o : α) : α :=
  if ht : t < e then
    have h1 : t < p.ia.size := by omega
    let v := rd x (p.ia[t]'h1).toNat * rd y (p.ib[t]'(by have := ha.1; omega)).toNat
    row₂ p ha x y e he (t + 1) (p.acc ha t h1 o v)
  else o
termination_by e - t

/-- One output of a unary plan. -/
@[specialize] def row₁ (p : Plan) (ha : p.Aligned) (x : Packed.Arr α) (e : Nat) (he : e ≤ p.ia.size)
    (t : Nat) (o : α) : α :=
  if ht : t < e then
    have h1 : t < p.ia.size := by omega
    row₁ p ha x e he (t + 1) (p.acc ha t h1 o (rd x (p.ia[t]'h1).toNat))
  else o
termination_by e - t

/-- The outputs `c, …, k-1` of a binary plan, pushed onto `out`. -/
@[specialize] def rows₂ (p : Plan) (ha : p.Aligned) (x y : Packed.Arr α) (k c : Nat)
    (out : Packed.Arr α) : Packed.Arr α :=
  if c < k then
    let s := (p.rowStart[c]?.getD 0).toNat
    let e := min (p.rowStart[c + 1]?.getD 0).toNat p.ia.size
    rows₂ p ha x y k (c + 1) (Packed.push out (row₂ p ha x y e (Nat.min_le_right _ _) s Coeff.zero))
  else out
termination_by k - c

/-- The outputs `c, …, k-1` of a unary plan, pushed onto `out`. -/
@[specialize] def rows₁ (p : Plan) (ha : p.Aligned) (x : Packed.Arr α) (k c : Nat)
    (out : Packed.Arr α) : Packed.Arr α :=
  if c < k then
    let s := (p.rowStart[c]?.getD 0).toNat
    let e := min (p.rowStart[c + 1]?.getD 0).toNat p.ia.size
    rows₁ p ha x k (c + 1) (Packed.push out (row₁ p ha x e (Nat.min_le_right _ _) s Coeff.zero))
  else out
termination_by k - c

/-- Package raw storage of the right size (`rows₂`/`rows₁` push exactly `k`
entries onto an empty buffer; the fallback is unreachable). -/
@[inline] def finish {k : Nat} (res : Packed.Arr α) : Values α k :=
  if h : Packed.size res = k then ⟨res, h⟩ else zeroValues k

/-- Run a binary plan: the result of `x ⊙ y` as a fresh length-`k` vector. -/
@[specialize] def eval₂ {n m k : Nat} (p : Plan) (x : Values α n) (y : Values α m) : Values α k :=
  if ha : p.Aligned then finish (rows₂ p ha x.data y.data k 0 (Packed.mkEmpty k)) else zeroValues k

/-- Run a unary plan: the image of `x` as a fresh length-`k` vector. -/
@[specialize] def eval₁ {n k : Nat} (p : Plan) (x : Values α n) : Values α k :=
  if ha : p.Aligned then finish (rows₁ p ha x.data k 0 (Packed.mkEmpty k)) else zeroValues k

end Plan

end Grassmann.Kernel
