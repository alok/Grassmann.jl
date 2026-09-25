/-
Interpreted multiply-accumulate plans (DESIGN.md §5.3, the fallback kernels).

A `Plan` is DirectSum's `plan₂`/`plan₁` (`DirectSum.Ops`) in structure-of-arrays
form: entry `t` performs

  `out[ic t] += coef t · x[ia t] · y[ib t]`    (binary)
  `out[ic t] += coef t · x[ia t]`              (unary)

in the storage positions of the operand and result layouts. Coefficients are
exact `Rat`s; the interpreter classifies them once (`code`: `+1`, `-1` or
general) so that the common `±1` entries cost one add/subtract and no
conversion, and only general coefficients (diagonal metrics, conformal `½`)
go through `Coeff.ofRat`.

The loops are tail-recursive over `Nat` fuel and read/write the raw packed
storage (`FloatArray` at `α = Float`), `@[specialize]`d on the coefficient
class, per DESIGN.md §2 rules 2-3. Writes are in place: the output buffer is
fresh and uniquely referenced.
-/
import Grassmann.Types.Dims

namespace Grassmann.Kernel

open DirectSum StaticVectors AbstractTensors

/-- A compiled multiply-accumulate plan (structure of arrays). All arrays have
the same length, the number of entries. -/
structure Plan where
  /-- Position in the first operand. -/
  ia : Array UInt32 := #[]
  /-- Position in the second operand (`0` in unary plans). -/
  ib : Array UInt32 := #[]
  /-- Position in the result. -/
  ic : Array UInt32 := #[]
  /-- Coefficient class: `0` is `+1`, `1` is `-1`, `2` is general (`coef`). -/
  code : ByteArray := .empty
  /-- The exact coefficient of every entry. -/
  coef : Array Rat := #[]
  /-- Contributions dropped because they carry a repeated tangent generator
  (a coefficient that is itself a blade of `loworder(V)`, which a scalar
  `Coeff` cannot hold). Always `0` outside tangent spaces. -/
  nested : Nat := 0
  deriving Inhabited

namespace Plan

/-- Number of multiply-accumulate entries. -/
@[inline] def size (p : Plan) : Nat := p.ia.size

/-- Append one entry `out[c] += r · x[a] · y[b]`. -/
def push (p : Plan) (a b c : Nat) (r : Rat) : Plan :=
  { p with
    ia := p.ia.push a.toUInt32, ib := p.ib.push b.toUInt32, ic := p.ic.push c.toUInt32
    code := p.code.push (if r == 1 then 0 else if r == -1 then 1 else 2)
    coef := p.coef.push r }

variable {α : Type} [Coeff α]

/-- Checked read of raw packed storage (zero out of range). -/
@[inline] def rd (a : Packed.Arr α) (i : Nat) : α :=
  if h : i < Packed.size a then Packed.get a ⟨i, h⟩ else Coeff.zero

/-- Checked in-place write of raw packed storage (no-op out of range). -/
@[inline] def wr (a : Packed.Arr α) (i : Nat) (x : α) : Packed.Arr α :=
  if h : i < Packed.size a then Packed.set a ⟨i, h⟩ x else a

/-- Accumulate `v` into `o` with the coefficient of entry `t`. -/
@[inline] def acc (p : Plan) (t : Nat) (o v : α) : α :=
  match p.code[t]! with
  | 0 => o + v
  | 1 => o - v
  | _ => o + Coeff.ofRat p.coef[t]! * v

/-- The binary loop: entries `t, t+1, …, t+k-1`. -/
@[specialize] def loop₂ (p : Plan) (x y : Packed.Arr α) : Nat → Nat → Packed.Arr α → Packed.Arr α
  | 0, _, out => out
  | k + 1, t, out =>
    let c := p.ic[t]!.toNat
    let v := rd x p.ia[t]!.toNat * rd y p.ib[t]!.toNat
    loop₂ p x y k (t + 1) (wr out c (p.acc t (rd out c) v))

/-- The unary loop: entries `t, t+1, …, t+k-1`. -/
@[specialize] def loop₁ (p : Plan) (x : Packed.Arr α) : Nat → Nat → Packed.Arr α → Packed.Arr α
  | 0, _, out => out
  | k + 1, t, out =>
    let c := p.ic[t]!.toNat
    loop₁ p x k (t + 1) (wr out c (p.acc t (rd out c) (rd x p.ia[t]!.toNat)))

/-- Package raw storage of the right size (the size is preserved by the loops,
which only overwrite entries; the fallback is unreachable). -/
@[inline] def finish {k : Nat} (res : Packed.Arr α) : Values α k :=
  if h : Packed.size res = k then ⟨res, h⟩ else zeroValues k

/-- Run a binary plan: the result of `x ⊙ y` in a fresh length-`k` vector. -/
@[specialize] def eval₂ {n m k : Nat} (p : Plan) (x : Values α n) (y : Values α m) : Values α k :=
  finish (loop₂ p x.data y.data p.size 0 (zeroValues (α := α) k).data)

/-- Run a unary plan: the image of `x` in a fresh length-`k` vector. -/
@[specialize] def eval₁ {n k : Nat} (p : Plan) (x : Values α n) : Values α k :=
  finish (loop₁ p x.data p.size 0 (zeroValues (α := α) k).data)

end Plan

end Grassmann.Kernel
