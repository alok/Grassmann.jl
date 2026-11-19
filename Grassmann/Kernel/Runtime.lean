/-
Runtime support for generated Grassmann kernels (`Grassmann.Kernel.Generated.*`), separated
from the compile-time elaborator modules (`Grassmann.Kernel.Codegen.*`) so runtime binaries,
WASM, and C ABI targets never link against `Lean.Elab`/`Lean.Meta`.

Contains:
* `pickBase` / `pickBaseImpl`: in-place output buffer selection for binary kernels;
* `halfL` / `parityOf`: layout parity helpers;
* `refBinOut` … `refConvSubOut`: out-of-line reference kernel fallbacks used by generated dispatch;
* `SandwichKernels`, `RevSandwich`, and the high-priority typed `⊘` / `>>>` instances.
-/
module

public import Grassmann.Algebra.Products
public import Grassmann.Kernel.Dyn

@[expose] public section

namespace Grassmann.Kernel

open DirectSum StaticVectors AbstractTensors

/-- `pickBase`'s run-time choice: `x` when it is exclusive, else `y` when that is, else `x`. -/
@[inline] unsafe def pickBaseImpl {α : Type} [Coeff α] {n : Nat} (x y : Values α n) : Values α n :=
  if isExclusiveUnsafe x then x else if isExclusiveUnsafe y then y else x

/-- The output buffer of a generated kernel with two operands of the output's size: logically
`x`; at run time whichever of `x` and `y` is exclusive, so that the kernel's writes are in
place (`pickBaseImpl`). A kernel using it writes every output, so the result does not depend on
the buffer chosen. -/
@[implemented_by pickBaseImpl]
def pickBase {α : Type} [Coeff α] {n : Nat} (x _y : Values α n) : Values α n := x

end Grassmann.Kernel

namespace Grassmann.Kernel.Codegen

open DirectSum StaticVectors AbstractTensors

/-- The layout of a half (`false` even, `true` odd). -/
@[inline] def halfL (odd : Bool) : Layout := if odd then .odd else .even

/-- The parity of a graded or half layout (`none` for `.full`). -/
def parityOf : Layout → Option Bool
  | .chain g => some (g % 2 == 1)
  | .even => some false
  | .odd => some true
  | .full => none

/-! ## Fallbacks

The generated dispatch falls through to these out-of-line copies of the reference kernels:
one call per unmatched case keeps the dispatch code small, and each is still specialized at
the coefficient type of its call site. -/

/-- `Grassmann.Kernel.refBin`, out of line. -/
@[noinline, specialize] def refBinOut {α : Type} [Coeff α] (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  refBin V op la lb lc x y

/-- `Grassmann.Kernel.refBinProj`, out of line. -/
@[noinline, specialize] def refBinProjOut {α : Type} [Coeff α] (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  refBinProj V op la lb lc x y

/-- `Grassmann.Kernel.refUn`, out of line. -/
@[noinline, specialize] def refUnOut {α : Type} [Coeff α] (V : TensorBundle) (op : UnOp) (la lc : Layout)
    (x : Values α (la.size V.n)) : Values α (lc.size V.n) :=
  refUn V op la lc x

/-- `convertLayout`, out of line (the fallback of the generated conversions). -/
@[noinline, specialize] def refConvOut {α : Type} [Coeff α] (n : Nat) (la lc : Layout)
    (x : Values α (la.size n)) : Values α (lc.size n) :=
  convertLayout n la lc x

/-- The reference `conv la lc x + conv lb lc y`, out of line. -/
@[noinline, specialize] def refConvAddOut {α : Type} [Coeff α] (n : Nat) (la lb lc : Layout)
    (x : Values α (la.size n)) (y : Values α (lb.size n)) : Values α (lc.size n) :=
  convertLayout n la lc x + convertLayout n lb lc y

/-- The reference `conv la lc x - conv lb lc y`, out of line. -/
@[noinline, specialize] def refConvSubOut {α : Type} [Coeff α] (n : Nat) (la lb lc : Layout)
    (x : Values α (la.size n)) (y : Values α (lb.size n)) : Values α (lc.size n) :=
  convertLayout n la lc x - convertLayout n lb lc y

/-- The dynamic layer's interpreted loop, out of line (the fallback of the generated dynamic
dispatch). -/
@[noinline, specialize] def dynLoopOut {α : Type} [Coeff α] (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  Loops.run true { V, op, a := .dense la, b := .dense lb, lc, outerFirst := true } x.data y.data

end Grassmann.Kernel.Codegen

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Kernel.Codegen

/-- The sandwich products of the space `V` on storage layouts (graded or half `R` and `x`),
generic in the coefficient type. -/
class SandwichKernels (V : TensorBundle) where
  /-- `x ⊘ R = (~R) ⟑ x ⟑ involute(R)`, projected onto `x`'s layout (`r` in layout `lr`). -/
  sandwich : {α : Type} → [Coeff α] → (lr lx : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lx.size V.n)
  /-- `R >>> x = R ⟑ x ⟑ clifford(R)`, projected onto `x`'s layout. -/
  tsandwich : {α : Type} → [Coeff α] → (lr lx : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lx.size V.n)
  /-- `R ⟑ x ⟑ ~R` (the typed `R * x * ~R`, unprojected) into layout `lc`, the result layout of
  the typed products (the half of `x`'s parity). -/
  rsandwich : {α : Type} → [Coeff α] → (lr lx lc : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lc.size V.n)

namespace Kernel

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-- The layout of the intermediate product of a sandwich: the half of parity
`parity(R) ⊕ parity(x)` (the full layout when either is not graded). -/
@[inline] def sandwichMid (lr lx : Layout) : Layout :=
  match parityOf lr, parityOf lx with
  | some p, some q => halfL (p ^^ q)
  | _, _ => .full

/-- `x ⊘ R` by the space's `Kernels`, exactly as the typed instances of
`Grassmann.Algebra.Products` compute it (`sandwichCore`). -/
@[inline] def sandwichTwo (lr lx : Layout) (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) :
    Values α (lx.size V.n) :=
  sandwichCore lr lx (sandwichMid lr lx) lx (parityOf lr) r x

/-- `R >>> x` by the space's `Kernels`, as the typed instances compute it. -/
@[inline] def tsandwichTwo (lr lx : Layout) (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) :
    Values α (lx.size V.n) :=
  let lt := sandwichMid lr lx
  Kernels.binProj .mul lt lr lx (Kernels.bin .mul lr lx lt r x) (Kernels.un .clifford lr lr r)

/-- `R * x * ~R` by the space's `Kernels`, as the typed products compute it: `R ⟑ x` into the
half of their parities, `~R`, and the product of the two into `lc`. -/
@[inline] def rsandwichThree (lr lx lc : Layout) (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) :
    Values α (lc.size V.n) :=
  let lt := sandwichMid lr lx
  Kernels.bin .mul lt lr lc (Kernels.bin .mul lr lx lt r x) (Kernels.un .reverse lr lr r)

/-- `sandwichTwo`, out of line (the fallback of generated dispatch; specialized on the
space, a closed constant at every call site, so that it is not rebuilt at run time). -/
@[noinline, specialize V] def sandwichOut (V : TensorBundle) [Kernels V] (lr lx : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lx.size V.n) :=
  sandwichTwo lr lx r x

/-- `tsandwichTwo`, out of line. -/
@[noinline, specialize V] def tsandwichOut (V : TensorBundle) [Kernels V] (lr lx : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lx.size V.n) :=
  tsandwichTwo lr lx r x

/-- `rsandwichThree`, out of line. -/
@[noinline, specialize V] def rsandwichOut (V : TensorBundle) [Kernels V] (lr lx lc : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lc.size V.n) :=
  rsandwichThree lr lx lc r x

end Kernel

/-- The kernel-by-kernel sandwiches for every space (low priority: generated instances win). -/
instance (priority := low) SandwichKernels.reference (V : TensorBundle) [Kernels V] : SandwichKernels V where
  sandwich lr lx r x := Kernel.sandwichTwo lr lx r x
  tsandwich lr lx r x := Kernel.tsandwichTwo lr lx r x
  rsandwich lr lx lc r x := Kernel.rsandwichThree lr lx lc r x

/-! ## Typed sandwiches through `SandwichKernels`

The graded/half shapes of `Grassmann.Algebra.Products` (same types, same values). -/

section Typed

variable {V : TensorBundle} {G H : Nat} {p q : Bool} {α : Type} [Coeff α] [SandwichKernels V] {X Y : Type}

instance (priority := high) [AsChain X V G α] [AsChain Y V H α] : Sandwich X Y (Chain V G α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (.chain H) (.chain G) (AsChain.toChain R).v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain X V G α] : Sandwich X (Half V q α) (Chain V G α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (halfLayout q) (.chain G) R.v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain Y V H α] : Sandwich (Half V p α) Y (Half V p α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (.chain H) (halfLayout p) (AsChain.toChain R).v x.v⟩⟩

instance (priority := high) : Sandwich (Half V p α) (Half V q α) (Half V p α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (halfLayout q) (halfLayout p) R.v x.v⟩⟩

instance (priority := high) [AsChain X V G α] [AsChain Y V H α] : HShiftRight Y X (Chain V G α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (.chain H) (.chain G) (AsChain.toChain R).v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain X V G α] : HShiftRight (Half V q α) X (Chain V G α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (halfLayout q) (.chain G) R.v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain Y V H α] : HShiftRight Y (Half V p α) (Half V p α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (.chain H) (halfLayout p) (AsChain.toChain R).v x.v⟩⟩

instance (priority := high) : HShiftRight (Half V q α) (Half V p α) (Half V p α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (halfLayout q) (halfLayout p) R.v x.v⟩⟩

end Typed

/-! ## `R * x * ~R` as one kernel -/

/-- The fused `R * x * ~R` (Julia evaluates the same three products; here one kernel): an
instance exists for a chain or half `R` and a chain or half `x`, with the result type of the
three typed products. `a * b * ~a` elaborates to `rsandwich a b` when an instance applies. -/
class RevSandwich (Y X : Type) (Z : outParam Type) where
  /-- `R * x * ~R`. -/
  rsandwich : Y → X → Z

section RevSandwich

variable {V : TensorBundle} {G H : Nat} {p q : Bool} {α : Type} [Coeff α] [SandwichKernels V] {X : Type}

instance [AsChain X V G α] : RevSandwich (Half V q α) X (Half V ((q ^^ (G % 2 == 1)) ^^ q) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (halfLayout q) (.chain G) (halfLayout ((q ^^ (G % 2 == 1)) ^^ q))
    R.v (AsChain.toChain x).v⟩⟩

instance : RevSandwich (Half V q α) (Half V p α) (Half V ((q ^^ p) ^^ q) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (halfLayout q) (halfLayout p) (halfLayout ((q ^^ p) ^^ q)) R.v x.v⟩⟩

instance [AsChain X V G α] :
    RevSandwich (Chain V H α) X (Half V (((H + G) % 2 == 1) ^^ (H % 2 == 1)) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (.chain H) (.chain G)
    (halfLayout (((H + G) % 2 == 1) ^^ (H % 2 == 1))) R.v (AsChain.toChain x).v⟩⟩

instance : RevSandwich (Chain V H α) (Half V p α) (Half V ((p ^^ (H % 2 == 1)) ^^ (H % 2 == 1)) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (.chain H) (halfLayout p) (halfLayout ((p ^^ (H % 2 == 1)) ^^ (H % 2 == 1)))
    R.v x.v⟩⟩

end RevSandwich

end Grassmann
