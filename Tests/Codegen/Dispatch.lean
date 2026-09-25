/-
Compile-time checks of the generated kernels.

* **Dispatch** (`verify_kernel_dispatch`): for every kernel specification of a
  space, the space's `Kernels` instance applied to the literal operation and
  layouts reduces (definitionally, by `whnf` with the kernels themselves held
  opaque) to a call of exactly the generated kernel assigned to it. So the
  generated dispatch never silently falls back to the reference for a shape it
  has a kernel for. The command declares the number of verified specifications,
  which the run-time suite compares with the policy's count.
* **Values** (`decide` over `Int`, evaluated by the kernel): spot checks of
  generated kernels in each standard space, through the instance and by name.
-/
import Tests.Codegen.Common
import Lean.Meta.Eval

open Lean Meta Elab Command
open Grassmann DirectSum StaticVectors AbstractTensors Grassmann.Kernel Grassmann.Kernel.Codegen

namespace CodegenTests.Dispatch

/-- A layout as a core term. -/
def layoutExpr : Layout → Expr
  | .chain g => mkApp (mkConst ``Layout.chain) (mkNatLit g)
  | .even => mkConst ``Layout.even
  | .odd => mkConst ``Layout.odd
  | .full => mkConst ``Layout.full

/-- An operation as a core term. -/
def opExpr : KOp → Expr
  | .bin op => mkConst (Name.str ``BinOp (opTag (.bin op)))
  | .un op => mkConst (Name.str ``UnOp (opTag (.un op)))

private unsafe def evalBundleUnsafe (e : Expr) : MetaM TensorBundle :=
  evalExpr TensorBundle (mkConst ``TensorBundle) e

@[implemented_by evalBundleUnsafe]
private opaque evalBundle (e : Expr) : MetaM TensorBundle

/-- `verify_kernel_dispatch name : V`: check that the `Kernels V` instance dispatches every
kernel specification of `V` to its generated kernel, and declare `name : Nat` as the
number of specifications checked (an error lists the failures). -/
syntax (name := verifyDispatch) "verify_kernel_dispatch " ident " : " term : command

@[command_elab verifyDispatch] def elabVerifyDispatch : CommandElab
  | `(verify_kernel_dispatch $name : $t) => do
    let count ← liftTermElabM do
      let Ve ← Term.elabTermEnsuringType t (mkConst ``TensorBundle)
      Term.synthesizeSyntheticMVarsNoPostponing
      let Ve ← instantiateMVars Ve
      let V ← evalBundle Ve
      let some pre := registered? (← getEnv) V | throwError "{V} has no generated kernels"
      let inst ← synthInstance (mkApp (mkConst ``Kernels) Ve)
      let int := mkConst ``Int
      let coeffInt ← synthInstance (mkApp (mkConst ``Coeff) int)
      let P := mkApp2 (mkConst ``Coeff.packed) int coeffInt
      let vals (l : Layout) : Expr :=
        mkApp3 (mkConst ``Values [0]) int P
          (mkApp2 (mkConst ``Layout.size) (mkApp (mkConst ``TensorBundle.n) Ve) (layoutExpr l))
      let isKernel (n : Name) : Bool := n.getPrefix == pre && (n.getString!.startsWith "k_")
      let mut bad : Array String := #[]
      let assigned := assignKernels pre (planAll V (Policy.default V.n))
      for (pl, kname, _) in assigned do
        let s := pl.spec
        let k := s.key
        let ok ← withLocalDeclD `x (vals k.la) fun x => withLocalDeclD `y (vals k.lb) fun y => do
          let head := match s.field with
            | .bin => mkApp6 (mkConst ``Kernels.bin) Ve inst int coeffInt (opExpr k.op) (layoutExpr k.la)
            | .binProj => mkApp6 (mkConst ``Kernels.binProj) Ve inst int coeffInt (opExpr k.op) (layoutExpr k.la)
            | .un => mkApp6 (mkConst ``Kernels.un) Ve inst int coeffInt (opExpr k.op) (layoutExpr k.la)
          let e := match s.field with
            | .un => mkApp2 head (layoutExpr k.lc) x
            | _ => mkApp4 head (layoutExpr k.lb) (layoutExpr k.lc) x y
          let r ← withCanUnfoldPred (fun cfg info => if isKernel info.name then pure false
              else canUnfoldDefault cfg info) (whnf e)
          return r.isAppOf kname
        unless ok do bad := bad.push s!"{fieldTag s.field} {opTag k.op} {layoutTag k.la} {layoutTag k.lb} {layoutTag k.lc}"
      -- the fused sandwiches
      let sinst ← synthInstance (mkApp (mkConst ``SandwichKernels) Ve)
      let sps := planSandwiches V
      for sp in sps do
        let kname := sandwichName pre sp
        let ok ← withLocalDeclD `r (vals sp.lr) fun r => withLocalDeclD `x (vals sp.lx) fun x => do
          let f := if sp.shift then ``SandwichKernels.tsandwich else ``SandwichKernels.sandwich
          let e := mkAppN (mkConst f) #[Ve, sinst, int, coeffInt, layoutExpr sp.lr, layoutExpr sp.lx, r, x]
          let r ← withCanUnfoldPred (fun cfg info => if isKernel info.name then pure false
              else canUnfoldDefault cfg info) (whnf e)
          return r.isAppOf kname
        unless ok do bad := bad.push s!"{if sp.shift then ">>>" else "⊘"} {layoutTag sp.lr} {layoutTag sp.lx}"
      unless bad.isEmpty do
        throwError "{bad.size} of {assigned.size + sps.size} specifications of {V} do not dispatch to their kernel: {bad.toList.take 20}"
      return assigned.size + sps.size
    elabCommand (← `(/-- Number of kernel specifications whose dispatch was verified at compile time. -/
      def $name : Nat := $(quote count)))
  | _ => throwUnsupportedSyntax

verify_kernel_dispatch dispatchedR2 : ℝ2
verify_kernel_dispatch dispatchedR3 : ℝ3
verify_kernel_dispatch dispatchedR4 : ℝ4
verify_kernel_dispatch dispatchedSTA : STA
verify_kernel_dispatch dispatchedPGA2 : PGA2
verify_kernel_dispatch dispatchedPGA3 : PGA3
verify_kernel_dispatch dispatchedCGA2 : CGA2
verify_kernel_dispatch dispatchedCGA3 : CGA3

/-! ## Kernel-evaluated spot checks (`decide`, `Int`) -/

/-- `(e₁ + 2e₂ + 3e₃)(4e₁ + 5e₂ + 6e₃) = 32 - 3e₁₂ - 6e₁₃ - 3e₂₃` in `ℝ3`, through the dispatch. -/
example : (Kernels.bin (V := ℝ3) (α := Int) .mul (.chain 1) (.chain 1) .even
    ⟨#[1, 2, 3], rfl⟩ ⟨#[4, 5, 6], rfl⟩).toList = [32, -3, -6, -3] := by decide

/-- The same vectors' wedge `-3e₁₂ - 6e₁₃ - 3e₂₃` and contraction `32`. -/
example : (Kernels.bin (V := ℝ3) (α := Int) .wedge (.chain 1) (.chain 1) (.chain 2)
    ⟨#[1, 2, 3], rfl⟩ ⟨#[4, 5, 6], rfl⟩).toList = [-3, -6, -3] := by decide
example : (Kernels.bin (V := ℝ3) (α := Int) .contraction (.chain 1) (.chain 1) (.chain 0)
    ⟨#[1, 2, 3], rfl⟩ ⟨#[4, 5, 6], rfl⟩).toList = [32] := by decide

/-- `e₁₂ e₁₂ = -1` and `e₁ e₂₃ = e₁₂₃` by name: the `ℝ3` multivector product
(storage `1, e₁, e₂, e₃, e₁₂, e₁₃, e₂₃, e₁₂₃`). -/
example : (Grassmann.Kernel.Gen.ℝ3.k_bin_mul_f_f_f (α := Int)
    ⟨#[0, 0, 0, 0, 1, 0, 0, 0], rfl⟩ ⟨#[0, 0, 0, 0, 1, 0, 0, 0], rfl⟩).toList =
    [-1, 0, 0, 0, 0, 0, 0, 0] := by decide
example : (Grassmann.Kernel.Gen.ℝ3.k_bin_mul_f_f_f (α := Int)
    ⟨#[0, 1, 0, 0, 0, 0, 0, 0], rfl⟩ ⟨#[0, 0, 0, 0, 0, 0, 1, 0], rfl⟩).toList =
    [0, 0, 0, 0, 0, 0, 0, 1] := by decide

/-- Reverse and Hodge of `1 + e₁ + e₁₂ + e₁₂₃` in `ℝ3`. -/
example : (Kernels.un (V := ℝ3) (α := Int) .reverse .full .full
    ⟨#[1, 1, 0, 0, 1, 0, 0, 1], rfl⟩).toList = [1, 1, 0, 0, -1, 0, 0, -1] := by decide
example : (Kernels.un (V := ℝ3) (α := Int) .complementrighthodge (.chain 1) (.chain 2)
    ⟨#[1, 0, 0], rfl⟩).toList = [0, 0, 1] := by decide

/-- `STA`: `γ₀² = -1`, `γ₁² = +1` (signature `-+++`). -/
example : (Kernels.bin (V := STA) (α := Int) .mul (.chain 1) (.chain 1) .even
    ⟨#[1, 0, 0, 0], rfl⟩ ⟨#[1, 0, 0, 0], rfl⟩).toList = [-1, 0, 0, 0, 0, 0, 0, 0] := by decide
example : (Kernels.bin (V := STA) (α := Int) .mul (.chain 1) (.chain 1) .even
    ⟨#[0, 1, 0, 0], rfl⟩ ⟨#[0, 1, 0, 0], rfl⟩).toList = [1, 0, 0, 0, 0, 0, 0, 0] := by decide

/-- `PGA3`: the degenerate generator squares to zero, the others to one. -/
example : (Kernels.bin (V := PGA3) (α := Int) .contraction (.chain 1) (.chain 1) (.chain 0)
    ⟨#[1, 2, 0, 0], rfl⟩ ⟨#[1, 3, 0, 0], rfl⟩).toList = [6] := by decide

/-- `CGA3`: `v∞ v∅ = -1 + v∞∅` (the `basis!` test's value). -/
example : (Kernels.bin (V := CGA3) (α := Int) .mul (.chain 1) (.chain 1) .even
    ⟨#[1, 0, 0, 0, 0], rfl⟩ ⟨#[0, 1, 0, 0, 0], rfl⟩).toList.take 2 = [-1, 1] := by decide

end CodegenTests.Dispatch
