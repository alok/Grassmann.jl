/-
Elaboration-time kernel generation: Lean's `@generated` (DESIGN.md §5.2).

`grassmann_kernels V` evaluates the space `V` at elaboration time, plans every
kernel the emission policy selects (`Grassmann.Kernel.Codegen.Plans`), emits each
as a straight-line `@[specialize]` definition generic over `[Coeff α]`
(`Grassmann.Kernel.Codegen.Emit`), and declares a `Kernels V` instance whose
dispatch covers those shapes and falls back to the reference kernels for the
rest. `basis!` runs it for spaces with at most 6 generators
(`Grassmann.Basis`; opt out with `basis! (kernels := false) V` or
`set_option grassmann.basis.kernels false`).

```lean
namespace MyKernels
grassmann_kernels S!"++-+"      -- declares MyKernels.«⟨++-+⟩».* and a Kernels instance
end MyKernels
```

The declarations go to `<current namespace>.<name>`, where `<name>` is the
identifier `V` if it is one (`grassmann_kernels ℝ3` → `….ℝ3`) and the display of
the space otherwise; the instance is `<prefix>.instKernels` and has default
priority, so it wins over the low-priority `Kernels.reference` (and a later
user instance of the same space wins over it). A process-wide registry
(`kernelRegistry`) records the spaces that have kernels; a second
`grassmann_kernels`/`basis!` for a registered space does nothing.

Generated kernels for the standard spaces (`ℝ2`, `ℝ3`, `ℝ4`, `STA`, `PGA2`,
`PGA3`, `CGA2`, `CGA3`) are in `Grassmann.Kernel.Generated`.

Options: `grassmann_kernels (dense := false) (maxEntries := 1024) V` overrides
the emission policy (`Policy`): `dense` controls the `Multivector`-operand
families, `maxEntries` caps the size of a single kernel.

Tracing: `set_option trace.grassmann.codegen true` reports the kernel count, the
entry count and the time of each stage.
-/
import Grassmann.Kernel.Codegen.Sandwich
import Lean.Meta.Eval

namespace Grassmann.Kernel.Codegen

open Lean Meta Elab Command DirectSum

initialize registerTraceClass `grassmann.codegen

/-- The spaces with generated kernels, and the prefix of their declarations. -/
initialize kernelRegistry :
    SimplePersistentEnvExtension (TensorBundle × Name) (Std.HashMap TensorBundle Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (V, pre) => m.insert V pre
    addImportedFn := fun ess => ess.foldl (init := {}) fun m es =>
      es.foldl (init := m) fun m (V, pre) => m.insert V pre }

/-- The prefix of the generated kernels of `V`, if it has any. -/
def registered? (env : Environment) (V : TensorBundle) : Option Name :=
  (kernelRegistry.getState env).get? V

/-- Evaluate a `TensorBundle` term at elaboration time. -/
private unsafe def evalBundleUnsafe (t : Term) : TermElabM TensorBundle := do
  let e ← Term.elabTermEnsuringType t (mkConst ``DirectSum.TensorBundle)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  evalExpr TensorBundle (mkConst ``DirectSum.TensorBundle) e

@[implemented_by evalBundleUnsafe]
private opaque evalBundle (t : Term) : TermElabM TensorBundle

/-- Emit the kernels of the space `V` (denoted by the term `t`) under the prefix `pre`,
unless `V` already has kernels. -/
def generateKernels (t : Term) (V : TensorBundle) (pre : Name) (pol : Policy) : CommandElabM Unit := do
  if (registered? (← getEnv) V).isSome then return
  if V.n > 12 then throwError m!"grassmann_kernels: {V} has {V.n} generators (at most 12)"
  let t0 ← IO.monoMsNow
  let spaceId := mkIdent (`_root_ ++ pre ++ `space)
  elabCommand (← `(/-- The space of these generated kernels. -/ abbrev $spaceId : DirectSum.TensorBundle := $t))
  let planned := planAll V pol
  let t1 ← IO.monoMsNow
  let valueId := mkIdent (`_root_ ++ pre ++ `spaceValue)
  elabCommand (← `(/-- The space of these generated kernels as a run-time constant (never inlined,
    so the fallback kernels read one shared value). -/ @[noinline] def $valueId : DirectSum.TensorBundle :=
      $(mkCIdent (pre ++ `space))))
  let em ← emitSpace V (mkCIdent (pre ++ `space)) (mkCIdent (pre ++ `spaceValue)) pre planned
  let sw ← emitSandwiches V (mkCIdent (pre ++ `space)) pre
  let t2 ← IO.monoMsNow
  modifyEnv (kernelRegistry.addEntry · (V, pre))
  trace[grassmann.codegen] "{V}: {em.kernels} kernels, {em.entries} entries, {sw} fused sandwiches; \
    plans {t1 - t0} ms, emission and compilation {t2 - t1} ms"

/-- `grassmann_kernels V`: generate straight-line kernels and a `Kernels V` instance for
the space `V` (DESIGN.md §5.2). Optional `(dense := false)` and `(maxEntries := n)`
override the emission policy. -/
syntax (name := kernelsCmd) "grassmann_kernels "
  (atomic("(" &"dense" " := ") ident ")")? (atomic("(" &"maxEntries" " := ") num ")")? term : command

/-- The declaration prefix for the space term `t`: the current namespace and the
identifier, or the display of the space. -/
def prefixFor (t : Term) (V : TensorBundle) : CommandElabM Name := do
  let base := match t.raw with
    | .ident _ _ nm _ => Name.mkSimple nm.toString
    | _ => Name.mkSimple (toString V)
  return (← getCurrNamespace) ++ base

@[command_elab kernelsCmd] def elabKernels : CommandElab
  | `(grassmann_kernels $[(dense := $d)]? $[(maxEntries := $m)]? $t) => do
    let V ← liftTermElabM (evalBundle t)
    let mut pol := Policy.default V.n
    if let some d := d then
      match d.getId with
      | `true => pol := { pol with dense := true }
      | `false => pol := { pol with dense := false }
      | _ => throwErrorAt d "expected `true` or `false`"
    if let some m := m then pol := { pol with maxEntries := m.getNat }
    generateKernels t V (← prefixFor t V) pol
  | _ => throwUnsupportedSyntax

end Grassmann.Kernel.Codegen
