/-
`export_alias N => C`: make `N` (in the current namespace) another name of the
existing declaration `C`, exactly as `export` does for a same-named declaration
(`Lean.addAlias`). Name resolution, `export` from downstream namespaces and dot
notation on the alias (`N.field` when `N.field` is aliased too) all see the
original constant, so there is one declaration and no ambiguity when both names
are in scope.

Used to make AbstractTensors' `Wedge`/`Vee` the AbstractLattices classes
`HWedge`/`HVee`: Julia's `∧`/`∨` are one generic function extended by every
package (`AbstractLattices.jl src/AbstractLattices.jl:5-9`).
-/
import Lean.Elab.Command

namespace AbstractTensors

open Lean Elab Command

/-- `export_alias N => C`: declare `N` (relative to the current namespace) as an
alias of the constant `C`. -/
syntax (name := exportAlias) "export_alias " ident " => " ident : command

@[command_elab exportAlias] def elabExportAlias : CommandElab
  | `(export_alias $n => $c) => do
    let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    let name := (← getCurrNamespace) ++ n.getId
    modify fun s => { s with env := addAlias s.env name target }
  | _ => throwUnsupportedSyntax

end AbstractTensors
