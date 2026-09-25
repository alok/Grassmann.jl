import Bench.Harness

/-!
# Optional suites

`optional_suite% "name" Some.Decl` is `some (IntoSuite.into "name" Some.Decl)` when `Some.Decl`
resolves in the current environment and `none` otherwise. The driver can therefore list a suite
that another module will provide later (for example `Bench.Grassmann.run`) without the build
depending on that module: the suite switches on as soon as its module is imported into
`Bench.lean`. It is a plain macro (`Macro.resolveGlobalName`), so the bench executable does not
link the Lean compiler.
-/

namespace Bench

/-- `optional_suite% "name" decl`: the suite `decl` if it exists, else `none`. -/
syntax (name := optionalSuite) "optional_suite% " str ident : term

macro_rules
  | `(optional_suite% $n:str $id:ident) => do
    let found ← Lean.Macro.resolveGlobalName id.getId
    if found.any (·.2.isEmpty) then `(some (Bench.IntoSuite.into $n $id)) else `(none)

end Bench
