import Tests.Golden.Defects

/-!
# Pending defects: Julia defects the harness found that `defects.json` lacks

The generator attributes every Julia error and every mismatch *against its reference* to a
defect (`unexplained = 0`), but it does not compare outputs that carry no dense vector (a
plain `Number`). Evaluating the goldens against DirectSum's reference semantics
(`Tests.Golden.Reference`) exposes Julia defects hiding there. They are listed here, with the
same fields and match language as `oracle/defects.toml`, until they move to that file
(integrator request) and the goldens are retagged. The runner applies their policy on top
of the committed tags and reports them separately; the committed-tag re-derivation check
ignores them.
-/

namespace Tests.ElementOracle

/-- An optional compiled glob (for writing match tables in Lean). -/
def glob? (s : String) : Option Glob := some (Glob.compile s)

/-- Julia defects not (yet) in `oracle/defects.toml`. -/
def pendingDefects : DefectTable := ⟨#[]⟩

end Tests.ElementOracle
