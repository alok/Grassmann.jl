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

namespace Tests.Golden

/-- An optional compiled glob (for writing match tables in Lean). -/
def glob? (s : String) : Option Glob := some (Glob.compile s)

/-- Julia defects not (yet) in `oracle/defects.toml`. -/
def pendingDefects : DefectTable := ⟨#[
  { id := "grade-couple-coefficient", policy := .skip,
    title := "grade(z::Couple, grade(B)) returns the bare coefficient imagvalue(z) (a Number) \
      instead of im·B; grade(z::PseudoCouple, grade(B)) and grade(z, mdims(V)) likewise return \
      realvalue(z) / imagvalue(z) instead of re·B / im·I",
    source := "Grassmann.jl src/multivectors.jl:670, :697",
    correct := "imaginary(z) for a Couple; Single(realvalue(z), B) and imagvalue(z)·I for a \
      PseudoCouple (the grade projection of the Multivector path)",
    tables := #[{ suite := glob? "unary", op := glob? "grade:1|grade:2|grade:3|grade:4|grade:5|grade:6|grade:7|grade:8",
                  out := glob? "Number", kinds := some #[KindPat.compile "Couple|PseudoCouple"] }] }
]⟩

end Tests.Golden
