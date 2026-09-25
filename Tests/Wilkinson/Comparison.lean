import Tests.Wilkinson.Util

/-!
`PolynomialComparison` against Julia (`oracle/golden/wilkinson/comparison.json`,
the constructor of src/polynomial.jl:42-68 run with the copied kernels and
REDUCE): driven by REDUCE's forms, the flags, the common cut-off `ω`, the
Simpson scores of the bounds and of the actual errors (`exacterr` against the
`BigFloat` optimal form), and the printed report; and the REDUCE emulation must
pick the same four forms (`optimal`, `expand`, `horner`, `factor`).
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson.Comparison

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/comparison.json"
  for c in jArr (jGet j "cases") do
    let e := jExpr (jGet c "input")
    let name := s!"comparison[{jExprStr (jGet c "input")}]"
    let fs := (jArr (jGet c "forms")).map jExpr
    let F : Forms := ⟨fs[0]!, fs[1]!, fs[2]!, fs[3]!, fs[4]!⟩
    -- the REDUCE emulation reproduces the forms REDUCE gave
    let G := Forms.ofCAS Reduce.cas e
    check s!"{name}.forms" (G.optimal == F.optimal && G.expand == F.expand && G.horner == F.horner &&
      G.factor == F.factor) s!"got {[G.optimal, G.expand, G.horner, G.factor].map JExpr.toJulia}"
    let C := PolynomialComparison.ofForms e F
    checkEq s!"{name}.extra" C.extra (jBool (jGet c "extra"))
    checkEq s!"{name}.rxtra" C.rxtra (jBool (jGet c "rxtra"))
    checkEq s!"{name}.ω" C.ω (jNat (jGet c "omega"))
    let smp := jArr (jGet c "smp")
    checkEq s!"{name}.results" C.results.size smp.size
    for (r, g) in C.results.toList.zip smp.toList do
      check s!"{name}.smp[{r.expr.toJulia}]" (sameFloat r.smp (hexF64 g)) s!"got {r.smp}, expected {hexF64 g}"
    for (r, g) in C.results.toList.zip (jArr (jGet c "exprval")).toList do
      check s!"{name}.exprval[{r.expr.toJulia}]" (sameFloat r.val.1 (jFloat g))
    let integral := jArr (jGet c "integral")
    checkEq s!"{name}.integral.size" C.integral.size integral.size
    for k in List.range (min C.integral.size integral.size) do
      check s!"{name}.integral[{k}]" (sameFloat C.integral[k]! (hexF64 integral[k]!))
        s!"got {C.integral[k]!}, expected {hexF64 integral[k]!}"
    for (E, g) in C.exact.toList.zip (jArr (jGet c "exact_sample")).toList do
      let idx := [1, 2, 100, 500, C.ω]
      for (i, h) in idx.zip (jArr g).toList do
        check s!"{name}.exacterr[{i}]" (sameFloat E[i - 1]! (hexF64 h)) s!"got {E[i - 1]!}, expected {hexF64 h}"
    checkEq s!"{name}.print" C.toJulia (jStr (jGet c "print"))

end Tests.Wilkinson.Comparison
