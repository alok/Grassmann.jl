import Tests.Wilkinson.Util

/-!
SyntaxTree against Julia (`oracle/golden/wilkinson/exprval.json`, ~600 random
polynomial expressions): parsing and printing of `Expr`s, `callcount`,
`expravg`, `exprval` (bit for bit: the logarithms are Julia's own), and the
`sub`/`abs`/`alg` rewrites (compared as Julia's `string(expr)`).
-/

open Lean Wilkinson Wilkinson.SyntaxTree Tests.Golden

namespace Tests.Wilkinson.Exprval


/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/exprval.json"
  for c in jArr (jGet j "cases") do
    let rec_ := jGet c "expr"
    let e := jExpr rec_
    let s := jExprStr rec_
    let name := s!"exprval[{s}]"
    match JExpr.parse s with
    | .ok p => check s!"{name}.parse" (p == e) s!"parsed {p.toJulia}"
    | .error m => check s!"{name}.parse" false m
    checkEq s!"{name}.string" e.toJulia s
    checkEq s!"{name}.callcount" (callcount e) (jNat (jGet c "callcount"))
    let (cs, avg, cp, pavg) := expravg e
    let ea := jArr (jGet c "expravg")
    check s!"{name}.expravg" (cs == jNat ea[0]! && sameFloat avg (jFloat ea[1]!) && cp == jNat ea[2]! &&
      sameFloat pavg (jFloat ea[3]!)) s!"got ({cs}, {avg}, {cp}, {pavg})"
    let (v, cal, mal, a, p) := exprval e
    let ev := jArr (jGet c "exprval")
    check s!"{name}.exprval" (sameFloat v (jFloat ev[0]!) && cal == jNat ev[1]! && sameFloat mal (jFloat ev[2]!) &&
      sameFloat a (jFloat ev[3]!) && sameFloat p (jFloat ev[4]!)) s!"got ({v}, {cal}, {mal}, {a}, {p})"
    checkEq s!"{name}.sub64" (sub .f64 e).toJulia (jStr (jGet c "sub64"))
    checkEq s!"{name}.sub32" (sub .f32 e).toJulia (jStr (jGet c "sub32"))
    checkEq s!"{name}.abs" (SyntaxTree.abs e).toJulia (jStr (jGet c "abs"))
    checkEq s!"{name}.alg" (alg (f := jl⟪1 + ϵ⟫) e).toJulia (jStr (jGet c "alg"))

end Tests.Wilkinson.Exprval
