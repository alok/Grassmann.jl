import Tests.Wilkinson.Util

/-!
The REDUCE emulation against REDUCE itself (`oracle/golden/wilkinson/reduce.json`:
~440 polynomials through `rcall(e, :expand/:horner/:factor)` with
`Reduce.Rational(false)`, and Wilkinson's `polyfactors`/`polyhorner`/`polyexpand`
on random coefficient lists). Trees must be identical, since `exprval` and the
Stieltjes bound see the tree.
-/

open Lean Wilkinson Tests.Golden

namespace Tests.Wilkinson.ReduceForms

/-- A coefficient list `[{"int"} | {"f64"}]`. -/
def jLits (j : Json) : List Lit :=
  (jArr j).toList.map fun x =>
    match jGet x "int" with
    | .str s => .int (s.toInt?.getD 0)
    | _ => .f64 (jFloat (jGet x "f64"))

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/reduce.json"
  for c in jArr (jGet j "forms") do
    let e := jExpr (jGet c "input")
    let name := s!"reduce[{jExprStr (jGet c "input")}]"
    let ev := jArr (jGet c "exprval")
    for (mode, f, k) in [("expand", Reduce.expand, 0), ("horner", Reduce.horner, 1), ("factor", Reduce.factor, 2)] do
      let want := jExpr (jGet c mode)
      let got := f e
      check s!"{name}.{mode}" (got == want) s!"got {got.toJulia}, expected {want.toJulia}"
      match ev[k]! with
      | .str "DomainError" => pure ()
      | x => check s!"{name}.{mode}.exprval" (sameFloat (SyntaxTree.exprval got).1 (jFloat x))
    -- the three forms are the same polynomial
    let p := Poly.ofJExpr e
    check s!"{name}.equal" ([Reduce.expand e, Reduce.horner e, Reduce.factor e].all (Poly.ofJExpr · == p))
  for c in jArr (jGet j "polyfactors") do
    let want := jExpr (jGet c "out")
    let got := Reduce.polyfactors (jLits (jGet c "a"))
    check s!"polyfactors[{jExprStr (jGet c "out")}]" (got == want) s!"got {got.toJulia}"
  -- Julia's `Reduce.Algebra` shapes are not reproduced: the same polynomial, and
  -- the raw literal for a one-element list
  for (key, f) in [("polyhorner", Reduce.polyhorner), ("polyexpand", Reduce.polyexpand)] do
    for c in jArr (jGet j key) do
      let want := jExpr (jGet c "out")
      let got := f (jLits (jGet c "a"))
      let ok := match want with
        | .lit _ => got == want
        | _ => (Poly.ofJExpr got).isSome && Poly.ofJExpr got == Poly.ofJExpr want
      check s!"{key}[{jExprStr (jGet c "out")}]" ok s!"got {got.toJulia}"

end Tests.Wilkinson.ReduceForms
