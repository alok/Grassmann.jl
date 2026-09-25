import Tests.Wilkinson.Util

/-!
The REDUCE emulation against REDUCE itself (`oracle/golden/wilkinson/reduce.json`:
~440 polynomials through `rcall(e, :expand/:horner/:factor)` with
`Reduce.Rational(false)`, and Wilkinson's `polyfactors`/`polyhorner`/`polyexpand`
on random coefficient lists, plus the `Reduce.Algebra` edge lists of `algebra.json`). Trees
must be identical, since `exprval` and the Stieltjes bound see the tree.
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
  -- SyntaxTree on REDUCE's Int128/BigInt literals
  for c in jArr (jGet j "wide") do
    let e := jExpr (jGet c "expr")
    let name := s!"wide[{jExprStr (jGet c "expr")}]"
    checkEq s!"{name}.callcount" (SyntaxTree.callcount e) (jNat (jGet c "callcount"))
    let (v, _, mal, a, p) := SyntaxTree.exprval e
    let ev := jArr (jGet c "exprval")
    check s!"{name}.exprval" (sameFloat v (jFloat ev[0]!) && sameFloat mal (jFloat ev[2]!) &&
      sameFloat a (jFloat ev[3]!) && sameFloat p (jFloat ev[4]!))
    checkEq s!"{name}.sub64" (SyntaxTree.sub .f64 e).toJulia (jStr (jGet c "sub64"))
    checkEq s!"{name}.abs" (SyntaxTree.abs e).toJulia (jStr (jGet c "abs"))
  for c in jArr (jGet j "polyfactors") do
    let want := jExpr (jGet c "out")
    let got := Reduce.polyfactors (jLits (jGet c "a"))
    check s!"polyfactors[{jExprStr (jGet c "out")}]" (got == want) s!"got {got.toJulia}"
  -- Julia's `Reduce.Algebra` shapes, one `off exp` REDUCE call per operation (`Reduce.Alg`),
  -- here and on the edge lists of `oracle/golden/wilkinson/algebra.json`
  let alg ← loadJson "oracle/golden/wilkinson/algebra.json"
  for src in [j, alg] do
    for (key, f) in [("polyhorner", Reduce.polyhorner), ("polyexpand", Reduce.polyexpand)] do
      for c in jArr (jGet src key) do
        let want := jExpr (jGet c "out")
        let got := f (jLits (jGet c "a"))
        check s!"{key}[{(jArr (jGet c "a")).toList.map Json.compress}]" (got == want)
          s!"got {got.toJulia}, expected {want.toJulia}"

/-- Complete factorization over `ℤ` against REDUCE (`oracle/golden/wilkinson/factor.json`,
`oracle/wilkinson/factor.jl`): products of irreducible factors of degree `≥ 2`, Swinnerton-Dyer
polynomials and cyclotomic products, which only the Berlekamp–Zassenhaus stage can split. -/
def factorSuite : TestM Unit := do
  let j ← loadJson "oracle/golden/wilkinson/factor.json"
  for c in jArr (jGet j "cases") do
    let e := jExpr (jGet c "input")
    let want := jExpr (jGet c "factor")
    let got := Reduce.factor e
    check s!"factor[{jExprStr (jGet c "input")}]" (got == want) s!"got {got.toJulia}, expected {want.toJulia}"
  -- the modular pieces on their own
  let sd3 : Array Int := #[576, 0, -960, 0, 352, 0, -40, 0, 1]
  checkEq "S₃ is irreducible" (Zassenhaus.factorSquareFree sd3).length 1
  check "S₃ splits mod 7 into ≥ 4 factors" ((Fp.berlekamp 7 (Fp.ofZ 7 sd3)).length ≥ 4)
  -- Berlekamp's factors multiply back to the monic input mod p
  for p in [3, 5, 7, 11, 101] do
    let f := Fp.monic p (Fp.ofZ p (Zassenhaus.mulZ #[1, 1, 0, 0, 1] #[2, 0, 0, -1, 1]))
    let us := Fp.berlekamp p f
    checkEq s!"berlekamp mod {p} multiplies back" (us.foldl (Fp.mul p) #[1]) f

end Tests.Wilkinson.ReduceForms
