/-
`basis!`: Julia's `@basis` (DirectSum.jl `src/basis.jl:57-132`,
port-notes/grassmann-types.md §4.11; DESIGN.md §4.5).

`basis! S!"∞∅+++"` declares, in the current namespace,

* `V : TensorBundle`, the space (an `abbrev`, so instances keyed on it unfold);
* `v : Submanifold V 0`, the unit scalar (Julia `One(V)`);
* every basis blade under its Julia display name, `v₁ v₂ … v₁₂ … v₁₂₃` (with
  `«v∞» «v∅» «v∞∅₁»` for the conformal null generators and `«w¹»` for
  covectors, which need guillemets), each a `Submanifold V G`;
* ASCII aliases from Julia's labels, `v1 v12 v123`, with `∞ ↦ inf` and
  `∅ ↦ o` (`vinf`, `vo`, `vinfo1`); an alias that would repeat a name already
  declared (possible for `n ≥ 10`, where Julia's labels are ambiguous) is skipped.

Julia's `@basis` also binds `v⃖` to the *string* `"v"` (defect `misc-types`) and
`𝟎`/`∞`; those are not declared. The generated-kernel emission DESIGN.md §5.2
attaches to `basis!` belongs to the code-generation stage. Spaces with more than
10 generators are rejected (1024 declarations).
-/
import Grassmann.Types.Single
import Lean.Elab.Command
import Lean.Meta.Eval

namespace Grassmann

open Lean Elab Command DirectSum

/-- `basis! V`: declare the space `V`, its unit scalar `v` and every basis blade
(Julia `@basis V`). -/
syntax (name := basisCmd) "basis! " term : command

/-- Evaluate a `TensorBundle` term at elaboration time. -/
private unsafe def evalBundleUnsafe (t : Term) : TermElabM TensorBundle := do
  let e ← Term.elabTermEnsuringType t (mkConst ``DirectSum.TensorBundle)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  Meta.evalExpr TensorBundle (mkConst ``DirectSum.TensorBundle) e

@[implemented_by evalBundleUnsafe]
private opaque evalBundle (t : Term) : TermElabM TensorBundle

/-- The ASCII alias of a blade label: Julia's label with `∞ ↦ inf`, `∅ ↦ o`. -/
def asciiAlias (label : String) : String :=
  (label.replace "∞" "inf").replace "∅" "o"

/-- Elaborate `basis! V`: evaluate `V`, then declare the space, the blades and the aliases. -/
@[command_elab basisCmd] def elabBasis : CommandElab
  | `(basis! $t) => do
    let V ← liftTermElabM (evalBundle t)
    if V.n > 10 then
      throwError m!"basis!: {V.n} generators would declare {toString (2 ^ V.n)} blades (at most 10 generators)"
    let vId := mkIdent `V
    elabCommand (← `(/-- The space declared by `basis!`. -/ abbrev $vId : DirectSum.TensorBundle := $t))
    let mut declared : Std.HashSet String := {"V"}
    for b in Leibniz.indexBasisAll V.n do
      let g := Bits.popcount b
      let pretty := V.bladeLabel b
      let id := mkIdent (Name.mkSimple pretty)
      let gLit := Syntax.mkNumLit (toString g)
      let bLit := Syntax.mkNumLit (toString b.toNat)
      elabCommand (← `(/-- A basis blade declared by `basis!`. -/
        def $id : DirectSum.Submanifold $vId $gLit := ⟨$bLit⟩))
      declared := declared.insert pretty
      let ascii := asciiAlias (V.bladeLabel b (label := true))
      if !declared.contains ascii then
        let aId := mkIdent (Name.mkSimple ascii)
        elabCommand (← `(/-- ASCII alias of a basis blade declared by `basis!`. -/
          abbrev $aId : DirectSum.Submanifold $vId $gLit := $id))
        declared := declared.insert ascii
      let alias := asciiAlias pretty
      if !declared.contains alias then
        let aId := mkIdent (Name.mkSimple alias)
        elabCommand (← `(/-- ASCII alias of a basis blade declared by `basis!`. -/
          abbrev $aId : DirectSum.Submanifold $vId $gLit := $id))
        declared := declared.insert alias
  | _ => throwUnsupportedSyntax

end Grassmann
