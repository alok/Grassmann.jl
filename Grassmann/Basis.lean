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
`𝟎`/`∞`; those are not declared. Spaces with more than 10 generators are
rejected (1024 declarations).

## Generated kernels

For a space with at most 6 generators, `basis!` also emits the unrolled product
kernels of the space and its `Kernels` instance (DESIGN.md §4.5, §5.2; Julia's
`@generated` products run on first use, Lean's at elaboration), under
`<namespace>.kernels`, unless the space already has kernels: the standard spaces
of `Grassmann.Kernel.Generated` (`ℝ2`-`ℝ4`, `STA`, `PGA2`, `PGA3`, `CGA2`,
`CGA3`) always do. Opt out with `basis! (kernels := false) V` or
`set_option grassmann.basis.kernels false`.
-/
import Grassmann.Types.Single
import Grassmann.Kernel.Generated
import Lean.Elab.Command
import Lean.Meta.Eval

namespace Grassmann

open Lean Elab Command DirectSum

/-- Whether `basis!` emits the generated kernels of spaces with at most 6 generators. -/
register_option grassmann.basis.kernels : Bool := {
  defValue := true
  descr := "basis! emits unrolled product kernels (DESIGN.md §5.2) for spaces with n ≤ 6"
}

/-- `basis! V`: declare the space `V`, its unit scalar `v` and every basis blade
(Julia `@basis V`), and for `n ≤ 6` its generated kernels (`(kernels := false)`
opts out). `(names := E e)` names the space `E` and the blades `e₁ e₁₂ …` (aliases `e1 e12`),
Julia's `@basis V E e`; a third and fourth name replace the covector and tangent
prefixes `w`, `∂` (Julia's `cov`, `duo`). -/
syntax (name := basisCmd) "basis! " (atomic("(" &"kernels" " := ") ident ")")?
  (atomic("(" &"names" " := ") ident+ ")")? term : command

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
  | `(basis! $[(kernels := $k)]? $[(names := $ns*)]? $t) => do
    let V ← liftTermElabM (evalBundle t)
    let ns : Array Ident := ns.getD #[]
    let spaceName : Name := (ns[0]?.map (·.getId)).getD `V
    let pre := Leibniz.pre
    let names : Leibniz.Names :=
      ((ns[1]?.map (·.getId.toString)).getD pre.1,
       (ns[2]?.map (·.getId.toString)).getD pre.2.1,
       (ns[3]?.map (·.getId.toString)).getD pre.2.2.1, pre.2.2.2)
    -- Julia's labels with the prefixes renamed (the element *values* still print with the
    -- space's own prefixes, as in Julia: `e3` is `v₃`)
    let label := fun (b : UInt64) (ascii : Bool) =>
      ((((V.bladeLabel b (label := ascii)).replace "v" names.1).replace "w" names.2.1).replace
        "∂" names.2.2.1)
    let kernels ← match k with
      | none => pure (grassmann.basis.kernels.get (← getOptions))
      | some b => match b.getId with
        | `true => pure true
        | `false => pure false
        | _ => throwErrorAt b "expected `true` or `false`"
    if V.n > 10 then
      throwError m!"basis!: {V.n} generators would declare {toString (2 ^ V.n)} blades (at most 10 generators)"
    let vId := mkIdent spaceName
    elabCommand (← `(/-- The space declared by `basis!`. -/ abbrev $vId : DirectSum.TensorBundle := $t))
    let mut declared : Std.HashSet String := {spaceName.toString}
    for b in Leibniz.indexBasisAll V.n do
      let g := Bits.popcount b
      let pretty := label b false
      let id := mkIdent (Name.mkSimple pretty)
      let gLit := Syntax.mkNumLit (toString g)
      let bLit := Syntax.mkNumLit (toString b.toNat)
      elabCommand (← `(/-- A basis blade declared by `basis!`. -/
        def $id : DirectSum.Submanifold $vId $gLit := ⟨$bLit⟩))
      declared := declared.insert pretty
      let ascii := asciiAlias (label b true)
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
    if kernels && V.n ≤ 6 then
      Kernel.Codegen.generateKernels vId V ((← getCurrNamespace) ++ `kernels)
        (Kernel.Codegen.Policy.default V.n)
  | _ => throwUnsupportedSyntax

/-- `dualbasis! V`: Julia `@dualbasis V`, the basis of the dual space `V′` (covector
blades `w¹ w¹² …`, aliases `w1 w12`). -/
syntax (name := dualbasisCmd) "dualbasis! " term : command

macro_rules
  | `(dualbasis! $t) => `(basis! (DirectSum.TensorBundle.dual $t))

/-- `mixedbasis! V`: Julia `@mixedbasis V`, the basis of `V ⊕ V′` (vectors, covectors and
their mixed blades `v₁w¹ …`). -/
syntax (name := mixedbasisCmd) "mixedbasis! " term : command

macro_rules
  | `(mixedbasis! $t) => `(basis! (DirectSum.TensorBundle.oplus! $t (DirectSum.TensorBundle.dual $t)))

/-! ## Hyperplanes (Julia `hyperplanes`, `𝕚 𝕛 𝕜`) -/

/-- Julia `hyperplanes(V)` (`src/Grassmann.jl:62`): the terms `I ⟑ vₖ` for every generator
(`k < n - diffvars`), the hyperplanes orthogonal to the basis vectors; in `ℝ3`
`[1v₂₃, -1v₁₃, 1v₁₂]`, in `ℝ4` `[-1v₂₃₄, 1v₁₃₄, -1v₁₂₄, 1v₁₂₃]`. Each is a grade-`n-1` term
(its coefficient is `0` for a degenerate `I ⟑ vₖ`). -/
def hyperplanes (V : TensorBundle) : Array (Single V (V.n - 1) Int) :=
  (List.range (V.n - V.diffvars)).toArray.map fun k =>
    let e : UInt64 := (1 : UInt64) <<< k.toUInt64
    match V.apply₂ .mul (DirectSum.Bits.lowMask V.n) e with
    | .ok (.blade b) => ⟨b, 1⟩
    | .ok (.single c b) => ⟨b, c.num⟩
    | _ => ⟨DirectSum.Bits.lowMask V.n ^^^ e, 0⟩

/-- Julia `𝕚 = hyperplanes(ℝ3)[1] = v₂₃` (`src/Grassmann.jl:71`): the quaternion unit
`i` as a bivector of `ℝ3` (`𝕚 * 𝕛 = -v₁₂`… with the dynamic layer's kinds). -/
def «𝕚» {α : Type} [AbstractTensors.Coeff α] : Single ℝ3 2 α := ⟨6, AbstractTensors.Coeff.one⟩

/-- Julia `𝕛 = hyperplanes(ℝ3)[2] = -v₁₃`. -/
def «𝕛» {α : Type} [AbstractTensors.Coeff α] : Single ℝ3 2 α := ⟨5, -AbstractTensors.Coeff.one⟩

/-- Julia `𝕜 = hyperplanes(ℝ3)[3] = v₁₂`. -/
def «𝕜» {α : Type} [AbstractTensors.Coeff α] : Single ℝ3 2 α := ⟨3, AbstractTensors.Coeff.one⟩

end Grassmann
