/-
The basis container `Λ(V)` (Julia `Basis`, `SparseBasis`, `ExtendedBasis`,
`DirectSum.jl src/basis.jl:1-202, 345-458`) and its syntax.

* `Λ(V)`: the basis of the space `V` (`DirectSum.Basis V`). It prints as
  Julia's `show(Λ(V))` (`DirectSum.Basis{⟨+++⟩,8}(v, v₁, …)`, the sparse and
  extended forms beyond `n = 8` and `n = 22`), and `Λ(V)[i]` is its `i`-th
  blade in basis order (1-based, as Julia: `Λ(3)[5] = v₁₂`). `Λ(3)` (a numeral)
  is the basis of Julia's `Int` space `ℝ3`, `Λ(n, d, o, s)` that of
  `Signature(n, d, o, s)`.
* `Λ(V).name`: the blade named `name`, resolved while elaborating, so the
  result is typed: a unit blade `Submanifold V G` (`Λ(ℝ^3).v12 : Submanifold
  (ℝ^3) 2`), or, when reordering the indices gives a sign or a metric factor,
  that coefficient times the blade (`Λ(3).v21 = -1v₁₂`, `(-1 : Int) * v₁₂`, a
  `Grassmann.Single` once Grassmann is imported). Names follow
  `TensorBundle.lookup` (`v`, `v12`, `v21`, `w¹`-style `w12`, `∂1v2`,
  `v32a87Ng`); names with `∞`/`∅`, which are not Lean identifiers, are written
  with guillemets: `Λ(S!"∞∅+").«v∞∅1»`. `V` must be a closed term. A name that
  is not a blade name is an ordinary projection of the basis (`Λ(V).dual`).
* `Λ!"+++"`: Julia `Λ"+++"` (`@Λ_str`), the basis of `S!"+++"`.
* `Λ(V)′` and `Λ(V) ⊕ Λ(W)` are the bases of `V′` and `V ⊕ W`
  (`Basis.dual`, `Basis.oplus`).
-/
import DirectSum.SetOps
import DirectSum.Names
import DirectSum.Parse
import Lean.Elab.SyntheticMVars
import Lean.Meta.Eval

namespace DirectSum

open Bits

/-- Julia `Λ(V)` (`Basis{V}`, `SparseBasis`, `ExtendedBasis`): the basis of the
space `V`, which is carried in the type. -/
structure Basis (V : TensorBundle) : Type where
  deriving DecidableEq, Repr, Inhabited

/-- Julia `Λ(V)`, `Basis(V)`: the basis of `V`. -/
def Λ (V : TensorBundle) : Basis V := ⟨⟩

namespace Basis

variable {V W : TensorBundle}

/-- Julia `show(Λ(V))` (`DirectSum.jl src/basis.jl:195-202, 345-347, 373-376`). -/
instance : ToString (Basis V) := ⟨fun _ => V.showBasis⟩

/-- The number of blades, Julia `length(Λ(V)) = 2ⁿ`. -/
def size (_ : Basis V) : Nat := 2 ^ V.n

/-- The `i`-th blade (1-based, basis order: grade-major, lexicographic within a
grade; Julia `getindex(::Basis, i)`), with its grade. -/
def get (_ : Basis V) (i : Nat) : (G : Nat) × Submanifold V G :=
  let b := Leibniz.basisAt V.n (i - 1)
  ⟨popcount b, ⟨b⟩⟩

/-- Julia `Λ(V)[i]` (1-based): `Λ(3)[5] = v₁₂`. -/
instance : GetElem (Basis V) Nat ((G : Nat) × Submanifold V G) (fun _ i => 0 < i ∧ i ≤ 2 ^ V.n) where
  getElem x i _ := x.get i

/-- Julia `Λ(V)'`: the basis of the dual space. -/
def dual (_ : Basis V) : Basis V.dual := ⟨⟩

/-- Julia `Λ(V) ⊕ Λ(W)`: the basis of the direct sum (`Λ(ℝ^14) ⊕ Λ(ℝ^14)'`). -/
def oplus (_ : Basis V) (_ : Basis W) : Basis (V ⊕ W) := ⟨⟩

/-- The blade named `s` (Julia `getproperty(Λ(V), s)`, `TensorBundle.lookup`),
evaluated at run time. -/
def lookup (_ : Basis V) (s : String) : Option BladeResult := V.lookup s

end Basis

/-- Display of a blade of run-time grade (the elements of `Λ(V)`). -/
instance {V : TensorBundle} : ToString ((G : Nat) × Submanifold V G) := ⟨fun ⟨_, b⟩ => toString b⟩

/-! ## Syntax -/

/-- `Λ(V)`: the basis of `V` (Julia `Λ(V)`); `Λ(3)` is the basis of the `Int`
space `ℝ3`, `Λ(n, d, o, s)` that of `Signature(n, d, o, s)`. -/
syntax:max (name := basisLit) "Λ(" term,+ ")" : term

/-- `Λ(V).name`: the blade (or scaled blade) named `name`, resolved while
elaborating (Julia `Λ(V).v12`). -/
syntax:max (name := basisBlade) "Λ(" term,+ ")" noWs "." noWs ident : term

/-- `Λ!"+++"`: the basis of `S!"+++"` (Julia `Λ"+++"`, `@Λ_str`). -/
syntax:max (name := basisStr) "Λ!" str : term

namespace BasisSyntax

open Lean Elab Term Meta

/-- The space term of `Λ(args…)`: a numeral is Julia's `Int` space, four
arguments are `Signature(n, d, o, s)`, anything else is a `TensorBundle`. -/
def spaceTerm (args : Array Term) : MacroM Term := do
  match args with
  | #[n] =>
    match n.raw.isNatLit? with
    | some _ => `(DirectSum.TensorBundle.euclidean $n)
    | none => pure n
  | #[n, d, o, s] =>
    `(DirectSum.TensorBundle.ofCode $n ($d != 0) ($o != 0) (($s : Nat).toUInt64))
  | _ => Macro.throwError "Λ(…) takes a space, a numeral, or (n, d, o, s)"

macro_rules
  | `(Λ( $args,* )) => do `(DirectSum.Λ $(← spaceTerm args.getElems))
  | `(Λ! $s:str) => `(DirectSum.Λ (S! $s:str))

/-- Evaluate a closed `TensorBundle` expression at elaboration time. -/
private unsafe def evalBundleUnsafe (e : Expr) : TermElabM TensorBundle :=
  Meta.evalExpr TensorBundle (mkConst ``DirectSum.TensorBundle) e

@[implemented_by evalBundleUnsafe]
private opaque evalBundle (e : Expr) : TermElabM TensorBundle

/-- The components of a (possibly `«»`-quoted, dotted) identifier: `v12.indices`
is the blade `v12` followed by the projection `.indices`. -/
private def components (n : Name) : List String :=
  n.eraseMacroScopes.components.map fun
    | .str _ s => s
    | c => c.toString

/-- A coefficient as an `Int` literal when integral, else a `Rat` expression. -/
private def coeffTerm (c : Rat) : MacroM Term := do
  let lit := Syntax.mkNumLit (toString c.num.natAbs)
  let base ← if c.den == 1 then `(($lit : Int))
    else `((($lit : Rat) / ($(Syntax.mkNumLit (toString c.den)) : Rat)))
  if c.num < 0 then `((-$base)) else pure base

@[term_elab basisBlade] def elabBasisBlade : TermElab := fun stx expectedType? => do
  match stx with
  | `(Λ( $args,* ).$name) =>
    let spaceStx ← liftMacroM (spaceTerm args.getElems)
    let Ve ← elabTermEnsuringType spaceStx (mkConst ``DirectSum.TensorBundle)
    synthesizeSyntheticMVarsNoPostponing
    let Ve ← instantiateMVars Ve
    if Ve.hasFVar || Ve.hasMVar then
      throwErrorAt stx "Λ(V).name needs a closed space V (it is resolved while elaborating)"
    let V ← evalBundle Ve
    let (s, projs) := match components name.getId with
      | s :: rest => (s, rest)
      | [] => ("", [])
    let some r := V.lookup s |
      -- not a blade name: an ordinary projection of the basis value (`Λ(V).dual`)
      elabTerm (← `((DirectSum.Λ $spaceStx).$name)) expectedType?
    let blade := fun (b : UInt64) =>
      mkApp3 (mkConst ``DirectSum.Submanifold.mk) Ve (toExpr (popcount b)) (toExpr b)
    let term ← match r with
      | .blade b => exprToSyntax (blade b)
      | .single c b => do
        let bs ← exprToSyntax (blade b)
        let cs ← liftMacroM (coeffTerm c)
        `(($cs * $bs))
      | .zero => do
        let bs ← exprToSyntax (blade 0)
        `(((0 : Int) * $bs))
      | _ => throwErrorAt name
          "{s} is not a single term in {V} (the product of its generators is {repr r})"
    let term ← projs.foldlM (init := term) fun t p => `($t.$(mkIdent (Name.mkSimple p)))
    elabTerm term expectedType?
  | _ => throwUnsupportedSyntax

end BasisSyntax

end DirectSum
