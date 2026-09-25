import Lean.Elab.Command
import FieldAlgebra.Ring
import FieldAlgebra.Values

/-!
# `group!`, `group2!`, `constgroup!`, `ring!`: declaring a named basis

Julia's `@group`, `@group2`, `@constgroup` and `@ring` (`FieldAlgebra.jl:663-737`)
declare a named basis and bind its generators:

```lean
ring! xyz x y z          -- `xyz : Basis`, `x y z : Ring xyz` (Julia `@ring xyz x y z`)
group! XYZ x y z w       -- `x y z w : Group XYZ` (Julia `@group2 XYZ x y z w`)
group! Phys (kB := 1.380649e-23) (two := 2) (τ ≡ 6.283185307179586)
```

With values (every generator `(name := value)` or `(name ≡ value)`), the command
also emits a `GroupValues` instance, which gives `GroupValues.product`
(`float(g)`), `factorize` and the ` = value` display (`FieldAlgebra.Values`).
Generators whose value is an integer literal (`2`, or an integral scientific
literal such as `1e3`) are Julia's integer generators (`checkint2`): they are
evaluated as `float(p)^e` in the integer factor of `product` and stripped by
`factorize`; `≡` generators are stripped from non-integral floats (`τ ≡ 2π`).

Julia's `@group` wraps each generator in a `FieldConstants.Constant`, which only
changes Julia's dispatch; here `group!`, `group2!` and `constgroup!` all bind
plain `Group` values. Generator names are identifiers; use `«2»` for Julia's
numeric names (displayed `2`).
-/

namespace FieldAlgebra.Command

open Lean Elab Command

/-- A generator of `group!`/`ring!`: a name, `(name := value)`, or `(name ≡ value)`. -/
declare_syntax_cat fa_gen
/-- A generator without a value. -/
syntax ident : fa_gen
/-- A generator with a numeric value. -/
syntax "(" ident " := " term ")" : fa_gen
/-- A generator with a value that `factorize` strips from floats (Julia `τ ≡ 2π`). -/
syntax "(" ident " ≡ " term ")" : fa_gen

/-- Julia `@group2 Name gens…`: a basis and one `Group` per generator. -/
syntax (name := group2Cmd) "group2! " ident (ppSpace fa_gen)+ : command
/-- Julia `@group Name gens…` (here the same as `group2!`). -/
syntax (name := groupCmd) "group! " ident (ppSpace fa_gen)+ : command
/-- Julia `@constgroup Name gens…` (here the same as `group2!`). -/
syntax (name := constgroupCmd) "constgroup! " ident (ppSpace fa_gen)+ : command
/-- Julia `@ring Name gens…`: a basis and one one-term `Ring` per generator. -/
syntax (name := ringCmd) "ring! " ident (ppSpace fa_gen)+ : command

/-- A parsed generator. -/
structure Gen where
  /-- the binding -/
  id : Ident
  /-- the value, if any -/
  val : Option Term := none
  /-- declared with `≡` -/
  divisor : Bool := false

/-- Parse one generator. -/
def parseGen (g : TSyntax `fa_gen) : CommandElabM Gen :=
  match g with
  | `(fa_gen| $id:ident) => pure { id }
  | `(fa_gen| ($id:ident := $v)) => pure { id, val := some v }
  | `(fa_gen| ($id:ident ≡ $v)) => pure { id, val := some v, divisor := true }
  | _ => throwErrorAt g "unexpected generator syntax"

/-- The integer an integer literal (or integral scientific literal) denotes
(Julia `checkint2` on the macro's syntax). -/
def intLiteral? (t : Term) : Option Nat :=
  match t.raw.isNatLit? with
  | some n => some n
  | none => match t.raw.isScientificLit? with
    | some (m, true, e) => if m % 10 ^ e == 0 then some (m / 10 ^ e) else none
    | some (m, false, e) => some (m * 10 ^ e)
    | none => none

/-- A doc comment `/-- s -/` as syntax. -/
def docComment (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (" " ++ s ++ " -/")]⟩

/-- Display name of a generator (`«2»` shows as `2`). -/
def genText (id : Ident) : String := id.getId.eraseMacroScopes.toString (escape := false)

/-- Elaborate `group!`/`ring!`. -/
def elabDecl (ring : Bool) (name : Ident) (gs : Array (TSyntax `fa_gen)) : CommandElabM Unit := do
  let gens ← gs.mapM parseGen
  let texts := gens.map (genText ·.id)
  let n := gens.size
  let charNames := texts.all (·.length == 1)
  let nameStr := name.getId.eraseMacroScopes.toString (escape := false)
  let textStx : Array Term := texts.map fun t => quote t
  elabCommand (← `(command|
    /-- A named basis (Julia `@group`/`@ring`). -/
    def $name : FieldAlgebra.Basis :=
      { name := $(quote nameStr), n := $(quote n), text := #[$textStx,*], charNames := $(quote charNames) }))
  for h : i in [0:n] do
    let g := gens[i]
    let doc := docComment s!"The generator `{texts[i]!}` of `{nameStr}`."
    if ring then
      elabCommand (← `(command| $doc:docComment def $(g.id) : FieldAlgebra.Ring $name :=
        FieldAlgebra.Ring.ofGroup (FieldAlgebra.Group.gen ⟨$(quote i), by decide⟩)))
    else
      elabCommand (← `(command| $doc:docComment def $(g.id) : FieldAlgebra.Group $name :=
        FieldAlgebra.Group.gen ⟨$(quote i), by decide⟩))
  let valued := gens.filter (·.val.isSome)
  if valued.isEmpty then return
  if valued.size != n then
    throwErrorAt name "either every generator has a value or none does (Julia `valbols`)"
  let vals ← gens.mapM fun g => do
    let some v := g.val | unreachable!
    match intLiteral? v with
    | some p => `(FieldAlgebra.GenValue.prime $(quote p))
    | none => `(FieldAlgebra.GenValue.const ($v : Float))
  let divs ← (gens.zipIdx.filter (·.1.divisor)).mapM fun (g, i) => do
    let some v := g.val | unreachable!
    `(($(quote i), ($v : Float)))
  elabCommand (← `(command|
    /-- The generator values of the basis (Julia `@group … begin a = v … end`). -/
    instance : FieldAlgebra.GroupValues $name := ⟨#[$vals,*], #[$divs,*]⟩))

/-- Julia `@group2`. -/
@[command_elab group2Cmd] def elabGroup2 : CommandElab
  | `(group2! $name:ident $gs*) => elabDecl false name gs
  | _ => throwUnsupportedSyntax

/-- Julia `@group`. -/
@[command_elab groupCmd] def elabGroup : CommandElab
  | `(group! $name:ident $gs*) => elabDecl false name gs
  | _ => throwUnsupportedSyntax

/-- Julia `@constgroup`. -/
@[command_elab constgroupCmd] def elabConstgroup : CommandElab
  | `(constgroup! $name:ident $gs*) => elabDecl false name gs
  | _ => throwUnsupportedSyntax

/-- Julia `@ring`. -/
@[command_elab ringCmd] def elabRing : CommandElab
  | `(ring! $name:ident $gs*) => elabDecl true name gs
  | _ => throwUnsupportedSyntax

end FieldAlgebra.Command
