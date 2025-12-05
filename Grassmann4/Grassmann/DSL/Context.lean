/-
  Grassmann/DSL/Context.lean - Algebra Context Blocks

  Provides elegant syntax for entering an algebra context:

    Cl(3,0,0) {
      let v := e₁ + e₂
      v ⊛ v
    }

  Named shortcuts:
    R3 { ... }    -- Cl(3,0,0)
    PGA3 { ... }  -- Cl(3,0,1)
    CGA3 { ... }  -- Cl(4,1,0)
    STA { ... }   -- Cl(1,3,0)

  The context block automatically binds:
  - Basis vectors: e₁, e₂, ..., eₙ (also e1, e2, ..., en)
  - Multi-index blades: e₁₂, e₁₃, e₂₃, e₁₂₃, etc.
  - The signature as `_sig`
-/
import Lean
import Grassmann.DSL.Subscript

open Lean Elab Meta Term Macro

namespace Grassmann.DSL

/-! ## Context Syntax -/

/-- Cl(p,q,r) { body } for Clifford algebra context -/
syntax "Cl(" num "," num "," num ")" "{" term "}" : term

/-- Cl(p,q) { body } shorthand (r = 0) -/
syntax "Cl(" num "," num ")" "{" term "}" : term

/-- Cl(n) { body } shorthand (q = r = 0, Euclidean) -/
syntax "Cl(" num ")" "{" term "}" : term

/-- Named algebra shortcuts -/
syntax "R3" "{" term "}" : term     -- Cl(3,0,0)
syntax "R2" "{" term "}" : term     -- Cl(2,0,0)
syntax "R4" "{" term "}" : term     -- Cl(4,0,0)
syntax "PGA2" "{" term "}" : term   -- Cl(2,0,1)
syntax "PGA3" "{" term "}" : term   -- Cl(3,0,1)
syntax "CGA2" "{" term "}" : term   -- Cl(3,1,0)
syntax "CGA3" "{" term "}" : term   -- Cl(4,1,0)
syntax "STA" "{" term "}" : term    -- Cl(1,3,0)

/-! ## Binding Generation -/

/-- Generate a single blade binding with both ASCII and subscript names.
    Takes the signature identifier to ensure consistent hygiene scope. -/
def generateBladeBinding (mask : Nat) (dim : Nat) (sigRef : TSyntax `ident) :
    MacroM (TSyntax `term → MacroM (TSyntax `term)) := do
  let asciiName := bitmaskToName mask dim
  let subscriptName := bitmaskToSubscript mask dim
  let asciiIdent := mkIdent (Name.mkSimple asciiName)
  let subscriptIdent := mkIdent (Name.mkSimple subscriptName)
  let maskLit := Syntax.mkNumLit (toString mask)
  let dimLit := Syntax.mkNumLit (toString dim)
  -- Construct names manually to bypass macro hygiene without requiring imports
  let mvType := mkIdent (Name.mkStr2 "Grassmann" "MultivectorS")
  let ofBladeFn := mkIdent (Name.mkStr3 "Grassmann" "MultivectorS" "ofBlade")
  let bladeType := mkIdent (Name.mkStr2 "Grassmann" "Blade")
  return fun body => `(
    let $asciiIdent : $mvType $sigRef Float :=
      $ofBladeFn (⟨BitVec.ofNat $dimLit $maskLit⟩ : $bladeType $sigRef)
    let $subscriptIdent := $asciiIdent
    $body
  )

/-- Generate all basis bindings for dimension n.
    Takes the signature identifier to ensure consistent hygiene scope. -/
def generateAllBindings (n : Nat) (sigRef : TSyntax `ident) (body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  -- Limit dimension to avoid exponential explosion
  if n > 8 then
    Macro.throwError s!"Dimension {n} too large for full basis generation (max 8). \
      Use explicit blade construction."

  -- Generate bindings for all 2^n - 1 non-zero masks
  let numBlades := (1 <<< n) - 1
  let mut result := body

  -- Generate in reverse order so innermost bindings are for e₁, e₂, etc.
  for mask in (List.range numBlades).reverse do
    let m := mask + 1  -- Start from 1, not 0
    let binding ← generateBladeBinding m n sigRef
    result ← binding result

  return result

/-! ## Macro Rules -/

/-- Main Cl(p,q,r) context macro -/
macro_rules
  | `(Cl($p:num, $q:num, $r:num) { $body }) => do
    let pVal := p.getNat
    let qVal := q.getNat
    let rVal := r.getNat
    let n := pVal + qVal + rVal

    if n == 0 then
      Macro.throwError "Algebra dimension must be at least 1"

    let nLit := Syntax.mkNumLit (toString n)

    -- Create the signature identifier here to ensure consistent hygiene scope
    let sigIdent : TSyntax `ident := mkIdent `_sig
    let bodyWithBindings ← generateAllBindings n sigIdent body

    -- Construct names manually to bypass macro hygiene without requiring imports
    let sigType := mkIdent (Name.mkStr2 "Grassmann" "Signature")
    let sigClr := mkIdent (Name.mkStr3 "Grassmann" "Signature" "clr")
    `(
      let $sigIdent : $sigType $nLit := $sigClr $p $q $r
      $bodyWithBindings
    )

/-- Cl(p,q) shorthand -/
macro_rules
  | `(Cl($p:num, $q:num) { $body }) => `(Cl($p, $q, 0) { $body })

/-- Cl(n) shorthand (Euclidean) -/
macro_rules
  | `(Cl($n:num) { $body }) => `(Cl($n, 0, 0) { $body })

/-! ## Named Algebra Shortcuts -/

macro_rules
  | `(R2 { $body }) => `(Cl(2, 0, 0) { $body })

macro_rules
  | `(R3 { $body }) => `(Cl(3, 0, 0) { $body })

macro_rules
  | `(R4 { $body }) => `(Cl(4, 0, 0) { $body })

macro_rules
  | `(PGA2 { $body }) => `(Cl(2, 0, 1) { $body })

macro_rules
  | `(PGA3 { $body }) => `(Cl(3, 0, 1) { $body })

macro_rules
  | `(CGA2 { $body }) => `(Cl(3, 1, 0) { $body })

macro_rules
  | `(CGA3 { $body }) => `(Cl(4, 1, 0) { $body })

macro_rules
  | `(STA { $body }) => `(Cl(1, 3, 0) { $body })

end Grassmann.DSL
