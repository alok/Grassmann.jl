/-
String grammars for spaces and the literal syntax `S!"…"`, `D!"…"`, `V!"…"`,
`ℝ^n` (Julia `@S_str`, `@D_str`, `@V_str`, `ℝ^n`; DirectSum.jl
`src/DirectSum.jl:139-150, 205, 410-438`).

The macros run the parser at elaboration time and emit a `TensorBundle`
structure literal, so `abbrev CGA3 := S!"∞∅+++"` unfolds to a constructor
application and a malformed string is a compile-time error.
-/
module

public import DirectSum.ParseCore
public meta import DirectSum.ParseCore

public section

namespace DirectSum

/-- `S!"-+++"`: a `Signature` literal (Julia `S"-+++"`); `∞`/`∅` prefixes give
conformal/projective spaces (`S!"∞∅+++"`). -/
syntax:max (name := sigLit) "S!" str : term

/-- `D!"1,2,-3"`: a `DiagonalForm` literal (Julia `D"1,2,-3"`). -/
syntax:max (name := diagLit) "D!" str : term

/-- `V!"…"`: Julia `V"…"` with the corrected grammar (digits, commas, signs). -/
syntax:max (name := bundleLit) "V!" str : term

/-- `ℝ^n`: the Euclidean `Signature` of dimension `n` (Julia `ℝ^n`). A numeral
`n` elaborates to a structure literal; any other term to `TensorBundle.sig n`. -/
syntax:max "ℝ^" term:max : term

end DirectSum

end

public meta section

namespace DirectSum

open Bits Lean

namespace TensorBundle

/-- Syntax for a natural-number literal. -/
def natLit (n : Nat) : Term := Syntax.mkNumLit (toString n)

/-- Syntax for a rational constant. -/
def ratLit (r : Rat) : MacroM Term := do
  let num := natLit r.num.natAbs
  let base ← if r.den == 1 then `(($num : Rat)) else `((($num : Rat) / ($(natLit r.den) : Rat)))
  if r.num < 0 then `((-$base)) else pure base

/-- Syntax for a Boolean constant. -/
def boolLit (b : Bool) : MacroM Term := if b then `(true) else `(false)

/-- Syntax for an integer constant. -/
def intLit (i : Int) : MacroM Term :=
  if i < 0 then `((-$(natLit i.natAbs) : Int)) else `(($(natLit i.natAbs) : Int))

/-- A structure literal elaborating to `V` (used by `S!`, `D!`, `V!`, `ℝ^`). -/
def toSyntax (V : TensorBundle) : MacroM Term := do
  let metric ← match V.metric with
    | .signature s => `(DirectSum.Metric.signature ($(natLit s.toNat) : UInt64))
    | .euclid => `(DirectSum.Metric.euclid)
    | .diagonal d => do
      let xs ← d.mapM ratLit
      `(DirectSum.Metric.diagonal #[$xs,*])
    | .tensor g => do
      let rows ← g.mapM fun row => do
        let xs ← row.mapM ratLit
        `(#[$xs,*])
      `(DirectSum.Metric.tensor #[$rows,*])
  `(({ n := $(natLit V.n), metric := $metric, hasinf := $(← boolLit V.hasinf),
       hasorigin := $(← boolLit V.hasorigin), dyadmode := $(← intLit V.dyadmode),
       polymode := $(← boolLit V.polymode), diffvars := $(natLit V.diffvars),
       diffmode := $(natLit V.diffmode), name := $(natLit V.name) } : DirectSum.TensorBundle))

end TensorBundle

def expandWith (p : String → Except String TensorBundle) (s : TSyntax `str) :
    MacroM Term :=
  match p s.getString with
  | .ok V => V.toSyntax
  | .error e => Macro.throwErrorAt s e

macro_rules
  | `(S! $s) => expandWith TensorBundle.parseSignature s
  | `(D! $s) => expandWith TensorBundle.parseDiagonal s
  | `(V! $s) => expandWith TensorBundle.parseBundle s
  | `(ℝ^ $n) => match n.raw.isNatLit? with
    | some k => (TensorBundle.sig k).toSyntax
    | none => `(DirectSum.TensorBundle.sig $n)

end DirectSum
