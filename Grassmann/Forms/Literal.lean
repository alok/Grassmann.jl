/-
Operator literals: Julia's `@TensorOperator`, `@Endomorphism`, `@Outermorphism`,
`@SpectralOperator` (Grassmann.jl `src/forms.jl:11, 624-633, 724, 388-390`) on a matrix
literal, with the shape checked when the term is elaborated (no `Option`):

| Julia | here (scoped in `Grassmann`) | result |
|---|---|---|
| `@TensorOperator [1 2 3; 4 5 6]` | `op![[1, 2, 3], [4, 5, 6]]` | `TensorOperator ℝ³ (.chain 1) ℝ² (.chain 1) α` (rows = codomain) |
| `@Endomorphism [1 2; 3 4]` | `endo![[1, 2], [3, 4]]` | `Endomorphism ℝ² (.chain 1) α` (square, else an elaboration error) |
| `@Outermorphism [1 2; 3 4]` | `outer![[1, 2], [3, 4]]` | its `Outermorphism` (the compounds) |
| `@SpectralOperator [2 1; 1 2]` | `spectral![[2, 1], [1, 2]]` | its eigen-decomposition (`TensorOperator.eigen`, `Float`) |

Rows are Julia's rows (`[1 2; 3 4]` is `[[1, 2], [3, 4]]`): row `i` lists the `i`-th components
of the column images. The spaces are Julia's `Submanifold(n)` (`TensorBundle.euclidean n`); the
coefficient type comes from the context (`(endo![[1, 2], [3, 4]] : Endomorphism _ _ Float)`).
A ragged or empty literal is rejected at elaboration.
-/
import Grassmann.Forms.Spectral

namespace Grassmann

open DirectSum StaticVectors AbstractTensors

namespace Forms

/-- Entry `(i, j)` of a row-major literal with `c` columns (zero outside it). -/
@[inline] def litEntry {α : Type} [Coeff α] (a : Array α) (c i j : Nat) : α := a[i * c + j]?.getD Coeff.zero

/-- The operator of a row-major `r × c` literal. -/
@[inline] def ofLiteral {α : Type} [Coeff α] (r c : Nat) (a : Array α) :
    TensorOperator (TensorBundle.euclidean c) (.chain 1) (TensorBundle.euclidean r) (.chain 1) α :=
  TensorOperator.ofFn fun i j => litEntry a c i.1 j.1

/-- The rows of a matrix literal and their common length, or an error at the offending row. -/
def literalRows (rows : Array Lean.Term) : Lean.MacroM (Array (Array Lean.Term) × Nat) := do
  let mut out : Array (Array Lean.Term) := #[]
  for r in rows do
    match r with
    | `([$xs,*]) => out := out.push xs.getElems
    | _ => Lean.Macro.throwErrorAt r "operator literal: each row is a list literal `[a, b, …]`"
  let some first := out[0]? | Lean.Macro.throwError "operator literal: at least one row is needed"
  let c := first.size
  if c == 0 then Lean.Macro.throwError "operator literal: rows must not be empty"
  for h : k in [0:out.size] do
    if out[k].size != c then
      Lean.Macro.throwErrorAt rows[k]! s!"operator literal: row {k + 1} has {out[k].size} entries, row 1 has {c}"
  return (out, c)

end Forms

/-- Julia `@TensorOperator [a b; c d]`: an operator from its rows, shape checked at elaboration. -/
scoped syntax "op![" term,* "]" : term

/-- Julia `@Endomorphism [a b; c d]`: a square operator (else an elaboration error). -/
scoped syntax "endo![" term,* "]" : term

/-- Julia `@Outermorphism [a b; c d]`: the outermorphism of a square literal. -/
scoped syntax "outer![" term,* "]" : term

/-- Julia `@SpectralOperator [a b; c d]`: the eigen-decomposition of a square `Float` literal. -/
scoped syntax "spectral![" term,* "]" : term

macro_rules
  | `(op![ $rows,* ]) => do
    let (rs, c) ← Forms.literalRows rows.getElems
    let flat := rs.flatten
    `(Forms.ofLiteral $(Lean.quote rs.size) $(Lean.quote c) #[$flat,*])

macro_rules
  | `(endo![ $rows,* ]) => do
    let (rs, c) ← Forms.literalRows rows.getElems
    if rs.size != c then
      Lean.Macro.throwError s!"endo![…]: a square literal is expected, got {rs.size} × {c}"
    let flat := rs.flatten
    `((Forms.ofLiteral $(Lean.quote c) $(Lean.quote c) #[$flat,*] :
        Endomorphism (TensorBundle.euclidean $(Lean.quote c)) (.chain 1) _))

macro_rules
  | `(outer![ $rows,* ]) => do
    let (rs, c) ← Forms.literalRows rows.getElems
    if rs.size != c then
      Lean.Macro.throwError s!"outer![…]: a square literal is expected, got {rs.size} × {c}"
    let flat := rs.flatten
    `((Forms.ofLiteral $(Lean.quote c) $(Lean.quote c) #[$flat,*] :
        Endomorphism (TensorBundle.euclidean $(Lean.quote c)) (.chain 1) _).outermorphism)

macro_rules
  | `(spectral![ $rows,* ]) => do
    let (rs, c) ← Forms.literalRows rows.getElems
    if rs.size != c then
      Lean.Macro.throwError s!"spectral![…]: a square literal is expected, got {rs.size} × {c}"
    let flat := rs.flatten
    `(TensorOperator.eigen (Forms.ofLiteral $(Lean.quote c) $(Lean.quote c) #[$flat,*] :
        Endomorphism (TensorBundle.euclidean $(Lean.quote c)) (.chain 1) Float))

end Grassmann
