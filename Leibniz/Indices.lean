/-
Index printing, ported from Leibniz.jl `indices.jl`.

Basis blades print as a prefix followed by subscript (vectors) or
superscript (covectors) indices: `v₁₂₃`, `w¹²`, `∂₁`, `ϵ₂`. Indices 1–9 map to
subscript digits and 10 to `₀`. Indices 11–36 map to the alphanumeric
alphabets (`alphanumv` for vectors, `alphanumw` for covectors). The special
conformal indices are `-1 ↦ ∞` and `0 ↦ ∅`.
-/

namespace Leibniz

/-- Conformal/projective symbols: `∞` (point at infinity) and `∅` (origin). -/
def vio : Char × Char := ('∞', '∅')

/-- `"1234567890" ++ a–z ++ A–Z` : vector index alphabet. -/
def alphanumv : String := "1234567890abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
/-- `"1234567890" ++ A–Z ++ a–z` : covector index alphabet. -/
def alphanumw : String := "1234567890ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

private def subDigits : Array Char := #['₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉', '₀']
private def supDigits : Array Char := #['¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', '⁰']

/-- Nth character (1-based) of a string, or `'?'`. -/
private def charAt (s : String) (j : Nat) : Char := (s.toList[j - 1]?).getD '?'

/-- Subscript glyph for index `i` (Julia `subs[i]`), for `-1 ≤ i ≤ 36`. -/
def subs (i : Int) : Char :=
  if i == -1 then vio.1
  else if i == 0 then vio.2
  else
    let j := i.toNat
    if j ≤ 10 then subDigits[j - 1]! else charAt alphanumv j

/-- Superscript glyph for index `i` (Julia `sups[i]`), for `-1 ≤ i ≤ 36`. -/
def sups (i : Int) : Char :=
  if i == -1 then vio.1
  else if i == 0 then vio.2
  else
    let j := i.toNat
    if j ≤ 10 then supDigits[j - 1]! else charAt alphanumw j

/-- Vector/covector/tangent/cotangent prefixes `("v","w","∂","ϵ")`. -/
def pre : String × String × String × String := ("v", "w", "∂", "ϵ")
/-- Alternate prefixes used for labels: `("X","x","Y","y")`. -/
def PRE : String × String × String × String := ("X", "x", "Y", "y")

/-- Glyph for one index (Julia `printindex`).

* `label` : print indices 1–10 as plain digits (used for symbolic labels).
* `pfx` : the prefix in use; `v`/`∂` print subscripts, `w`/`ϵ` superscripts.
  Indices beyond 36 wrap by 26 and flip sub/superscript, as in Leibniz.jl. -/
def printIndex (i : Int) (label : Bool := false) (pfx : String := pre.1) : String :=
  let t := i > 36
  let j := if t then i - 26 else i
  if label && 0 < j && j ≤ 10 then toString j
  else
    let vecLike := pfx == pre.1 || pfx == pre.2.2.1
    -- `(e ∉ pre[[1,3]]) ⊻ t ? sups : subs`
    if (!vecLike) != t then (sups j).toString else (subs j).toString

/-- Prefix followed by all index glyphs, e.g. `printIndices [1,2] = "v₁₂"`. -/
def printIndices (is : List Int) (label : Bool := false) (pfx : String := pre.1) : String :=
  is.foldl (fun acc i => acc ++ printIndex i label pfx) pfx

example : printIndices [1, 2, 3] = "v₁₂₃" := by decide
example : printIndices [1, 2] (pfx := "w") = "w¹²" := by decide
example : printIndices [-1, 0, 1] = "v∞∅₁" := by decide
example : printIndices [10, 11, 12] = "v₀ab" := by decide
example : printIndices [] = "v" := by decide

end Leibniz
