import Similitude.Hom
import Similitude.UnitNames

/-!
# Unit names and the display of dimensions

Similitude prints a quantity's dimension through its unit system: the image
`U(d)` is looked up in the system's registry of derived unit names
(`unitdim.jl`, keyed by the exact image) and otherwise spelled out with the
system's base-unit names (`dimtext`): `J`, `lbf⋅ft`, `kg⋅m²s⁻²`, `M¹ᐟ²L³ᐟ²T⁻¹`
(`dimension.jl:36-64`, `derived.jl:505-622`).

Julia keys the registry by `Group{:USQ}` values including their element type,
so only exact (`Int`/`Rational`) images can match; `Float64` exponents never do
(`Metric(1, energy^1.0)` prints `kg⋅m²s⁻²`, not `J`).
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- A parsed registry: per system name, `(doubled image exponents, name)` pairs. -/
abbrev Registry := Array (String × Array (Array Int × String))

/-- Parse the generated per-system record strings of `UnitNames`. -/
def parseRegistry (data : Array (String × String)) : Registry :=
  data.map fun (sys, blob) =>
    (sys, ((blob.splitOn "\n").filter (· ≠ "")).toArray.map fun line =>
      match line.splitOn "\t" with
      | [k, v] => (((k.splitOn " ").filter (· ≠ "")).toArray.map (·.toInt!), v)
      | _ => (#[], line))

/-- Printed unit names (`unitgroup`), parsed once. -/
def unitText : Registry := parseRegistry unitTextData
/-- LaTeX unit names (`unitlatex`), parsed once. -/
def unitLatex : Registry := parseRegistry unitLatexData

/-- Doubled integer exponents of an exact vector, if every exponent is a multiple of `½`. -/
def doubledKey? : Exps 11 → Option (Array Int)
  | .exact v => (v.toArray.mapM fun q => let t := 2 * q; if t.den == 1 then some t.num else none)
  | .float _ => none

/-- Registry lookup by system name and exact image. -/
def Registry.find? (r : Registry) (sys : String) (img : Exps 11) : Option String := do
  let key ← doubledKey? img
  let (_, ents) ← Array.find? (·.1 == sys) r
  let (_, s) ← ents.find? (·.1 == key)
  return s

/-- Base-unit names of a system: `(dimtext, all single characters, dimlatex)`. -/
def dimText (sys : String) : Array String × Bool × Array String :=
  match dimTextTable.find? (·.1 == sys) with
  | some (_, t, c, l) => (t, c, l)
  | none => (usqBasis.text, true, usqBasis.latex)

/-- Julia `showgroup2(io, D, U)` (`dimension.jl:52-64`): the registered unit name
of the image `img` in the system named `sys`, or the monomial in its base units. -/
def showDims (sys : String) (img : Exps 11) : String :=
  match unitText.find? sys img with
  | some s => s
  | none =>
    let (names, chars, _) := dimText sys
    (Group.mk' img (.int 1) : USQGroup).showWith names chars "𝟙"

/-- Julia `latexgroup2(io, D, U)`: the LaTeX analogue (`dimension.jl:82-94`). -/
def latexDims (sys : String) (img : Exps 11) : String :=
  match unitLatex.find? sys img with
  | some s => s
  | none =>
    -- LaTeX names are strings, so `latexdims` always separates with `\cdot `
    (Group.mk' img (.int 1) : USQGroup).latexPre (dimText sys).2.2 false "\\mathbb{1}"

/-- How system `U` typesets a dimension `d` (Julia `latexgroup(io, U(d), U)`). -/
def _root_.UnitSystems.Sys.latexDim (U : Sys) (d : Exps 11) : String :=
  latexDims U.name (U.hom.apply d)

/-- The image of a USQ exponent vector under a system (`U(d)`). -/
def _root_.UnitSystems.Sys.image (U : Sys) (d : Exps 11) : Exps 11 := U.hom.apply d

/-- How system `U` prints a dimension `d` (Julia `showgroup(io, normal(U)(d), U)`). -/
def _root_.UnitSystems.Sys.showDim (U : Sys) (d : Exps 11) : String := showDims U.name (U.image d)

/-- The name Similitude prints for the `Unified` system. -/
def unifiedName : String := "Unified"

/-- How `Unified` prints a dimension: through `UnitSystem(d)` over the defining
constants (`Similitude.jl:158-164`, master branch). -/
def showDimUnified (d : Exps 11) : String := showDims unifiedName (usqMap.apply d)

end Similitude
