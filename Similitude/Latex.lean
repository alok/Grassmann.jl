import Similitude.Quotient

/-!
# LaTeX and markdown helpers (`Similitude.jl:281-348`)

The helpers Similitude's documentation is generated with:

* `latexquantity(q)`: a triple `(value and unit, the exact monomial, system)`
  for a quantity, a conversion factor or a constant, e.g. for `mile`
  `("$5280.0$ $\left[\text{ft}\right]$", "$2^{5}3\cdot 5\cdot 11$", "English")`;
* `latexquotient(U)`: for each class of `U/~`, the image and the quantities with
  their USQ dimensions;
* `latexdimensions(d, U)`: the image of `d` in `U`'s base units.

The monomials use FieldAlgebra's `latexgroup_pre` with the identity glyph `'1'`
(a `Char`, so no `\cdot ` before a coefficient). Julia's `latexdimensions`
calls `latexgroup` with the un-normalized system, for which neither the
registered names nor the system's base units apply, so it prints the image in
the USQ letters (energy in Metric is `\text{M}\cdot \text{L}^{2}\text{T}^{-2}`);
the other helpers use the registered names.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- Julia's default `dimlatex(U)` (`Similitude.jl:201`), the USQ letters. -/
def usqLatex : Array String :=
  #["\\text{F}", "\\text{M}", "\\text{L}", "\\text{T}", "\\text{Q}", "\\Theta", "\\text{N}",
    "\\text{J}", "\\text{A}", "\\text{R}", "\\text{C}"]

/-- The LaTeX monomial of an image in the USQ letters, without the registry. -/
def latexMonomial (img : Exps 11) : String :=
  (Group.mk' img (.int 1) : USQGroup).latexPre usqLatex false "\\mathbb{1}"

/-- FieldAlgebra's `latexgroup_pre(io, x, latext(x), '1')` for a Similitude value:
the constants monomial (names `usqlatex`), or the number itself (Julia `print`). -/
def latexValue : Scalar → String
  | .grp g => g.latexPre constantsLatex false "1" (coefSep := false)
  | x => x.toString

/-- FieldAlgebra's `special_print(product(x))` of a value. -/
def latexProduct (x : Scalar) : String := specialPrintFloat x.toFloat

/-- Julia `latexquantity(q::Quantity)` (`Similitude.jl:314-325`). -/
def latexquantity {U : Sys} {d : Dim} (q : Q U d) : String × String × String :=
  let v := Scalar.grp Consts.one * q.val
  (s!"${latexProduct v}$ $\\left[{U.latexDim d.toGroup.v}\\right]$", s!"${latexValue q.val}$", U.name)

/-- Julia `latexquantity(q::ConvertUnit)` (`Similitude.jl:326-340`). -/
def latexquantityConv {U S : Sys} {d : Dim} (_ : ConvertUnit U S d) : String × String × String :=
  let e := d.toGroup.v
  let rat := ratio e U S
  let d' := convertDim (pairData U S).2 e
  (s!"${latexProduct rat}$ $\\left[{S.latexDim d'}\\right]/\\left[{U.latexDim d'}\\right]$",
   s!"${latexValue rat}$", s!"{U.name} -> {S.name}")

/-- Julia `latexquantity(q::Group)` of a constant (`Similitude.jl:298-306`). -/
def latexquantityConst (g : Consts) : String × String × String :=
  (s!"${latexProduct (.grp g)}$ $\\left[\\mathbb\{1}\\right]$", s!"${latexValue (.grp g)}$", "Universe")

/-- Julia `latexquotient(U)` (`Similitude.jl:281-296`): for each class of `U/~`, the
image (registered name or monomial) and `q $\left[dims\right]$, …` with each
quantity's USQ dimension. -/
def latexquotient (U : Sys) : List (String × String) :=
  (quotient U).map fun (k, qs) =>
    (s!"${latexDims U.name k.v}$",
     ", ".intercalate (qs.map fun q =>
       let m := q.dim.toGroup.latexPre usqBasis.text true "\\mathbb{1}"
       s!"{q.name} $\\left[{m}\\right]$"))

/-- Julia `latexdimensions(D, U)` (`Similitude.jl:342-346`): the image of `d` in
`U`, written in the USQ letters (Julia passes the un-normalized system, for which
neither the registry nor the system's `dimlatex` applies). -/
def latexdimensions (d : Dim) (U : Sys) : String := s!"${latexMonomial (U.image d.toGroup.v)}$"

end Similitude
