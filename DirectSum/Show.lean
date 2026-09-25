/-
Julia-exact display of spaces, subspaces and basis terms (DirectSum.jl
`src/DirectSum.jl:167-356`, Leibniz.jl `src/indices.jl:185-203`).

* `TensorBundle.toString` is Julia `show(::Signature)` / `show(::DiagonalForm)`
  (`⟨+++⟩`, `⟨-+++⟩`, `⟨∞∅+++⟩`, `T¹⟨+++₁⟩`, `⟨---⟩'`, `⟨-++++---⟩*`, `⟨1,2,3⟩`).
* `TensorBundle.showSub V S` is Julia `show(::Submanifold)` for the subspace with
  mask `S` (`⟨__+_+⟩`, `⟨∅-1__⟩`); `showHandle V = showSub V (lowMask n)` is the
  full-space handle every element carries (`⟨111⟩`, `⟨∞∅111⟩`, `T¹⟨+++---₁²⟩*`).
* Coefficients are exact `Rat`s. `showNum r float` prints them as a Julia `Int`
  (when `float = false` and `r` is integral) or as the Julia `Float64` nearest
  to them, through `JuliaBase.F64.showString` (Ryu shortest round-trip digits).
-/
import DirectSum.Space
import JuliaBase.Float

namespace DirectSum

open Bits Leibniz

/-! ## Numbers -/

/-- The `Float64` nearest to `r` (correctly rounded when numerator and
denominator are below `2^53`, which covers every metric and product
coefficient here). -/
@[inline] def ratToFloat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

/-- Julia `show(::Float64)` of the double nearest to `r`, via JuliaBase's port
of `Ryu.writeshortest` (shortest round-trip digits, `.0` on integers, Julia's
plain-vs-exponent rule). -/
def juliaFloat (r : Rat) : String := JuliaBase.F64.showString (ratToFloat r)

/-- A coefficient as Julia prints it: an `Int` when `float = false` and `r` is
integral, else a `Float64` (`juliaFloat`). -/
def showNum (r : Rat) (float : Bool := false) : String :=
  if !float && r.den == 1 then toString r.num else juliaFloat r

#guard juliaFloat 6 == "6.0"
#guard juliaFloat (-1/2) == "-0.5"
#guard juliaFloat (3/4) == "0.75"
#guard juliaFloat 1000000 == "1.0e6"
#guard juliaFloat 12345678 == "1.2345678e7"
#guard juliaFloat (1/100000) == "1.0e-5"
#guard juliaFloat (1/10000) == "0.0001"
#guard juliaFloat 100000 == "100000.0"
#guard juliaFloat (1/3) == "0.3333333333333333"
#guard juliaFloat (1/10) == "0.1"

/-- A diagonal-form entry: integers print as integers, other values as Julia
floats (`1.5`) when their decimal terminates, else `p//q`. -/
def showDiagEntry (r : Rat) : String := if r.den == 1 then toString r.num else juliaFloat r

namespace TensorBundle

variable (V : TensorBundle)

/-! ## Spaces -/

/-- `T^μ⟨` prefix (empty `⟨` when `μ = 0`). -/
private def openBracket (mu : Nat) : String :=
  if mu > 0 then "T" ++ (sups mu).toString ++ "⟨" else "⟨"

/-- `⟩` followed by `*` (dyadic) / `'` (dual) and the name-scheme subscript. -/
private def closeBracket : String :=
  "⟩" ++ (if V.dyadmode < 0 then "*" else if V.dyadmode > 0 then "'" else "")
    ++ (if V.name > 1 then (subs V.name).toString else "")

/-- Tangent-slot glyphs after the metric: `ν` subscripts (superscripts when dual
xor not polymode), then for dyadic spaces `ν` superscripts. -/
private def tangentGlyphs : String :=
  let d := V.diffvars
  if d == 0 then "" else
    let first := (List.range d).map fun x =>
      if (V.dyadmode > 0) != !V.polymode then sups (Int.ofNat (x + 1)) else subs (Int.ofNat (x + 1))
    let second := if V.dyadmode < 0 then (List.range d).map fun x => sups (Int.ofNat (x + 1)) else []
    String.ofList (first ++ second)

/-- The `⟨…⟩` display of a matrix row restricted to `cols` (Julia `Values` show):
`[1.0, 0.5, 0.0]`. -/
private def showRow (row : Array Rat) (cols : List Nat) : String :=
  "[" ++ ", ".intercalate (cols.map fun j => juliaFloat (row[j - 1]?.getD 0)) ++ "]"

/-- Julia `show(::Submanifold)` of the subspace of `V` spanned by mask `S`
(`DirectSum.jl src/DirectSum.jl:325-356`): each generator prints its metric
glyph if present, `_` otherwise; conformal (non-diagonal) spaces print `1`/`-1`
(`⟨∅-1__⟩`), a `DiagonalForm` its values with `,`, an `Int` space `1`, a
`MetricTensor` its rows restricted to `S`. Tangent slots follow Julia's
`diffvars(::Submanifold)` quirk (only the last `ν` positions count). -/
def showSub (S : UInt64) : String := Id.run do
  let n := V.n
  let F := V.diffvars
  let C := V.dyadmode
  let ind := indicesList S
  let G := ind.length
  -- Julia `diffvars(::Submanifold)`: count of `ind` in the last `F` positions.
  let d := ind.countP fun i => i + F ≥ n + 1
  let N := G - (if d > 0 then (if C < 0 then 2 * d else d) else 0)
  let NM := n - (if F > 0 then (if C < 0 then 2 * F else F) else 0)
  let sinf := V.hasinf && testBit S 0
  let sorigin := V.hasorigin && (if V.hasinf then testBit S 1 else testBit S 0)
  let start := (if sinf then 1 else 0) + (if sorigin then 1 else 0) + 1
  let sep := match V.metric with | .diagonal _ | .tensor _ => true | _ => false
  let mut out := openBracket V.diffmode
  if sinf then out := out ++ "∞"
  if sorigin then out := out ++ "∅"
  for k in [start:NM + 1] do
    if ind.contains k then
      let m := match V.metric with
        | .euclid => "1"
        | .signature s =>
          if V.isdiag then (if testBit s (k - 1) then "-" else "+")
          else (if testBit s (k - 1) then "-1" else "1")
        | .diagonal _ => showDiagEntry (V.metricAt k)
        | .tensor g => showRow ((g[k - 1]?.getD #[]).map fun x => if V.isdual then -x else x) ind
      out := out ++ m
    else out := out ++ "_"
    if sep && k != NM then out := out ++ ","
  if d > 0 then
    let tail := ind.drop N
    for x in tail.take d do
      let i : Int := (x : Int) - NM
      out := out.push (if (C > 0) != !V.polymode then sups i else subs i)
    if C < 0 then
      for x in tail.drop d do out := out.push (sups ((x : Int) - NM))
  return out ++ closeBracket V

/-- Julia `show(Submanifold(V))`: the full-space handle, which is what Julia
prints for the space of an algebra element (`⟨111⟩`, `⟨∞∅111⟩`, `⟨1,2,3⟩`). -/
def showHandle : String := V.showSub (lowMask V.n)

/-- Julia `show(::Signature)` / `show(::DiagonalForm)` (`DirectSum.jl
src/DirectSum.jl:175-243`) for the bare space. An `Int` space and a
`MetricTensor` have no bare display in Julia and print as their handle. -/
protected def toString : String :=
  let prefix_ := openBracket V.diffmode ++ (if V.hasinf then "∞" else "")
    ++ (if V.hasorigin then "∅" else "")
  let slots := (List.range V.grade).drop V.nulls
  match V.metric with
  | .euclid | .tensor _ => V.showHandle
  | .signature s =>
    prefix_ ++ String.ofList (slots.map fun k => if testBit s k then '-' else '+')
      ++ tangentGlyphs V ++ closeBracket V
  | .diagonal _ =>
    let vals := V.diagValues
    prefix_ ++ String.join (slots.map fun k =>
        showDiagEntry (vals[k]?.getD 0) ++ (if k + 1 != V.n then "," else ""))
      ++ tangentGlyphs V ++ closeBracket V

instance : ToString TensorBundle := ⟨TensorBundle.toString⟩

/-- Julia `show(Λ(V))` (`DirectSum.jl src/basis.jl:195-202, 345-347, 373-376`):
`DirectSum.Basis{V,2ⁿ}(v, v₁, …)` listing every blade for `n ≤ 8`,
`DirectSum.SparseBasis{V,2ⁿ}(v, ..., v₁₂…)` for `8 < n ≤ 22`, and
`DirectSum.ExtendedBasis{…}` beyond (or for dyadic spaces with `n > 16`). -/
def showBasis : String :=
  let size := toString (2 ^ V.n)
  let extended := V.n > 22 || (V.isdyadic && V.n > 16)
  if V.n ≤ 8 && !extended then
    "DirectSum.Basis{" ++ V.showHandle ++ "," ++ size ++ "}("
      ++ ", ".intercalate ((Leibniz.indexBasisAll V.n).map (V.bladeLabel ·)).toList ++ ")"
  else
    (if extended then "DirectSum.ExtendedBasis{" else "DirectSum.SparseBasis{") ++ V.showHandle ++ ","
      ++ size ++ "}(" ++ V.bladeLabel 0 ++ ", ..., " ++ V.bladeLabel (lowMask V.n) ++ ")"

/-- Julia `show(collect(V))` for a bare `Signature`/`DiagonalForm`
(`DirectSum.jl src/basis.jl:183`): the basis of *subspaces*,
`DirectSum.Basis{⟨-+++⟩,16}(⟨____⟩, ⟨-___⟩, …)`. -/
def showCollect : String :=
  "DirectSum.Basis{" ++ V.toString ++ "," ++ toString (2 ^ V.n) ++ "}("
    ++ ", ".intercalate ((Leibniz.indexBasisAll V.n).map (V.showSub ·)).toList ++ ")"

/-! ## Basis terms -/

/-- Julia `showvalue` of `c · e_b` (`Leibniz.jl src/indices.jl:195-203`) for a
real coefficient: the number (Int or Float per `float`), then the blade label.
Integers and finite floats take no `*`. -/
def showTerm (c : Rat) (b : UInt64) (float : Bool := false) : String :=
  showNum c float ++ V.bladeLabel b

end TensorBundle

/-- A subspace of `V`: Julia's non-basis `Submanifold{V,G,S}` (a mask of the
included generators). -/
structure SubSpace (V : TensorBundle) where
  /-- Included generators (bit `k-1` ⇔ generator `k`). -/
  mask : UInt64
  deriving DecidableEq, Repr, Hashable

namespace SubSpace

variable {V : TensorBundle}

/-- Julia `rank`: number of included generators. -/
@[inline] def rank (s : SubSpace V) : Nat := popcount s.mask

instance : ToString (SubSpace V) := ⟨fun s => V.showSub s.mask⟩

end SubSpace

namespace TensorBundle

/-- Julia `V(i, j, …)`: the subspace spanned by the listed 1-based generators
(order and repeats are ignored), e.g. `(ℝ^5).sub [3,5]` prints `⟨__+_+⟩`. -/
def sub (V : TensorBundle) (is : List Nat) : SubSpace V :=
  ⟨is.foldl (fun m i => m ||| (bit i &&& lowMask V.n)) 0⟩

/-- The full-space handle `Submanifold(V)` as a subspace. -/
def handle (V : TensorBundle) : SubSpace V := ⟨lowMask V.n⟩

end TensorBundle

end DirectSum
