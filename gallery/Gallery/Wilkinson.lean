import Wilkinson
import Gallery.Common

/-!
# Wilkinson.jl `plot(::PolynomialComparison)` (`src/polynomial.jl:96-133`)

The error-analysis figure of Wilkinson.jl: for the expanded, Horner and factored forms of a
polynomial (and REDUCE's rounded factorization when it differs, and the input when it is none
of the three), the Stieltjes log-error bound and the actual error against a 256-bit
evaluation, each relative to the `BigFloat` bound of the optimal form, over the log-spaced
grid `floatset(Float64, 3000; scale = log)`. Bounds are solid (`lw = 0.7`), actual errors
dashed with small circles, in PyPlot's colour letters `y r b g k`.

The data is `Wilkinson.PolynomialComparison.ofForms` on REDUCE's forms (written out below as
REDUCE prints them; the port's own CAS reproduces the exact ones, not the rounded
factorization) and `plotData`. Upstream the legend is a positional list that mislabels the
lines when the input is drawn (`extra`) and spells "orignal"; here each line carries its
own label.
-/

namespace Gallery.WilkinsonFigs

open Wilkinson LeanPlot

/-- A polynomial with the five REDUCE forms `[optimal, expand, horner, factor, factor
rounded]` (`src/polynomial.jl:48-56`), as Julia prints them. -/
structure Case where
  /-- gallery name -/
  name : String
  /-- the input expression -/
  input : String
  /-- REDUCE's forms -/
  forms : Array String

/-- Parse a Julia expression (the cases are fixed literals). -/
def parse! (s : String) : JExpr := (JExpr.parse s).toOption.getD (.sym "x")

/-- The comparison of a case. -/
def Case.comparison (c : Case) : PolynomialComparison :=
  let fs := c.forms.map parse!
  PolynomialComparison.ofForms (parse! c.input) ⟨fs[0]!, fs[1]!, fs[2]!, fs[3]!, fs[4]!⟩

/-- `@sprintf("%.2e", x)` for positive finite `x`. -/
def fmtE2 (x : Float) : String :=
  let e0 := (Float.log10 x).floor
  let m := x / Float.pow 10 e0
  let r := (m * 100).round
  let (r, e) := if r ≥ 1000 then ((r / 10).round, e0 + 1) else (r, e0)
  let ri := r.toUInt64.toNat
  let ei : Int := if e < 0 then -((-e).toUInt64.toNat : Int) else (e.toUInt64.toNat : Int)
  let es := toString ei.natAbs
  s!"{ri / 100}.{(ri % 100) / 10}{ri % 10}e{if ei < 0 then "-" else "+"}{if es.length < 2 then "0" ++ es else es}"

/-- PyPlot's colour letters. -/
def pyColor : String → RGBA
  | "y" => ⟨0.75, 0.75, 0, 1⟩ | "r" => ⟨1, 0, 0, 1⟩ | "b" => ⟨0, 0, 1, 1⟩
  | "g" => ⟨0, 0.5, 0, 1⟩ | _ => ⟨0, 0, 0, 1⟩

/-- Non-finite values as `NaN` (line breaks). -/
def finite (v : FloatArray) : FloatArray := v.foldl (fun acc y => acc.push (if y.isFinite then y else 0.0 / 0.0)) .empty

/-- The figure: every series of `plotData` over `collect(set)`, legend on the right. -/
def figure (c : Case) (C : PolynomialComparison) : Figure := Id.run do
  let (series, _) := C.plotData
  let xs := C.set.collect
  let xlabel := s!"log|x|, Δ={fmtE2 C.set.stepValue}"
  let ylabel := "log |[alg(f)](x)−f(x)| / δ(f,x,2^-255),  log δ(f,x,2^-52)/δ(f,x,2^-255)"
  let mut ax := Axis2.new (title := (parse! c.input).toJulia) (xlabel := xlabel) (ylabel := ylabel)
  ax := ax.yaxis fun s => { s with labelsize := 11 }
  for s in series do
    let col : ColorSpec := .solid (pyColor s.color)
    let ys := finite s.ys
    if s.actual then
      ax := ax.lines xs ys (color := some col) (linewidth := 0.7) (linestyle := .dash) (label := some s.label)
      ax := ax.scatter xs ys (color := some col) (markersize := 2)
    else
      ax := ax.lines xs ys (color := some col) (linewidth := 0.7) (label := some s.label)
  return Figure.new (820, 480) |>.axis 1 1 ax |>.legend 1 2 (1, 1)

/-- The checks against the Julia dump: flags, forms, and every series (every 10th point and
the sum over all finite points). -/
def checks (C : PolynomialComparison) (j : Lean.Json) : Array Check := Id.run do
  let (series, _) := C.plotData
  let js := jarr (jget j "series")
  let sums := jfloats (jget j "sums")
  let stride := jnat (jget j "stride")
  let mut cs : Array Check := #[
    eqCheck "extra (input drawn)" C.extra ((jget j "extra").getBool?.toOption.getD false),
    eqCheck "rxtra (rounded factorization drawn)" C.rxtra ((jget j "rxtra").getBool?.toOption.getD false),
    eqCheck "series" series.size js.size,
    closeCheck s!"grid (every {stride}th)" (every C.set.collect stride) (jfloats (jget j "x")) 0]
  let labels := (jarr (jget j "labels")).map jstr
  let mut worst : Float := 0
  let mut worstSum : Float := 0
  let mut ok := labels == series.map (·.label)
  for ((sr, jk), k) in (series.zip js).zipIdx do
    let ys := finite sr.ys
    -- the dump spells non-finite values out (`NaN`, `-Inf`): compare the raw series
    let raw := every sr.ys stride
    let jr := jfloats jk
    let sameNonFinite := (List.range (min raw.size jr.size)).all fun i =>
      let a := raw[i]!
      let b := jr[i]!
      a.isFinite == b.isFinite && (a.isFinite || a.isNaN == b.isNaN && (a.isNaN || (a > 0) == (b > 0)))
    let d := if sameNonFinite then maxRelDiff (raw.foldl (fun acc y => acc.push (if y.isFinite then y else 0)) .empty)
      (jr.foldl (fun acc y => acc.push (if y.isFinite then y else 0)) .empty) else 1.0 / 0.0
    let s := sumFinite ys
    let dsum := (s - sums[k]!).abs / (if sums[k]!.abs > 1 then sums[k]!.abs else 1)
    worst := max worst d
    worstSum := max worstSum dsum
    ok := ok && d == 0 && dsum ≤ 1e-12
  cs := cs.push { label := "every series (labels, every 10th value, Σ)", ok
                  detail := s!"max rel |Δ| = {sci worst} (sampled), {sci worstSum} (sums) over {series.size} series" }
  return cs

/-- The three figures: Wilkinson's `(x-2)^9`, a cubic whose rounded factorization differs
(`rxtra`), and a product that is none of REDUCE's forms (`extra`). -/
def cases : List (Case × String) := [
  (⟨"wilkinson-x-2-pow-9", "(x - 2) ^ 9", #["(x - 2) ^ 9",
    "((((((((x ^ 9 - 18 * x ^ 8) + 144 * x ^ 7) - 672 * x ^ 6) + 2016 * x ^ 5) - 4032 * x ^ 4) + 5376 * x ^ 3) - 4608 * x ^ 2) + 2304x) - 512",
    "((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512",
    "(x - 2) ^ 9", "(x - 2) ^ 9"]⟩, "Error bounds of the forms of (x − 2)⁹"),
  (⟨"wilkinson-cubic", "x^3 - 6x^2 + 11x - 6", #["(x - 1) * (x - 2) * (x - 3)", "((x ^ 3 - 6 * x ^ 2) + 11x) - 6",
    "((x - 6) * x + 11) * x - 6", "(x - 1) * (x - 2) * (x - 3)", "(x - 1) * (x - 2.0) * (x - 3.0)"]⟩,
    "Error bounds of x³ − 6x² + 11x − 6, with REDUCE's rounded factorization"),
  (⟨"wilkinson-product", "(2x - 1) * (3x + 2)", #["(3x + 2) * (2x - 1)", "(6 * x ^ 2 + x) - 2", "(6x + 1) * x - 2",
    "(3x + 2) * (2x - 1)", "(3x + 2) * (2x - 1)"]⟩, "Error bounds of (2x − 1)(3x + 2), with the input form")]

/-- The Wilkinson entries. -/
def entries : List Entry := cases.map fun (c, title) =>
  { name := c.name, title, group := "Wilkinson"
    source := s!"`plot(PolynomialComparison(:({c.input})))` (Wilkinson.jl `src/polynomial.jl:96-133`)"
    build := fun j? => do
      let C := c.comparison
      return { fig := figure c C, checks := match j? with | some j => checks C j | none => #[] } }

end Gallery.WilkinsonFigs
