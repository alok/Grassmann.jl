import Bench.Harness
import Wilkinson

/-!
# `wilkinson`: polynomial round-off analysis

Julia twin: `oracle/bench/wilkinson.jl` (SyntaxTree 1.0.1 and Wilkinson's kernels, copied as in
the oracle since Wilkinson.jl needs PyPlot).

* `parse`: 11 Julia expression strings (the oracle's fixed polynomials, including `(x-2)^9` in
  expanded and Horner form) parsed to ASTs (Julia: `Meta.parse`); check: total call count.
* `exprval`: SyntaxTree's `exprval` score of each AST.
* `errval_*`: `errval(expr, Float64)`: the Stieltjes bound of `abs(expr)` on the 3000-point
  logarithmic grid and its Simpson score. Lean interprets the AST at each grid point; Julia
  generates and compiles a function per call (`genlatest`, as Wilkinson.jl does), and the
  Julia-only `*_nocodegen` rows time the same numerics with the function generated once.
-/

namespace Bench.Wilkinson

open _root_.Wilkinson Bench

/-- The expression strings (as in the Julia twin). -/
def exprs : Array String := #[
  "x^9 - 2", "(x - 2)^9", "2x^2 - 1//2", "x^2 + 3x + 2", "(x + 1) * (x + 2)",
  "2 + x * (3 + x)", "1.0 - 3.0x + x^3", "((x - 1) * x + 1) * x + 5", "(x - 1) * (x - 2) * (x - 3)",
  "x^9 - 18x^8 + 144x^7 - 672x^6 + 2016x^5 - 4032x^4 + 5376x^3 - 4608x^2 + 2304x - 512",
  "((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512"]

/-- The `errval` cases. -/
def errvalCases : List (String × String) := [
  ("factored9", "(x - 2)^9"),
  ("expanded9", "x^9 - 18x^8 + 144x^7 - 672x^6 + 2016x^5 - 4032x^4 + 5376x^3 - 4608x^2 + 2304x - 512"),
  ("horner9", "((((((((x - 18) * x + 144) * x - 672) * x + 2016) * x - 4032) * x + 5376) * x - 4608) * x + 2304) * x - 512")]

/-- Parse (failures count as zero calls). -/
def parseE (s : String) : JExpr := (JExpr.parse s).toOption.getD (.sym "x")

/-- `∑ callcount (parse s)`. -/
def parseAll (ss : Array String) : Nat :=
  ss.foldl (fun acc s => acc + SyntaxTree.callcount (parseE s)) 0

/-- `∑ exprval e`. -/
def exprvalAll (es : Array JExpr) : Float :=
  es.foldl (fun acc e => acc + (SyntaxTree.exprval e).1) 0

/-- The suite. -/
def suite : Suite := ⟨"wilkinson", do
  let n := exprs.size
  bench "parse" (ops := n) (param := s!"{n} exprs") fun s => parseAll (blackBox s exprs)
  let es := exprs.map parseE
  bench "exprval" (ops := n) (param := s!"{n} exprs") fun s => exprvalAll (blackBox s es)
  for (name, src) in errvalCases do
    let e := parseE src
    bench s!"errval_{name}" (param := "N=3000") fun s => errval (blackBox s e) .f64⟩

end Bench.Wilkinson
