import Wilkinson.BigFloat
import Wilkinson.Expr
import Wilkinson.FloatOps
import Wilkinson.Range
import Wilkinson.Num
import Wilkinson.SyntaxTree
import Wilkinson.Analysis
import Wilkinson.Parse
import Wilkinson.Poly
import Wilkinson.Reduce

/-!
# Wilkinson

Lean port of Michael Reed's `Wilkinson.jl` (v0.1.1): round-off analysis of
polynomial forms (expanded, Horner, factored) by the Stieltjes log-error bound
and the actual error against a 256-bit `BigFloat` evaluation, together with the
parts of `SyntaxTree.jl` (1.0.1) it relies on (`exprval`, `callcount`, `sub`,
`abs`, `alg`). See `docs/port-notes/small-algebra.md` §2.6, §4.6.

| module | Julia source | contents |
|---|---|---|
| `Wilkinson.Expr` | Julia `Expr` | `JExpr`, `jl⟪ … ⟫` quotation, `string(::Expr)` |
| `Wilkinson.BigFloat` | MPFR `BigFloat` | `BigFloat p`, correctly rounded `+ - * /`, `^n`, `log` |
| `Wilkinson.FloatOps` | `base/reduce.jl` | `sum` |
| `Wilkinson.Range` | `base/twiceprecision.jl` | `Float32` colon, `FloatSet` grids |
| `Wilkinson.Num` | Julia promotion | `JNum`: Int64/Rational/Float32/Float64/BigFloat |
| `Wilkinson.SyntaxTree` | `SyntaxTree.jl` | `callcount`, `sub`, `abs`, `alg`, `exprval`, `eval` |
| `Wilkinson.Analysis` | `src/Wilkinson.jl`, `src/polynomial.jl` | `stieltjes`, `simpson`, `Ω`, `exacterr`, `PolynomialComparison` |
| `Wilkinson.Parse` | Julia's parser | `JExpr.parse` for expression strings |
| `Wilkinson.Poly` | (REDUCE's polynomial core) | `ℚ[x]`, square-free and irreducible factorization over `ℤ` |
| `Wilkinson.Reduce` | REDUCE via Reduce.jl | `expand`/`horner`/`factor` in REDUCE's output shapes, `polyfactors`/`polyhorner`/`polyexpand`, the `CAS`, `tests` |

Everything numeric is bit-for-bit Julia (`oracle/golden/wilkinson/`, checked by
`Tests.Wilkinson`): the grid, `exp`/`log` and powers (Julia's own kernels, from
`JuliaBase.Math`), sums, 256-bit `BigFloat`, the
Stieltjes bounds, Simpson scores and actual-error integrals, and every REDUCE
form in the golden corpus.

## Deviations from Julia

* REDUCE is replaced by exact `ℚ[x]` arithmetic that prints REDUCE's shapes
  (`Wilkinson.Reduce`). Not reproduced: `factor` with `on rounded` (numeric,
  possibly complex roots; `Reduce.cas` returns the exact factorization, so
  `rxtra` is false), the `Reduce.Algebra` shapes of `polyhorner`/`polyexpand`
  (the same polynomial in `horner`/`expand` shape), and factors found only by a
  full Zassenhaus search (the port's factorizer does rational roots and bounded
  Kronecker search).
* `//` between floats (a `MethodError` in Julia after `sub`) divides;
  `exprval` of a bare literal and `log` of a negative number (`DomainError`)
  give `NaN`.
* Allocation counts (`bytes allocated`, nondeterministic in Julia) are `0`, and
  `testpoly` compares error values without Julia's allocation tie-break.
* REDUCE's 2-D `display(RExpr(expr))` in the printed reports is Julia's infix
  `string(expr)`; `plot` returns the series (`PolynomialComparison.plotData`).
-/
