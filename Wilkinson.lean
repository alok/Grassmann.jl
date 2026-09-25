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
| `Wilkinson.FloatOps` | `base/special/pow.jl`, `base/reduce.jl` | `pow_body`, `literal_pow`, `sum` |
| `Wilkinson.Range` | `base/twiceprecision.jl` | `Float32` colon, `FloatSet` grids |
| `Wilkinson.Num` | Julia promotion | `JNum`: Int64/Rational/Float32/Float64/BigFloat |
| `Wilkinson.SyntaxTree` | `SyntaxTree.jl` | `callcount`, `sub`, `abs`, `alg`, `exprval`, `eval` |
| `Wilkinson.Analysis` | `src/Wilkinson.jl`, `src/polynomial.jl` | `stieltjes`, `simpson`, `Ω`, `exacterr`, `PolynomialComparison` |
| `Wilkinson.Parse` | Julia's parser | `JExpr.parse` for expression strings |
| `Wilkinson.Poly` | (REDUCE's polynomial core) | `ℚ[x]`, square-free and irreducible factorization over `ℤ` |
| `Wilkinson.Reduce` | REDUCE via Reduce.jl | `expand`/`horner`/`factor` in REDUCE's output shapes, `polyfactors`/`polyhorner`/`polyexpand`, the `CAS` |
-/
