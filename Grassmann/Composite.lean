import Grassmann.Composite.Scalar
import Grassmann.Composite.Series
import Grassmann.Composite.Couple
import Grassmann.Composite.Dense
import Grassmann.Composite.Chain
import Grassmann.Composite.Spinor
import Grassmann.Composite.Ring
import Grassmann.Composite.Norm
import Grassmann.Composite.Project
import Grassmann.Composite.Pow
import Grassmann.Composite.Phasor
import Grassmann.Composite.Kinds

/-!
# Grassmann.Composite: transcendental functions of the typed elements

Port of Grassmann.jl `src/composite.jl` (the exponential, logarithm, roots and
hyperbolic series), the integer powers of `src/algebra.jl:420-470`, the
`Couple`/`Phasor` helpers of `src/multivectors.jl:852-1090`, and AbstractTensors'
derived family (`cos`, `sin`, `tan`, …, the `co`/`pseudo` functions) on the static
layer (port-notes/grassmann-composite.md, abstracttensors-staticvectors.md §2.1.9,
grassmann-types.md §4.8). Coefficients are `Float` (Julia `Float64`).

## Functions by element type

| element | `exp`, `log`, `sqrt`, `cbrt`, `expm1`, `log1p` | `cosh`, `sinh` | `cos`, `sin`, `tan` | `pow` (`Int`) |
|---|---|---|---|---|
| `Single V G` | `Couple V` | `Single V 0`, `Single V G` | `Single V 0`, `Single V G`, `Single V G` | `Couple V` |
| `Couple V` | `Couple V` | `Couple V` | `Multivector V` | `Couple V` |
| `Chain V G` | `Multivector V` (`expEven`: `Spinor`) | `Spinor`, `Half V (G odd)` | `Spinor`, `Half V (G odd)` | `Multivector V` |
| `Spinor V` (`Half V false`) | `Spinor V` | `Spinor V` | `Spinor V` | `Spinor V` |
| `CoSpinor V`, `PseudoCouple V` | `Multivector V` | `Multivector V` | `Multivector V` | — |
| `Multivector V` | `Multivector V` | `Multivector V` | `Multivector V` (+ the whole AbstractTensors family) | `Multivector V` |
| `Phasor V` | `exp`, `sqrt`, `cbrt`: `Phasor`; `log`, `log1p`, `expm1`: `Couple` | — | — | `Phasor V` |

Also:

* inverse functions: `asinh`, `acosh`, `atanh`, `acoth` of terms and couples (couples) and
  spinors (spinors); `asin`, `atan` of terms (pseudo-couples, Julia's closed forms);
  `tanh`/`coth`, `exph`, `exp2`/`exp10`/`log2`/`log10` where they close;
* powers: integer `pow` everywhere, `rpow b t = b ^ t` (AbstractTensors), `powf t x =
  exp(x·log t)` for couples, spinors, multivectors and phasors;
* `logFast`/`loghFast` (Julia `log_fast`/`logh_fast`, Halley's iteration, capped: `none`
  where Julia loops forever) for couples, spinors and multivectors;
* `Couple.radius`/`angle`/`polarize`/`vectorize`/`complexify`/`divSame`,
  `Phasor.complexify`/`inv`/`eval`/`angleOn` (Julia `∠`), the quaternion
  `Half.radius`/`angle` and `Spinor.quatvalue`, `Chain.complexify`/`polarize`,
  Grassmann's two-argument hyperbolic arctangent `Composite.atanh2`; the complex-like
  accessors `realvalue`/`imagvalue`/`reim`/`amplitude`/`phase`/`unitangle`, `a ∠ θ`,
  `hyperplanes` and `𝕚 𝕛 𝕜` (`Composite.Phasor`);
* `^` on every kind (`Composite.Pow`: integer and real exponents, real bases);
* `abs`, `unit`, `unitize`, `unitnorm`, `geomabs` per kind with Julia's result kinds
  (`Composite.Norm`); `↑`/`↓` (`project`/`reject`, `Composite.Project`);
* the derived functions (`cot` … `acsch`, `sinc`, `cosc`, `exp2` …) on every kind
  (`Composite.Kinds`, generated);
* the `co`/`pseudo` family on chains (`Chain.coexp`, `coabs`, `coinv`, …) and, through
  `AbstractTensors.Generic`, on multivectors;
* `TensorRing` instances for `Multivector V Float` (every space) and `Spinor V Float`
  (even-dimensional spaces, `EvenDim V`), through which `AbstractTensors.Generic`
  supplies `tanh`, `asinh`, `acos`, `sinc`, `log10`, `coexp`, `geomabs`, … (exposed as
  `Multivector.tanh`, …).

## Performance

The closed forms of terms and couples are `@[inline]` straight-line code; chains, quaternions
and multivectors whose (non-scalar) square is a scalar take closed forms computed from their
coefficients (the square as a signature-weighted sum, no product kernel), and the series and
inverses run on the storage with in-place updates. Measured by the `composite` bench suite
(`Bench/Composite.lean`, its Julia twin `oracle/bench/composite.jl`; Apple M4 Max, ns per call
including the construction of the argument, which alone costs 15 ns here and 0.6 ns in Julia):

| call (`ℝ3` unless noted) | Lean | Julia |
|---|---|---|
| `Couple.exp`, `Single.exp` | 19, 18 | 5.1, 6.3 |
| `Couple.log`, `Couple.sqrt` (through `ComplexF64`) | 50, 47 | 14, 14 |
| `Couple.cosh` (hyperbolic) | 32 | 18 |
| `Chain.exp` (bivector) | 47 | 16 |
| `Chain.cos` | 41 | 31 |
| `Spinor.exp`, `log`, `sqrt` | 41, 44, 70 | 22, 26, 75 |
| `Multivector.exp`, `log`, `sqrt` | 265, 237, 313 | 197, 148, 228 |
| `PGA3` motor `exp` | 220 | 161 |
| `CGA3` translator `exp` | 76 | 15 |
| `↑`/`↓` (`Inf3`, `CGA3`) | 38-51 | 0.5-9 (constant-folded) |
| README torus / orbit-2 / orbit-4 / helix | 406 / 247 / 368 / 614 | 305 / 60 / 219 / 1136 |
| `chainfield` (the `orb` versor) | 201 | 59 |

## Semantics

Julia's algorithms are reproduced exactly: closed forms where the (non-scalar part
of the) argument squares to a scalar, by the sign of the square; otherwise the
power series with Julia's norm-based stopping rule (`Composite.Series`), whose
values agree with Julia only to ~1e-8…1e-12 by design. Where Julia returns
different containers by value (a `Couple` or a `Spinor` from `exp` of a `Single`
in a conformal space), the static result type is the smallest container that is
always correct and the coefficients agree.

Julia defects fixed rather than replicated (port-notes/grassmann-composite.md
§8.3): the parabolic `exp` (`e^s(1 + t)` for `e^s(1 + m)`), the zero-angle `NaN`s,
the broken generated `cosh`/`sinh` (and so `cos`/`sin` of spinors, multivectors
and most couples), `cbrt` of an elliptic couple, `exp` of a `Phasor`, negative and
null-blade powers, `expm1` of a negative pure-scalar spinor, and `log(b, t)`.
Kept on purpose: quirk B2 (`cos t = cosh(I ⟑ t)`, hyperbolic for scalars when
`I² = +1`), the series accuracy, the approximate `isscalar` test, and Julia's
`DomainError`/`inv(m) is undefined` cases, which are `NaN` (or `none` in the `?`
variants) here.

## Example

```lean
open Grassmann DirectSum in
#eval (Couple.exp (⟨3, 1.0, 2.0⟩ : Couple S!"+++" Float))   -- -1.1312 + 2.4717v₁₂
```
-/
