import Grassmann.Composite.Scalar
import Grassmann.Composite.Series
import Grassmann.Composite.Couple
import Grassmann.Composite.Dense
import Grassmann.Composite.Chain
import Grassmann.Composite.Spinor
import Grassmann.Composite.Ring

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

Also: `Couple.radius`/`angle`/`polarize`/`vectorize`/`complexify`/`divSame`/`powf`,
`Phasor.complexify`/`inv`/`powf`, the quaternion `Half.radius`/`angle` and
`Spinor.quatvalue`, `rpow b t = b ^ t`, Grassmann's two-argument hyperbolic
arctangent `Composite.atanh2`, and `TensorRing` instances for `Multivector V Float`
(every space) and `Spinor V Float` (even-dimensional spaces, `EvenDim V`) through
which `AbstractTensors.Generic` supplies `tanh`, `asinh`, `acos`, `sinc`, `log10`,
`coexp`, `geomabs`, … (exposed as `Multivector.tanh`, …).

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
