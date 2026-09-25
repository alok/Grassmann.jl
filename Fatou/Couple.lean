import Fatou.Complex

/-!
# Generalized units: Grassmann `Couple{V,B}` maps

Fatou's Grassmann extension (`ext/GrassmannExt.jl:19-30`) iterates maps over
`Couple{V,B}` numbers `a + b·B` for a basis blade `B` with `B² = s`: `s = -1` is the complex
plane (`Λ(S"++").v12`), `s = +1` the split-complex (hyperbolic) plane (`Λ(S"+-").v12`), and
`s = 0` would be the dual numbers. The Julia extension is broken (its result is type-asserted
`ComplexF64` but is a `Values{2}`, port-notes/fatou.md §4.10); with the intended
`Complex(value(z)...)` it gives the hyperbolic Mandelbrot set, which the Lean kernel computes
directly: a `Couple` is carried in a `C64` as `(a, b)`, and the map and escape functional use
the operations below. `s` is meant to be a literal, so the branches fold away when inlined.

```lean
-- hyperbolic Mandelbrot set: z ↦ z² + c over a + b·B with B² = +1, escape on a² - b² ≥ 4
fatou (mandelbrot (fun z c => Couple.sq 1 z + c) { n := 40, N := 20 } (Q := fun z _ => Couple.abs2 1 z))
```
-/

namespace Fatou

namespace Couple

/-- `(a + bB)(c + dB) = (ac + s·bd) + (ad + bc)B` for `B² = s ∈ {-1, 0, 1}` (Grassmann's
`Couple` product). -/
@[inline] def mul (s : Int) (z w : C64) : C64 :=
  let bd := z.im * w.im
  let re := if s == 1 then z.re * w.re + bd else if s == -1 then z.re * w.re - bd else z.re * w.re
  ⟨re, z.re * w.im + z.im * w.re⟩

/-- `(a + bB)² = (a² + s·b²) + 2ab·B`, written as the product `mul s z z`. -/
@[inline] def sq (s : Int) (z : C64) : C64 := mul s z z

/-- Grassmann `abs2(a + bB) = a² + b²·abs2_inv(B)` with `abs2_inv(B) = -s`: `a² + b²` in the
complex plane, `a² - b²` (possibly negative) in the split-complex plane, `a²` for dual numbers. -/
@[inline] def abs2 (s : Int) (z : C64) : Float :=
  let bb := z.im * z.im
  if s == 1 then z.re * z.re - bb else if s == -1 then z.re * z.re + bb else z.re * z.re

end Couple

end Fatou
