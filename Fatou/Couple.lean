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
-- the same from the expression, Julia's `mandelbrot(:(z^2 + c); B = Λ(S"+-").v12)`
fatou (mandelbrot! "z^2 + c" (B := "1") { n := 40, N := 20 })
```

Division is `z · w⁻¹` with `(a + bB)⁻¹ = (a - bB)/(a² - s·b²)`, and integer powers follow
Julia's `literal_pow`/`power_by_squaring` multiplication order.
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

/-- `(a + bB)⁻¹ = (a - bB)/(a² - s·b²)` (the conjugate over `abs2`). -/
@[inline] def inv (s : Int) (z : C64) : C64 :=
  let d := abs2 s z
  ⟨z.re / d, -z.im / d⟩

/-- `z / w = z · w⁻¹`. -/
@[inline] def div (s : Int) (z w : C64) : C64 := mul s z (inv s w)

/-- `x / w` for a real `x`: `x · w⁻¹`. -/
@[inline] def rdiv (s : Int) (x : Float) (w : C64) : C64 :=
  let i := inv s w
  ⟨x * i.re, x * i.im⟩

/-- `k` squarings. -/
def squareTimes (s : Int) : Nat → C64 → C64
  | 0, x => x
  | k + 1, x => squareTimes s k (mul s x x)

/-- The main loop of Julia's `power_by_squaring`. -/
def powLoop (s : Int) : Nat → Nat → C64 → C64 → C64
  | 0, _, _, y => y
  | fuel + 1, p, x, y =>
    if p == 0 then y
    else
      let t := C64.trailingZeros p + 1
      let x := squareTimes s t x
      powLoop s fuel (p >>> t) x (mul s y x)

/-- Julia's `power_by_squaring(z, p)` (intfuncs.jl:394-438) in the `Couple` product. -/
def powBySquaring (s : Int) (z : C64) (p : Nat) : C64 :=
  if p == 1 then z
  else if p == 0 then ⟨1, 0⟩
  else if p == 2 then mul s z z
  else
    let t := C64.trailingZeros p + 1
    let x := squareTimes s (t - 1) z
    powLoop s 64 (p >>> t) x x

/-- Julia's literal `z^n` (`literal_pow`: `z*z`, `z*z*z` for `n = 2, 3`, `power_by_squaring`
beyond, through `inv` for negative `n`) in the `Couple` product. -/
@[inline] def pow (s : Int) (z : C64) (n : Int) : C64 :=
  match n with
  | 0 => ⟨1, 0⟩
  | 1 => z
  | 2 => mul s z z
  | 3 => mul s (mul s z z) z
  | .ofNat k => powBySquaring s z k
  | .negSucc 0 => inv s z
  | .negSucc 1 => let i := inv s z; mul s i i
  | .negSucc k => powBySquaring s (inv s z) (k + 1)

end Couple

end Fatou
