import Tests.Fatou.Harness
import Fatou.Symbolic

/-!
The Lean side of the oracle catalog of `oracle/fatou/gen.jl`: every Julia `Define` there,
rebuilt with the symbolic front-ends (`juliafill!`, `mandelbrot!`, `newton!`) from the same Julia
expression. The maps are compiled at elaboration time with Julia's types and methods, and the
Newton maps are derived by `Fatou.CAS`; where REDUCE's `off exp` form of the Newton map differs
from the CAS's expanded form (`sin(z) - 1`, `z^2 - im`, `exp(z) + 1`), REDUCE's expression is
given as `(map := …)`, which is what Julia iterates (the `F` field of `sets.json`).

Each entry is a function of the column count `n`, so the same definition serves the
reduced dump and the full README resolution.
-/

namespace Tests.Fatou.Catalog

open _root_.Fatou

/-- `c₀ = -0.06 + 0.67im` of the README filled Julia set. -/
def c₀ : C64 := ⟨-0.06, 0.67⟩

/-- REDUCE's Newton map of `z^3 - 1` with `m = 1`, `(2 * z ^ 3 + 1) / (3 * z ^ 2)`, written by
hand (the reference the symbolic front-end is checked against). -/
@[inline] def newtonCubic (z _c : C64) : C64 := ((2 : Float) * z ^ 3 + (1 : Float)) / ((3 : Float) * z ^ 2)

/-- README filled Julia set (`README.md:68-74`; Julia interpolates the value `c₀`). -/
@[inline] def readmeFilledJulia (n : Nat) : Define :=
  juliafill! "z^2 + (-0.06 + 0.67im)"
    { bounds := ⟨-1.5, 1.5, -1, 1⟩, N := 80, n, cmap := "gnuplot", iter := true }

/-- README Mandelbrot set (`README.md:78-82`). -/
@[inline] def readmeMandelbrot (n : Nat) : Define :=
  mandelbrot! "z^2 + c" { n, N := 20, bounds := ⟨-1.91, 0.51, -1.21, 1.21⟩, cmap := "gist_earth" }

/-- README Newton fractal of `z^3 - 1` (`README.md:98-104`). -/
@[inline] def readmeNewton (n : Nat) : Define :=
  newton! "z^3 - 1" { n, ϵ := some 0.1, N := 25, iter := true, cmap := "jet" }

/-- README generalized Newton fractal (`README.md:108-116`), iterating REDUCE's form
`((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z)`. -/
@[inline] def readmeGenNewton (n : Nat) : Define :=
  newton! "sin(z) - 1" (m := "1 - 1im") (map := "((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z)")
    { bounds := ⟨-2 * pi / 3, -pi / 3, -pi / 6, pi / 6⟩, n, N := 33, iter := true, ϵ := some 0.05,
      cmap := "cubehelix" }

/-- `newton(:(z^3-1))` with the defaults. -/
@[inline] def defaultNewton (n : Nat) : Define := newton! "z^3 - 1" { n }

/-- `mandelbrot(:(z^2+c))` with the defaults. -/
@[inline] def defaultMandelbrot (n : Nat) : Define := mandelbrot! "z^2 + c" { n }

/-- `juliafill(:(z^2-0.06+0.67im))` with the defaults. -/
@[inline] def defaultJuliafill (n : Nat) : Define := juliafill! "z^2 - 0.06 + 0.67im" { n }

/-- The catalog: Julia name ↦ Lean `Define` at `n` columns. -/
def catalog : List (String × (Nat → Define)) := [
  ("readme_filled_julia", readmeFilledJulia),
  ("readme_mandelbrot", readmeMandelbrot),
  ("readme_newton", readmeNewton),
  ("readme_gen_newton", readmeGenNewton),
  ("default_newton", defaultNewton),
  ("default_mandelbrot", defaultMandelbrot),
  ("default_juliafill", defaultJuliafill),
  ("plane_juliafill", fun n => juliafill! "z^2 - 0.06 + 0.67im" { n, plane := true }),
  ("disk_juliafill", fun n => juliafill! "z^2 - 0.06 + 0.67im" { n, disk := true }),
  ("p_juliafill", fun n => juliafill! "z^2 - 0.06 + 0.67im" { n, p := 0.3 }),
  ("cubic_mandelbrot", fun n => mandelbrot! "z^3 + c" { n, N := 30, bounds := .interval (-1.5) 1.5 }),
  ("seed_mandelbrot", fun n =>
    mandelbrot! "z^2 + c" { n, N := 25, seed := ⟨0.1, 0.1⟩, bounds := ⟨-2, 1, -1.5, 1.5⟩ }),
  ("basilica_iter", fun n => juliafill! "z^2 - 1" { bounds := .interval (-2) 2, iter := true, n }),
  ("affine_juliafill", fun n => juliafill! "3z + 2" { bounds := .interval (-pi) pi, n }),
  ("newton_m2", fun n => newton! "z^3 - 1" (m := "2") { n, N := 37, ϵ := some 0.27, iter := true }),
  ("newton_mhalf", fun n => newton! "z^3 - 1" (m := "-0.5") { n, N := 10 }),
  ("newton_cubic5", fun n => newton! "z^3 - 2z - 5" { n }),
  ("newton_zim", fun n =>
    newton! "z^2 - im" (m := "-0.5 + 2im") (map := "((4im - 1) * (im - z ^ 2) + 4 * z ^ 2) / (4z)")
      { n, N := 10 }),
  ("newton_octic", fun n =>
    newton! "z^8 - 15z^4 - 16" (m := "1.5") { bounds := ⟨-2 * pi / 3, 0, -pi / 3, pi / 3⟩, n, N := 17 }),
  ("cos_juliafill", fun n => juliafill! "cos(z)" { bounds := .interval 0.5 2, n }),
  ("newton_exp", fun n =>
    newton! "exp(z) + 1" (map := "(ℯ ^ z * (z - 1) - 1) / ℯ ^ z")
      { bounds := .square (2 * pi), n, N := 27, iter := true })
]

/-- Look up a catalog entry. -/
def find? (name : String) : Option (Nat → Define) := (catalog.find? (·.1 == name)).map (·.2)

/-- The first stage of the chaining tests, `juliafill(:(z^2-0.06+0.67im), n = 41, N = 5)`. -/
def chainFirst : Define := juliafill! "z^2 - 0.06 + 0.67im" { n := 41, N := 5 }

/-- The second stage, `mandelbrot(:(z^2+c), n = 41, N = 10)`. -/
def chainSecond : Define := mandelbrot! "z^2 + c" { n := 41, N := 10 }

end Tests.Fatou.Catalog
