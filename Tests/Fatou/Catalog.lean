import Tests.Fatou.Harness

/-!
The Lean side of the oracle catalog of `oracle/fatou/gen.jl`: every Julia `Define` there,
rebuilt with the Lean front-ends. Maps are written with `Fatou.C64`'s Julia-exact operations
in the order Julia evaluates the expression (`2 * z^3` scales by a real, `z - 1` subtracts
a real, `c₀` is a `ComplexF64` constant, …). Newton-mode entries pass REDUCE's factored
Newton map (the `F` field of `sets.json`) as `map`, which is what Julia iterates.

Each entry is a function of the column count `n`, so the same definition serves the
reduced dump and the full README resolution.
-/

namespace Tests.Fatou.Catalog

open _root_.Fatou

/-- `c₀ = -0.06 + 0.67im` of the README filled Julia set. -/
def c₀ : C64 := ⟨-0.06, 0.67⟩

/-- Julia's literal `0.67im`. -/
def i067 : C64 := ⟨0, 0.67⟩

/-- `(z^2 - 0.06) + 0.67im`, the map of the `juliafill` docstring and defaults. -/
@[inline] def jfMap (z _c : C64) : C64 := (z ^ 2 - (0.06 : Float)) + i067

/-- README filled Julia set (`README.md:68-74`). -/
@[inline] def readmeFilledJulia (n : Nat) : Define :=
  juliafill (fun z _ => z ^ 2 + c₀)
    { bounds := ⟨-1.5, 1.5, -1, 1⟩, N := 80, n, cmap := "gnuplot", iter := true,
      label := "z ^ 2 + (-0.06 + 0.67im)" }

/-- README Mandelbrot set (`README.md:78-82`). -/
@[inline] def readmeMandelbrot (n : Nat) : Define :=
  mandelbrot (fun z c => z ^ 2 + c)
    { n, N := 20, bounds := ⟨-1.91, 0.51, -1.21, 1.21⟩, cmap := "gist_earth", label := "z ^ 2 + c" }

/-- REDUCE's Newton map of `z^3 - 1` with `m = 1`: `(2 * z ^ 3 + 1) / (3 * z ^ 2)`. -/
@[inline] def newtonCubic (z _c : C64) : C64 := ((2 : Float) * z ^ 3 + (1 : Float)) / ((3 : Float) * z ^ 2)

/-- README Newton fractal of `z^3 - 1` (`README.md:98-104`). -/
@[inline] def readmeNewton (n : Nat) : Define :=
  newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { n, ϵ := some 0.1, N := 25, iter := true, cmap := "jet", label := "z ^ 3 - 1" }
    (map := some newtonCubic)

/-- REDUCE's generalized Newton map of `sin(z) - 1` with `m = 1 - 1im`:
`((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z)`. -/
@[inline] def newtonSin (z _c : C64) : C64 :=
  ((C64.sin z - (1 : Float)) * (⟨-1, 1⟩ : C64) + C64.cos z * z) / C64.cos z

/-- README generalized Newton fractal (`README.md:108-116`). -/
@[inline] def readmeGenNewton (n : Nat) : Define :=
  newton (fun z _ => C64.sin z - (1 : Float)) (fun z _ => C64.cos z)
    { m := some (.complexInt 1 (-1)), bounds := ⟨-2 * pi / 3, -pi / 3, -pi / 6, pi / 6⟩, n, N := 33,
      iter := true, ϵ := some 0.05, cmap := "cubehelix", label := "sin(z) - 1" }
    (map := some newtonSin)

/-- `newton(:(z^3-1))` with the defaults. -/
@[inline] def defaultNewton (n : Nat) : Define :=
  newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2) { n, label := "z ^ 3 - 1" }
    (map := some newtonCubic)

/-- `mandelbrot(:(z^2+c))` with the defaults. -/
@[inline] def defaultMandelbrot (n : Nat) : Define :=
  mandelbrot (fun z c => z ^ 2 + c) { n, label := "z ^ 2 + c" }

/-- `juliafill(:(z^2-0.06+0.67im))` with the defaults. -/
@[inline] def defaultJuliafill (n : Nat) : Define :=
  juliafill jfMap { n, label := "(z ^ 2 - 0.06) + 0.67im" }

/-- The catalog: Julia name ↦ Lean `Define` at `n` columns. -/
def catalog : List (String × (Nat → Define)) := [
  ("readme_filled_julia", readmeFilledJulia),
  ("readme_mandelbrot", readmeMandelbrot),
  ("readme_newton", readmeNewton),
  ("readme_gen_newton", readmeGenNewton),
  ("default_newton", defaultNewton),
  ("default_mandelbrot", defaultMandelbrot),
  ("default_juliafill", defaultJuliafill),
  ("plane_juliafill", fun n => juliafill jfMap { n, plane := true, label := "(z ^ 2 - 0.06) + 0.67im" }),
  ("disk_juliafill", fun n => juliafill jfMap { n, disk := true, label := "(z ^ 2 - 0.06) + 0.67im" }),
  ("p_juliafill", fun n => juliafill jfMap { n, p := 0.3, label := "(z ^ 2 - 0.06) + 0.67im" }),
  ("cubic_mandelbrot", fun n =>
    mandelbrot (fun z c => z ^ 3 + c) { n, N := 30, bounds := .interval (-1.5) 1.5, label := "z ^ 3 + c" }),
  ("seed_mandelbrot", fun n =>
    mandelbrot (fun z c => z ^ 2 + c)
      { n, N := 25, seed := ⟨0.1, 0.1⟩, bounds := ⟨-2, 1, -1.5, 1.5⟩, label := "z ^ 2 + c" }),
  ("basilica_iter", fun n =>
    juliafill (fun z _ => z ^ 2 - (1 : Float))
      { bounds := .interval (-2) 2, iter := true, n, label := "z ^ 2 - 1" }),
  ("affine_juliafill", fun n =>
    juliafill (fun z _ => (3 : Float) * z + (2 : Float)) { bounds := .interval (-pi) pi, n, label := "3z + 2" }),
  ("newton_m2", fun n =>
    newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
      { m := some 2, n, N := 37, ϵ := some 0.27, iter := true, label := "z ^ 3 - 1" }
      (map := some fun z _ => (z ^ 3 + (2 : Float)) / ((3 : Float) * z ^ 2))),
  ("newton_mhalf", fun n =>
    newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
      { m := some (-0.5), n, N := 10, label := "z ^ 3 - 1" }
      (map := some fun z _ => ((7 : Float) * z ^ 3 - (1 : Float)) / ((6 : Float) * z ^ 2))),
  ("newton_cubic5", fun n =>
    newton (fun z _ => z ^ 3 - (2 : Float) * z - (5 : Float)) (fun z _ => (3 : Float) * z ^ 2 - (2 : Float))
      { n, label := "(z ^ 3 - 2z) - 5" }
      (map := some fun z _ => ((2 : Float) * z ^ 3 + (5 : Float)) / ((3 : Float) * z ^ 2 - (2 : Float)))),
  ("newton_zim", fun n =>
    newton (fun z _ => z ^ 2 - C64.I) (fun z _ => (2 : Float) * z)
      { m := some (.complexFloat (-0.5) 2), n, N := 10, label := "z ^ 2 - im" }
      (map := some fun z _ =>
        ((⟨-1, 4⟩ : C64) * (C64.I - z ^ 2) + (4 : Float) * z ^ 2) / ((4 : Float) * z))),
  ("newton_octic", fun n =>
    newton (fun z _ => z ^ 8 - (15 : Float) * z ^ 4 - (16 : Float))
      (fun z _ => (8 : Float) * z ^ 7 - (60 : Float) * z ^ 3)
      { m := some 1.5, bounds := ⟨-2 * pi / 3, 0, -pi / 3, pi / 3⟩, n, N := 17,
        label := "(z ^ 8 - 15 * z ^ 4) - 16" }
      (map := some fun z _ =>
        ((13 : Float) * z ^ 8 - (75 : Float) * z ^ 4 + (48 : Float)) /
          ((8 : Float) * ((2 : Float) * z ^ 4 - (15 : Float)) * z ^ 3))),
  ("cos_juliafill", fun n =>
    juliafill (fun z _ => C64.cos z) { bounds := .interval 0.5 2, n, label := "cos(z)" }),
  ("newton_exp", fun n =>
    newton (fun z _ => C64.exp z + (1 : Float)) (fun z _ => C64.exp z)
      { bounds := .square (2 * pi), n, N := 27, iter := true, label := "exp(z) + 1" }
      (map := some fun z _ => (C64.exp z * (z - (1 : Float)) - (1 : Float)) / C64.exp z))
]

/-- Look up a catalog entry. -/
def find? (name : String) : Option (Nat → Define) := (catalog.find? (·.1 == name)).map (·.2)

/-- The first stage of the chaining tests, `juliafill(:(z^2-0.06+0.67im), n = 41, N = 5)`. -/
def chainFirst : Define := juliafill jfMap { n := 41, N := 5, label := "(z ^ 2 - 0.06) + 0.67im" }

/-- The second stage, `mandelbrot(:(z^2+c), n = 41, N = 10)`. -/
def chainSecond : Define := mandelbrot (fun z c => z ^ 2 + c) { n := 41, N := 10, label := "z ^ 2 + c" }

end Tests.Fatou.Catalog
