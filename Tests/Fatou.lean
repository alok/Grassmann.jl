import Tests.Fatou.Complex
import Tests.Fatou.Grid
import Tests.Fatou.Sets
import Tests.Fatou.Orbit
import Tests.Fatou.Color

/-!
Fatou test aggregator: oracle goldens from `oracle/fatou/gen.jl` and `oracle/fatou/mpl.py`
(`oracle/golden/fatou/`), plus compile-time checks.
-/

namespace Tests.Fatou

open _root_.Fatou

/-! Compile-time checks. -/

-- titles follow Julia's `String(K)` (`src/Fatou.jl:369-372`)
#guard (mandelbrot (fun z c => z ^ 2 + c) { label := "z ^ 2 + c" }).title == "f : z ↦ z ^ 2 + c, limit"
#guard (newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2)
    { iter := true, label := "z ^ 3 - 1" }).title == "f : z ↦ z ^ 3 - 1, m = 1, iter."
-- `typeplot` says "roots" for `m = 1` even outside Newton mode (Julia quirk)
#guard (juliafill (fun z _ => z) { m := some 1 }).typeplot == "roots"
-- per-front-end defaults (port-notes/fatou.md §2.3)
#guard (newton (fun z _ => z) (fun _ _ => 1)).spec.ϵ == 0.01
#guard (juliafill (fun z _ => z)).spec.ϵ == 4
#guard (newton (fun z _ => z) (fun _ _ => 1)).spec.m.isOne
-- sizes: rows = round((yb-ya)/(xb-xa)·n), ties to even
#guard ({ bounds := ⟨-1.5, 1.5, -1, 1⟩, n := 1501 } : Rectangle).rows == 1001
#guard ({ bounds := ⟨0, 2, 0, 1⟩, n := 5 } : Rectangle).rows == 2
#guard ({ bounds := ⟨0, 2, 0, 1⟩, n := 7 } : Rectangle).rows == 4
-- the verbatim per-point goldens of port-notes/fatou.md §4.4
#guard ((mandelbrot (fun z c => z ^ 2 + c) { N := 20 }).orbit ⟨-2, 0⟩).1 == 1
#guard ((mandelbrot (fun z c => z ^ 2 + c) { N := 20 }).orbit ⟨1, 1⟩).2 == ⟨1, 3⟩
#guard ((newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2) { ϵ := some 0.1, N := 25 }
    (map := some Catalog.newtonCubic)).orbit ⟨2.1, 0⟩).2.re == 1.015805042940846
#guard ((newton (fun z _ => z ^ 3 - (1 : Float)) (fun z _ => (3 : Float) * z ^ 2) { ϵ := some 0.1, N := 25 }
    (map := some Catalog.newtonCubic)).orbit ⟨0, 0⟩).2.re.isNaN
-- basin templates (`src/internals.jl:22-32`)
#guard basin true 0 "" ==
  "$D_0(\\epsilon) = \\left\\{ z\\in\\mathbb{C}: \\left|\\,z - r_i\\,\\right|<\\epsilon,\\,\\forall r_i(\\,f(r_i)=0 )\\right\\}$"
-- LaTeXStrings' wrapping rule
#guard latexstring "x" == "$x$" && latexstring "$x$" == "$x$" && latexstring "a\\$b" == "$a\\$b$"

/-- Run one suite, turning an exception into a failure. -/
def runSuite (name : String) (m : TestM Unit) : IO (Nat × Nat) := do
  let t : Tally ← try (do let (_, t) ← m.run {}; pure t) catch e => do
    IO.eprintln s!"  {name} error: {e}"
    pure { failed := 1 }
  IO.println s!"  {name}: {t.passed} passed, {t.failed} failed"
  return (t.passed, t.failed)

/-- Run every Fatou suite; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "Fatou:"
  let mut passed := 0
  let mut failed := 0
  for (name, suite) in [("complex", Complex.run), ("grids", Grid.run), ("sets", Sets.run),
      ("orbits", Orbit.run), ("colour", Color.run)] do
    let (p, f) ← runSuite name suite
    passed := passed + p
    failed := failed + f
  return (passed, failed)

end Tests.Fatou
