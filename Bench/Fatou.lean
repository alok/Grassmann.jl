import Bench.Harness
import Tests.Fatou.Catalog

/-!
# `fatou`: escape-time rasters

Julia twin: `oracle/bench/fatou.jl`, run with every core (`--threads=auto`). Each raster is
timed sequentially (`*_seq`, against a handwritten Julia kernel with Fatou's exact grid and loop,
one thread) and in parallel (`*_par`, Lean tasks against the same kernel threaded over rows like
`Fatou.Compute`); `*_fatoujl` is `Fatou.fatou` itself (Julia-only: its maps go through
`invokelatest`). The check is the total iteration count, equal on both sides.
-/

namespace Bench.Fatou

open _root_.Fatou Tests.Fatou.Catalog Bench

/-- Sum of the iteration counts (forces the whole raster). -/
def iterSum {r c : Nat} (Z : FilledSet r c) : Nat :=
  Z.iterHistogram.zipIdx.foldl (fun acc (h, k) => acc + h * k) 0

/-- The README Mandelbrot benchmark raster (`N = 100`, `[-2, 0.5] × [-1.25, 1.25]`). -/
@[inline] def mandel (n : Nat) : Define :=
  mandelbrot (fun z c => z ^ 2 + c) { n, N := 100, bounds := ⟨-2, 0.5, -1.25, 1.25⟩ }

/-- Sequential and parallel cases of one raster `mk n`. Inlined, so that `fatou` is specialized
on the map of `mk` (an opaque `Define` would run the generic, boxed kernel ~25× slower); only
the size goes through `blackBox`, so the raster is rebuilt on every call and never a closed
term. -/
@[inline] def rasterCases (tag param : String) (mk : Nat → Define) (n : Nat) : BenchM Unit := do
  bench s!"{tag}_seq" (param := param) fun s => iterSum (fatou (mk (blackBox s n)) (par := false))
  bench s!"{tag}_par" (param := param) fun s => iterSum (fatou (mk (blackBox s n)))

/-- The suite; sizes come from the configuration so nothing is hoisted into a closed term. -/
def suite : Suite := ⟨"fatou", do
  let n ← size 1000 100
  rasterCases "mandelbrot" s!"{n}² N=100" mandel n
  let m ← size 1501 151
  rasterCases "filled_julia" s!"{m}×{(m * 2 + 2) / 3} N=80" readmeFilledJulia m
  let k ← size 800 100
  rasterCases "newton" s!"{k}² N=25" readmeNewton k
  let g := k * 5 / 8
  rasterCases "gen_newton" s!"{g}² N=33" readmeGenNewton g⟩

end Bench.Fatou
