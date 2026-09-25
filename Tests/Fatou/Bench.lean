import Tests.Fatou.Catalog

/-!
Fatou benchmarks (hot path: the escape-time raster kernel). Run through an executable that
calls `Tests.Fatou.Bench.run`; `smoke := true` shrinks everything for CI.

Reference numbers (Apple M4 Max, 16 threads, Julia 1.13) are in `docs/PERF.md`:
`oracle`-side timings come from the handwritten Julia kernel with Fatou's exact grid and
loop semantics, and from `Fatou.fatou` itself.
-/

namespace Tests.Fatou.Bench

open _root_.Fatou Tests.Fatou.Catalog

/-- Best wall time in milliseconds of `reps` runs, and the last result. -/
def best {α : Type} (reps : Nat) (act : Unit → IO α) : IO (Float × α) := do
  let mut t := 1.0e30
  let mut last ← act ()
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    last ← act ()
    let t1 ← IO.monoNanosNow
    t := min t ((t1 - t0).toFloat / 1.0e6)
  return (t, last)

/-- Sum of the iteration counts (a checksum that forces the whole raster). -/
def iterSum {r c : Nat} (Z : FilledSet r c) : Nat :=
  Z.iterHistogram.zipIdx.foldl (fun acc (h, k) => acc + h * k) 0

/-- Run the benchmarks; sizes come from `n` so nothing is hoisted into a closed term. -/
def run (smoke : Bool := false) : IO Unit := do
  let reps := if smoke then 1 else 5
  let n : Nat := if smoke then 100 else 1000
  let bounds : Bounds := ⟨-2, 0.5, -1.25, 1.25⟩
  let (tp, sp) ← best reps fun _ => pure (iterSum (fatou (mandelbrot (fun z c => z ^ 2 + c) { n, N := 100, bounds })))
  let (ts, _) ← best reps fun _ =>
    pure (iterSum (fatou (mandelbrot (fun z c => z ^ 2 + c) { n, N := 100, bounds }) (par := false)))
  IO.println s!"fatou mandelbrot {n}×{n} N=100: parallel {tp} ms, sequential {ts} ms ({sp} iterations)"
  let m : Nat := if smoke then 151 else 1501
  let (tj, sj) ← best reps fun _ => pure (iterSum (fatou (readmeFilledJulia m)))
  let (tjs, _) ← best reps fun _ => pure (iterSum (fatou (readmeFilledJulia m) (par := false)))
  IO.println s!"fatou README filled Julia n={m}: parallel {tj} ms, sequential {tjs} ms ({sj} iterations)"
  let k : Nat := if smoke then 100 else 800
  let (tn, sn) ← best reps fun _ => pure (fatou (readmeNewton k)).iter.size
  let (tns, _) ← best reps fun _ => pure (fatou (readmeNewton k) (par := false)).iter.size
  IO.println s!"fatou README Newton n={k}: parallel {tn} ms, sequential {tns} ms ({sn / 2} pixels)"
  let g := k * 5 / 8
  let (tg, sg) ← best reps fun _ => pure (fatou (readmeGenNewton g)).iter.size
  let (tgs, _) ← best reps fun _ => pure (fatou (readmeGenNewton g) (par := false)).iter.size
  IO.println s!"fatou README generalized Newton n={g}: parallel {tg} ms, sequential {tgs} ms ({sg / 2} pixels)"

end Tests.Fatou.Bench
