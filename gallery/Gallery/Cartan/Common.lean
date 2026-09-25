import Gallery.Common
import GrassmannPlot

/-!
# Checks shared by the Cartan figures

The Julia dumps of `oracle/gallery/cartan_common.jl` summarize long arrays as
`{"n", "stride", "sample", "sum", "sumabs"}` (every `stride`-th value and the sums over all
values); `summaryChecks` compares a Lean array with such a summary.
-/

namespace Gallery.CartanCommon

open Lean LeanPlot

/-- Compare `lean` with a Julia summary `{n, stride, sample, sum, sumabs}`: the length, the
sampled values (max relative deviation `≤ tol`) and the sum over all values (`|Σ - Σ_J| ≤
tol·max(1, Σ|·|)`). -/
def summaryChecks (label : String) (lean : FloatArray) (j : Json) (tol : Float := 1e-9) : Array Check :=
  let k := jnat (jget j "stride")
  let s := sumFinite lean
  let js := jfloat (jget j "sum")
  let jabs := jfloat (jget j "sumabs")
  let d := (s - js).abs / (if jabs > 1 then jabs else 1)
  #[eqCheck s!"{label}: count" lean.size (jnat (jget j "n")),
    closeCheck s!"{label} (every {k}th)" (every lean (max k 1)) (jfloats (jget j "sample")) tol,
    { label := s!"{label}: sum over all", ok := d ≤ tol, detail := s!"|Δ| / Σ|·| = {sci d} (tol {sci tol})" }]

/-- The coordinates `0 … d-1` of points as separate arrays. -/
def coordArrays (p : Pts3) (d : Nat) : Array FloatArray :=
  #[p.xs, p.ys, p.zs].extract 0 d

/-- The checks of a curve dumped by `dump_speed_curve`: coordinates and `speed`. -/
def speedCurveChecks (pts : Pts3) (speed : FloatArray) (j : Json) : Array Check :=
  let d := jnat (jget j "dim")
  let cs := coordArrays pts d
  (Array.range d).foldl (init := summaryChecks "speed" speed (jget j "speed") 1e-9) fun acc i =>
    acc ++ summaryChecks s!"x{i + 1}" (cs.getD i .empty) (jget j s!"x{i + 1}")

/-- The checks of segment points dumped by `dump_segments`. -/
def segmentChecks (pts : Pts3) (j : Json) (tol : Float := 1e-9) : Array Check :=
  let d := jnat (jget j "dim")
  let cs := coordArrays pts d
  (Array.range d).foldl (init := #[eqCheck "segment points" pts.size (jnat (jget j "n"))]) fun acc i =>
    acc ++ summaryChecks s!"x{i + 1}" (cs.getD i .empty) (jget j s!"x{i + 1}") tol

/-- The segment points of the plot items of a canvas, concatenated (the data of its
`linesegments`/`wireframe` marks). -/
def segmentsOf (c : GrassmannPlot.Canvas) : Array Pts3 :=
  c.items.filterMap fun it => match it.mark with
    | .segments (.xyz p) _ => some p
    | .segments (.xy p) _ => some (Pts3.ofArrays p.xs p.ys (FloatArray.mk (Array.replicate p.size 0)))
    | _ => none

end Gallery.CartanCommon
