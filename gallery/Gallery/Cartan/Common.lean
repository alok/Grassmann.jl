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

/-- Compare points with a Julia `pts_summary` (`{n, dim, x1, x2, …}`). -/
def ptsChecks (label : String) (p : Pts3) (j : Json) (tol : Float := 1e-9) : Array Check :=
  let d := jnat (jget j "dim")
  let cs := coordArrays p d
  (Array.range d).foldl (init := #[eqCheck s!"{label}: points" p.size (jnat (jget j "n"))]) fun acc i =>
    acc ++ summaryChecks s!"{label} x{i + 1}" (cs.getD i .empty) (jget j s!"x{i + 1}") tol

/-- Compare NaN-separated polylines with a Julia `lines_moments` dump (order-independent: the
point and separator counts, `Σxᵢ` and `Σxᵢxⱼ` over the non-NaN points, relative tolerance `tol`). -/
def momentsChecks (label : String) (p : Pts3) (j : Json) (tol : Float := 1e-6) : Array Check :=
  let d := jnat (jget j "dim")
  let cs := coordArrays p d
  let good := (List.range p.size).filter fun i => !(cs.any fun c => (c.get! i).isNaN)
  let m1 := (List.range d).map fun a => good.foldl (fun s i => s + (cs.getD a .empty).get! i) 0
  let m2 := (List.range d).flatMap fun a => (List.range (d - a)).map fun b =>
    good.foldl (fun s i => s + (cs.getD a .empty).get! i * (cs.getD (a + b) .empty).get! i) 0
  let lean : FloatArray := ⟨(m1 ++ m2).toArray⟩
  let julia : FloatArray := ⟨(jfloats (jget j "m1")).data ++ (jfloats (jget j "m2")).data⟩
  #[eqCheck s!"{label}: points" p.size (jnat (jget j "n")),
    eqCheck s!"{label}: line breaks" (p.size - good.length) (jnat (jget j "nnan")),
    closeCheck s!"{label}: moments Σx, Σxx" lean julia tol]

/-- The positions of the `k`-th plot item of a canvas (lines, segments, scatter, arrows origins,
mesh vertices), as 3-D points. -/
def itemPoints (c : GrassmannPlot.Canvas) (k : Nat) : Pts3 :=
  let pos (p : Pos) : Pts3 := match p with
    | .xyz q => q
    | .xy q => Pts3.ofArrays q.xs q.ys (FloatArray.mk (Array.replicate q.size 0))
  match c.items[k]? with
  | some it => match it.mark with
    | .lines p _ | .segments p _ | .scatter p _ | .text p _ _ => pos p
    | .arrows o _ _ => pos o
    | .mesh m => m.mesh.pos
    | _ => default
  | none => default

/-- The mapped colour values of the `k`-th plot item of a canvas (empty if not colour-mapped). -/
def itemColorValues (c : GrassmannPlot.Canvas) (k : Nat) : FloatArray :=
  let vals (s : ColorSpec) : FloatArray := match s with
    | .values v _ => v
    | _ => .empty
  match c.items[k]? with
  | some it => match it.mark with
    | .lines _ s | .segments _ s => vals s.color
    | .scatter _ s => vals s.color
    | .arrows _ _ s => vals s.color
    | .mesh m => vals m.color
    | _ => .empty
  | none => .empty

/-- The segment points of the plot items of a canvas, concatenated (the data of its
`linesegments`/`wireframe` marks). -/
def segmentsOf (c : GrassmannPlot.Canvas) : Array Pts3 :=
  c.items.filterMap fun it => match it.mark with
    | .segments (.xyz p) _ => some p
    | .segments (.xy p) _ => some (Pts3.ofArrays p.xs p.ys (FloatArray.mk (Array.replicate p.size 0)))
    | _ => none

end Gallery.CartanCommon
