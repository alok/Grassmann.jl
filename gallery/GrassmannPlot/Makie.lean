import GrassmannPlot.Convert

/-!
# Makie's functions as a type-directed dispatch

Cartan's `MakieExt.jl` adds *methods* to Makie's generic functions: `lines(t::PlaneCurve)`,
`lines(t::RectangleMap)`, `mesh(M::TensorField{…,2,GridBundle})`, … Julia picks the method from
the argument types. Here each Makie function is a tag `Method`, and a method for arguments of
type `T` is an instance `MakiePlot m T`, so `lines t` resolves by the type of `t` exactly as
Julia's dispatch does (a real function of a real variable, a curve, a grid surface, a simplex
mesh, …). Two-argument methods (`lines(t, f)`, `mesh(M, f)`, `scaledarrows(M, t)`) are
instances on pairs.

The generic methods of `MakieExt.jl:60-84` are instances for every function at once:

* **Components** (`Components = AbstractVector{<:TensorField}`, `Cartan.jl:608`, e.g. the output
  of `boundarycomponents`): plot the first, then add the others (`Array T`);
* **LocalTensor**: plot the fiber (`LocalTensor B T`);
* packed fields (`AnyField`), the Lean form of a field whose base is decided at run time.

`m!(t)` is `Canvas.plot m c t`, `m(t)` is `plot m t` (a fresh canvas of the method's dimension).
-/

namespace GrassmannPlot

open LeanPlot Cartan

/-- The Makie (and Cartan) plotting functions Cartan gives methods for (`MakieExt.jl:60-84`). -/
inductive Method where
  | lines | linesegments | linegraph | scatter | text | mesh | wireframe | surface
  | contour | contourf | contour3d | heatmap | streamplot | arrows | arrows2d | arrows3d
  | scaledarrows | arrowsbundle | scaledfield | scaledbundle | planes | spaces
  | scaledplanes | scaledspaces | planesbundle | spacesbundle | graylines | voxels
  deriving BEq, Repr, Inhabited

/-- A Cartan method of the Makie function `m` for arguments of type `T`: `plot c t a` draws `t`
on the current axis (Julia `m!(t; a...)`), `dim t` is the dimension of the axis the
non-mutating `m(t)` creates (2: `Axis`, 3: `LScene`). -/
class MakiePlot (m : Method) (T : Type) where
  /-- Julia `m!(t; attrs...)`. -/
  plot : Canvas → T → Attrs → Canvas
  /-- The dimension of the automatic axis of `m(t)`. -/
  dim : T → Nat

/-- Julia `m!(t; attrs...)`: draw on the current axis. -/
@[inline] def Canvas.plot (m : Method) {T : Type} [MakiePlot m T] (c : Canvas) (t : T) (a : Attrs := {}) :
    Canvas := MakiePlot.plot m c t a

/-- Julia `m(t; attrs...)`: a fresh axis of the method's dimension with `t` drawn on it. -/
@[inline] def plot (m : Method) {T : Type} [MakiePlot m T] (t : T) (a : Attrs := {}) : Canvas :=
  MakiePlot.plot m (Canvas.fresh (MakiePlot.dim m t)) t a

/-! ## Generic methods (`MakieExt.jl:60-84`) -/

/-- Julia `fun(t::Components)`: the first component, then `fun!` of the others, all on one
axis. -/
instance instComponents {m : Method} {T : Type} [MakiePlot m T] : MakiePlot m (Array T) where
  plot c ts a := ts.foldl (fun c t => MakiePlot.plot m c t a) c
  dim ts := match ts[0]? with | some t => MakiePlot.dim m t | none => 2

/-- Julia `fun(t::LocalTensor)` = `fun(fiber(t))`. -/
instance instLocalTensor {m : Method} {B T : Type} [MakiePlot m T] : MakiePlot m (LocalTensor B T) where
  plot c t a := MakiePlot.plot m c t.fiber a
  dim t := MakiePlot.dim m t.fiber

/-- A packed field (`AnyField`): the method of its field. -/
instance instAnyField {m : Method} {M F : Type} [FrameBundle M] [FlatFiber F]
    [inst : ∀ b : M, MakiePlot m (TensorField b F)] : MakiePlot m (AnyField M F) where
  plot c t a := (inst t.base).plot c t.field a
  dim t := (inst t.base).dim t.field

/-! ## The named functions -/

section Named

variable {T : Type}

/-- Makie `lines(t)` (Cartan methods `MakieExt.jl:160-232`). -/
def lines [MakiePlot .lines T] (t : T) (a : Attrs := {}) : Canvas := plot .lines t a
/-- Makie `linesegments(t)`. -/
def linesegments [MakiePlot .linesegments T] (t : T) (a : Attrs := {}) : Canvas := plot .linesegments t a
/-- Cartan `linegraph(t)` (`MakieExt.jl:184-206, 627-797`). -/
def linegraph [MakiePlot .linegraph T] (t : T) (a : Attrs := {}) : Canvas := plot .linegraph t a
/-- Makie `scatter(t)` (`MakieExt.jl:604-611`). -/
def scatter [MakiePlot .scatter T] (t : T) (a : Attrs := {}) : Canvas := plot .scatter t a
/-- Makie `text(t)` (`MakieExt.jl:613-616`). -/
def text [MakiePlot .text T] (t : T) (a : Attrs := {}) : Canvas := plot .text t a
/-- Makie `mesh(t)` (`MakieExt.jl:816-874`). -/
def mesh [MakiePlot .mesh T] (t : T) (a : Attrs := {}) : Canvas := plot .mesh t a
/-- Makie `wireframe(t)` (`MakieExt.jl:808-825`). -/
def wireframe [MakiePlot .wireframe T] (t : T) (a : Attrs := {}) : Canvas := plot .wireframe t a
/-- Makie `surface(t)` (`MakieExt.jl:452-467, 876-891`). -/
def surface [MakiePlot .surface T] (t : T) (a : Attrs := {}) : Canvas := plot .surface t a
/-- Makie `contour(t)` (`MakieExt.jl:468-491`). -/
def contour [MakiePlot .contour T] (t : T) (a : Attrs := {}) : Canvas := plot .contour t a
/-- Makie `contourf(t)`. -/
def contourf [MakiePlot .contourf T] (t : T) (a : Attrs := {}) : Canvas := plot .contourf t a
/-- Makie `contour3d(t)`. -/
def contour3d [MakiePlot .contour3d T] (t : T) (a : Attrs := {}) : Canvas := plot .contour3d t a
/-- Makie `heatmap(t)`. -/
def heatmap [MakiePlot .heatmap T] (t : T) (a : Attrs := {}) : Canvas := plot .heatmap t a
/-- Makie `streamplot(t)` (`MakieExt.jl:522-558`). -/
def streamplot [MakiePlot .streamplot T] (t : T) (a : Attrs := {}) : Canvas := plot .streamplot t a
/-- Makie `arrows(t)` (`MakieExt.jl:562-597`): `arrows2d`, or `arrows3d` for 3-D fibers. -/
def arrows [MakiePlot .arrows T] (t : T) (a : Attrs := {}) : Canvas := plot .arrows t a
/-- Makie `arrows2d(t)`. -/
def arrows2d [MakiePlot .arrows2d T] (t : T) (a : Attrs := {}) : Canvas := plot .arrows2d t a
/-- Makie `arrows3d(t)`. -/
def arrows3d [MakiePlot .arrows3d T] (t : T) (a : Attrs := {}) : Canvas := plot .arrows3d t a
/-- Cartan `scaledarrows(M, t)` (`MakieExt.jl:371-385`). -/
def scaledarrows [MakiePlot .scaledarrows T] (t : T) (a : Attrs := {}) : Canvas := plot .scaledarrows t a
/-- Makie `voxels(t)` (`MakieExt.jl:443-448`). -/
def voxels [MakiePlot .voxels T] (t : T) (a : Attrs := {}) : Canvas := plot .voxels t a

end Named

namespace Canvas

variable {T : Type}

/-- Makie `lines!(t)`. -/
def lines [MakiePlot .lines T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .lines t a
/-- Makie `linesegments!(t)`. -/
def linesegments [MakiePlot .linesegments T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas :=
  c.plot .linesegments t a
/-- Cartan `linegraph!(t)`. -/
def linegraph [MakiePlot .linegraph T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .linegraph t a
/-- Makie `scatter!(t)`. -/
def scatter [MakiePlot .scatter T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .scatter t a
/-- Makie `text!(t)`. -/
def text [MakiePlot .text T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .text t a
/-- Makie `mesh!(t)`. -/
def mesh [MakiePlot .mesh T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .mesh t a
/-- Makie `wireframe!(t)`. -/
def wireframe [MakiePlot .wireframe T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .wireframe t a
/-- Makie `surface!(t)`. -/
def surface [MakiePlot .surface T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .surface t a
/-- Makie `contour!(t)`. -/
def contour [MakiePlot .contour T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .contour t a
/-- Makie `contourf!(t)`. -/
def contourf [MakiePlot .contourf T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .contourf t a
/-- Makie `contour3d!(t)`. -/
def contour3d [MakiePlot .contour3d T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .contour3d t a
/-- Makie `heatmap!(t)`. -/
def heatmap [MakiePlot .heatmap T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .heatmap t a
/-- Makie `streamplot!(t)`. -/
def streamplot [MakiePlot .streamplot T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .streamplot t a
/-- Makie `arrows!(t)`. -/
def arrows [MakiePlot .arrows T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .arrows t a
/-- Makie `arrows2d!(t)`. -/
def arrows2d [MakiePlot .arrows2d T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .arrows2d t a
/-- Makie `arrows3d!(t)`. -/
def arrows3d [MakiePlot .arrows3d T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .arrows3d t a
/-- Cartan `scaledarrows!(M, t)`. -/
def scaledarrows [MakiePlot .scaledarrows T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas :=
  c.plot .scaledarrows t a
/-- Makie `voxels!(t)`. -/
def voxels [MakiePlot .voxels T] (c : Canvas) (t : T) (a : Attrs := {}) : Canvas := c.plot .voxels t a

end Canvas

end GrassmannPlot
