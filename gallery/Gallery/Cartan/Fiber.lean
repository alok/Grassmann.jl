import Gallery.Cartan.Common
import Gallery.Cartan.Versors
import Gallery.Grassmann.Figures

/-!
# Cartan.jl `docs/src/fiber.md` sessions that need only the Cartan core

Each figure is the verbatim Julia session drawn with `GrassmannPlot` (Cartan's Makie methods):

| figure | Julia (`fiber.md`) | inventory |
|---|---|---|
| `cartan-riemann-{torus,orbit-2,orbit-4,helix}` | `lines(V(2,3,4).(f.(pts)))`, `pts = TensorField(-2π:0.0001:2π)` (`:477-493`) | C5 |
| `cartan-bivector-1 … -6` | `streamplot(tensorfield(t).(vdom))` over a 31×31 grid (`:495-509`) | C6 |
| `cartan-conformal-stream-{1,2}` | `streamplot(tensorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)).(vdom), gridsize=(10,10))` over 31³ grids (`:511-523`) | C7 |
| `cartan-circle`, `cartan-sphere-wireframe` | `lines(circ)`, `wireframe(spher.(SphereParameter(60,60)))` (`:602-613`) | C9 |
| `cartan-hopf` | `alteration!(stereohopf.(HopfParameter()), wireframe, wireframe!)` (`:765-775`) | C16 |

Checks: the plotted coordinates and the `speed` colouring of the curves (sampled and summed)
against `oracle/gallery/cartan-*.jl`; Makie's `streamplot_impl` of Julia's interpolated grid field
(arrow and point counts, a Float32 hash of every line point); the wireframe segment points.
-/

namespace Gallery.CartanFigs

open Lean LeanPlot Cartan Grassmann DirectSum JuliaBase GrassmannPlot
open Gallery.CartanVersors Gallery.CartanCommon

/-- Julia `-2*pi:0.0001:2*pi`, the parameter of the `fiber.md` curves (125 664 points). -/
def ptsAxis : Cartan.Axis := Cartan.Axis.colon (-twoPiF) (f64! 0.0001) twoPiF

/-- A curve `t ↦ f t` over `ptsAxis` (Julia `f.(pts)`). -/
def curveField (f : Float → Chain ℝ3 1 Float) : TensorField (GridBundle.ofAxis ptsAxis) (Chain ℝ3 1 Float) :=
  TensorField.ofAxisFn ptsAxis f

/-- The Cartan documentation URL of a `fiber.md` session. -/
def fiberDoc : String := "https://cartan.crucialflow.com/dev/fiber"

/-- A speed-coloured space-curve entry (`lines(curve)`, drawn in an `Axis3`). -/
def curveEntry (name title source : String) (f : Float → Chain ℝ3 1 Float) : Entry :=
  { name, title, source, group := "Cartan (fiber.md)", upstream := fiberDoc
    build := fun j? => do
      let t := curveField f
      let c := GrassmannPlot.lines t
      let checks := match j? with
        | some j => speedCurveChecks (curvePoints t) ((speedValues t).getD .empty) j
        | none => #[]
      return { fig := c.figure (600, 500), checks } }

/-! ## C6: bivector streamplots over grid fields -/

/-- Julia `-1.5:0.1:1.5`. -/
def gridAxis : Cartan.Axis := Cartan.Axis.colon (f64! -1.5) (f64! 0.1) (f64! 1.5)

/-- Julia `TensorField(ProductSpace{V}(-1.5:0.1:1.5,-1.5:0.1:1.5))`. -/
def plane : GridBundle 2 (AffinePoint 2) := GridBundle.ofSpace (.ofAxes #v[gridAxis, gridAxis])

/-- Julia `tensorfield(t).(vdom)` of plane versor `k`. -/
def bivectorField (k : Nat) : TensorField plane (Chain ℝ2 1 Float) :=
  TensorField.tabulate2 plane (planeField k)

/-- A C6 entry. -/
def bivectorEntry (k : Nat) : Entry :=
  { name := s!"cartan-bivector-{k}", group := "Cartan (fiber.md)", upstream := fiberDoc
    title := s!"Streamlines of the 31×31 grid field of {planeText k} ({if k ≤ 4 then "Euclidean" else "Lobachevskian"} plane)"
    source := s!"`{if k ≤ 4 then "basis\"2\"" else "@basis S\"+-\""}; vdom = TensorField(ProductSpace\{V}(-1.5:0.1:1.5,-1.5:0.1:1.5)); streamplot(tensorfield({planeText k}).(vdom))` (`fiber.md:495-509`)"
    build := fun j? => do
      let t := bivectorField k
      let r := stream2 t {}
      let c := drawStream (Canvas.fresh 2) r 15 {}
      return { fig := c.figure, checks := match j? with | some j => GrassmannFigs.streamChecks r j | none => #[] } }

/-! ## C7: conformal 3-D streamplots over grid fields -/

/-- Julia `TensorField(ProductSpace{W}(-1.5:0.1:1.5,…))` in three dimensions. -/
def cube : GridBundle 3 (AffinePoint 3) := GridBundle.ofSpace (.ofAxes #v[gridAxis, gridAxis, gridAxis])

/-- Julia `tensorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)).(vdom)` with the grid points in the generators
`w₁ w₂ w₃` of `S"∞+++"`. -/
def conformalField (w₁ w₂ w₃ : Nat) : TensorField cube (Chain ℝ3 1 Float) :=
  TensorField.tabulate3 cube (sphereAt w₁ w₂ w₃)

/-- A C7 entry. -/
def conformalEntry (k : Nat) (w₁ w₂ w₃ : Nat) (sub : String) : Entry :=
  { name := s!"cartan-conformal-stream-{k}", group := "Cartan (fiber.md)", upstream := fiberDoc
    title := s!"Streamlines of the 31³ grid field of exp((π/4)(v12+v∞3)) on ProductSpace\{{sub}}"
    source := s!"`@basis S\"∞+++\"; vdom = TensorField(ProductSpace\{{sub}}(-1.5:0.1:1.5,…)); streamplot(tensorfield(exp((pi/4)*(v12+v∞3)),V(2,3,4)).(vdom),gridsize=(10,10))` (`fiber.md:511-523`)"
    build := fun j? => do
      let t := conformalField w₁ w₂ w₃
      let (r, s) := stream3 t { gridsize := some #[10, 10] }
      let c := drawStream (Canvas.fresh 3) r s {}
      return { fig := c.figure (600, 500), checks := match j? with | some j => GrassmannFigs.streamChecks r j | none => #[] } }

/-! ## C9: circle and sphere -/

/-- Julia `t = TensorField(0:0.001:2pi); circ = Chain.(cos(t),sin(t))`. -/
def circle : TensorField (GridBundle.ofAxis (Cartan.Axis.colon 0 (f64! 0.001) twoPiF)) (Chain ℝ2 1 Float) :=
  TensorField.ofAxisFn _ fun x => Chain.ofFn fun i => if i.1 = 0 then F64.cos x else F64.sin x

/-- Julia `spher(x) = Chain(cos(x[2])*sin(x[1]), sin(x[2])*sin(x[1]), cos(x[1]))`. -/
def spher (x : AffinePoint 2) : Chain ℝ3 1 Float :=
  let a := x.get! 0
  let b := x.get! 1
  Chain.ofFn fun i => if i.1 = 0 then F64.cos b * F64.sin a else if i.1 = 1 then F64.sin b * F64.sin a else F64.cos a

/-- Julia `sph = spher.(SphereParameter(60,60))`. -/
def sphere := (Parameter.sphere #v[60, 60]).map spher

/-! ## C16: Hopf fibration -/

/-- Julia `stereohopf(θ, φ, ψ)`: `a = cos θ·exp((im/2)(ψ-φ))`, `b = sin θ·exp((im/2)(ψ+φ))`,
`Chain(imag(a), real(b), imag(b))/(1-real(a))` (Grassmann's division by a real: `* (1/x)`). -/
def stereohopf (x : AffinePoint 3) : Chain ℝ3 1 Float :=
  let θ := x.get! 0
  let φ := x.get! 1
  let ψ := x.get! 2
  let half (d : Float) : JuliaBase.Complex Float := ComplexF64.exp ⟨0 * d, f64! 0.5 * d⟩
  let ea := half (ψ - φ)
  let eb := half (ψ + φ)
  let ca := F64.cos θ
  let sb := F64.sin θ
  let are := ca * ea.re
  let aim := ca * ea.im
  let r := 1 / (1 - are)
  Chain.ofFn fun i => if i.1 = 0 then aim * r else if i.1 = 1 then sb * eb.re * r else sb * eb.im * r

/-- Julia `hs = stereohopf.(HopfParameter())`. -/
def hopf := Parameter.hopfDefault.map stereohopf

/-- Julia `alteration!(hs, wireframe, wireframe!)`: the seven leaves `leaf(hs, i, 1)` as
wireframes on one axis. -/
def hopfCanvas : Canvas :=
  (List.range 7).foldl (fun c i => c.wireframe (hopf.leafAt i 0)) (Canvas.fresh 3)

/-! ## C17: a tangent-space streamplot on the torus -/

/-- Julia `torus(x) = Chain((2+0.5cos(x[1]))*cos(x[2]), (2+0.5cos(x[1]))*sin(x[2]), 0.5sin(x[1]))`. -/
def torusMap (x : AffinePoint 2) : Chain ℝ3 1 Float :=
  let a := x.get! 0
  let b := x.get! 1
  let r := 2 + f64! 0.5 * F64.cos a
  Chain.ofFn fun i => if i.1 = 0 then r * F64.cos b else if i.1 = 1 then r * F64.sin b else f64! 0.5 * F64.sin a

/-- Julia `tor = torus.(TorusParameter(60,60))`. -/
def tor := (Parameter.torus #v[60, 60]).map torusMap

/-- Julia `vf3 = f3.(TorusParameter(100,100))`, `f3(x) = Chain(cos(x[1])*cos(x[2]),sin(x[2])*sin(x[1]))`. -/
def vf3 := (Parameter.torus #v[100, 100]).map fun x =>
  (Chain.ofFn fun i => if i.1 = 0 then F64.cos (x.get! 0) * F64.cos (x.get! 1) else F64.sin (x.get! 1) * F64.sin (x.get! 0) : Chain ℝ2 1 Float)

/-! ## Entries -/

/-- The `fiber.md` figures. -/
def entries : List Entry :=
  [curveEntry "cartan-riemann-torus" "Riemann-sphere curve as a TensorField, coloured by speed (torus)"
     "`pts = TensorField(-2*pi:0.0001:2*pi); @basis S\"∞+++\"; f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)); lines(V(2,3,4).(f.(pts)))` (`fiber.md:477-487`)"
     fun t => pick3 (torus t) 1 2 3,
   curveEntry "cartan-riemann-orbit-2" "Riemann-sphere curve of a translating versor, coloured by speed"
     "`f(t) = ↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3)); lines(V(2,3,4).(f.(pts)))` (`fiber.md:477-487`)"
     fun t => pick3 (orbit2 t) 1 2 3,
   curveEntry "cartan-riemann-orbit-4" "Riemann-sphere curve of a rotating and translating versor, coloured by speed"
     "`f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3)); lines(V(2,3,4).(f.(pts)))` (`fiber.md:477-487`)"
     fun t => pick3 (orbit4 t) 1 2 3,
   curveEntry "cartan-riemann-helix" "The same curve in conformal space S\"∞∅+++\", coloured by speed"
     "`@basis S\"∞∅+++\"; f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3)); lines(V(3,4,5).(vector.(f.(pts))))` (`fiber.md:488-493`)"
     fun t => pick3 (helix t) 2 3 4] ++
  (List.range 6).map (fun k => bivectorEntry (k + 1)) ++
  [conformalEntry 1 0 1 2 "V(1,2,3)", conformalEntry 2 1 2 3 "V(2,3,4)",
   { name := "cartan-circle", group := "Cartan (fiber.md)", upstream := fiberDoc
     title := "The unit circle as a plane curve, coloured by speed"
     source := "`t = TensorField(0:0.001:2pi); circ = Chain.(cos(t),sin(t)); lines(circ)` (`fiber.md:602-613`)"
     build := fun j? => do
       let c := GrassmannPlot.lines circle
       let checks := match j? with
         | some j => speedCurveChecks (curvePoints circle) ((speedValues circle).getD .empty) j
         | none => #[]
       return { fig := c.figure, checks } },
   { name := "cartan-sphere-wireframe", group := "Cartan (fiber.md)", upstream := fiberDoc
     title := "Wireframe of the sphere over SphereParameter(60,60)"
     source := "`spher(x) = Chain(cos(x[2])*sin(x[1]), sin(x[2])*sin(x[1]), cos(x[1])); wireframe(spher.(SphereParameter(60,60)))` (`fiber.md:602-613`)"
     build := fun j? => do
       let c := GrassmannPlot.wireframe sphere
       let checks := match j?, (segmentsOf c)[0]? with
         | some j, some p => segmentChecks p j
         | some _, none => #[{ label := "segments", ok := false, detail := "no segments drawn" }]
         | none, _ => #[]
       return { fig := c.figure (600, 500), checks } },
   { name := "cartan-torus-tangent-stream", group := "Cartan (fiber.md)", upstream := fiberDoc
     title := "Streamlines of a parameter field drawn on the torus (tangent-space streamplot)"
     source := "`tor = torus.(TorusParameter(60,60)); vf3 = f3.(TorusParameter(100,100)); streamplot(tor,vf3)` (`fiber.md:778-797`)"
     build := fun j? => do
       let c := (Canvas.ax3 (Axis3.new (aspect := .data))).streamplot (tor, vf3)
       let (r, _) := tangentStream3 vf3 {}
       return { fig := c.figure (600, 500), checks := match j? with | some j => GrassmannFigs.streamChecks r j | none => #[] } },
   { name := "cartan-hopf", group := "Cartan (fiber.md)", upstream := fiberDoc
     title := "Hopf fibration: seven nested tori of the stereographic Hopf map"
     source := "`hs = stereohopf.(HopfParameter()); alteration!(hs,wireframe,wireframe!)` (`fiber.md:765-775`)"
     build := fun j? => do
       let c := hopfCanvas
       let pts := Field.fiberPoints hopf
       let segs := segmentsOf c
       let checks := match j? with
         | some j =>
           let nseg := (jarr (jget j "nseg")).map jnat
           #[eqCheck "wireframes" segs.size (jnat (jget j "nplots")),
             eqCheck "segment points per leaf" (segs.map (·.size)).toList nseg.toList] ++
           (Array.range 3).foldl (init := #[]) fun acc i =>
             acc ++ summaryChecks s!"x{i + 1}" ((coordArrays pts 3).getD i .empty) (jget j s!"x{i + 1}")
         | none => #[]
       return { fig := c.figure (600, 500), checks } }]

end Gallery.CartanFigs
