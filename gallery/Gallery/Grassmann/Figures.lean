import Gallery.Common
import Gallery.Grassmann.Fields

/-!
# Grassmann.jl README figures (`README.md:63-67, 271-316`; `docs/src/algebra.md:1265-1316`)

* `grassmann-plane-1 … -6`: `streamplot(vectorfield(t), -1.5..1.5, -1.5..1.5)` of the six
  plane versors, traced by LeanPlot's port of Makie's `streamplot_impl` with the fields of
  `Gallery.Fields.planeFieldOf`;
* `grassmann-torus`, `-helix`, `-orbit-2`, `-orbit-4`: `lines(V(…).(points(f)))`, the
  125 664 samples of `-2π:0.0001:2π`, as one polyline in an `Axis3`;
* `grassmann-orb`, `-wave`: the 3D conformal streamplots with `gridsize = (10,10,10)`.

Checks: the streamplot output (arrow and point counts, a hash of every Float32 line point,
arrows, a sample of the lines) against Makie's own `streamplot_impl` run on Julia's field;
the curves (a sample every 64 points and the coordinate sums over all points) against
Julia's `points`.
-/

namespace Gallery.GrassmannFigs

open LeanPlot Gallery.Fields
open LeanPlot.Recipes.Algo (Stream.Options Stream.Result Stream.streamplot2 Stream.streamplot3)

/-! ## Streamplot data checks -/

/-- The coordinates of a point set, point-major, first `dim` coordinates. -/
def flat (p : Pts3) (dim : Nat) (stride : Nat := 1) : FloatArray :=
  go 0 (FloatArray.emptyWithCapacity (dim * p.size))
where
  /-- the stride loop -/
  go (i : Nat) (acc : FloatArray) : FloatArray :=
    if i < p.size then
      let v := p.get! i
      let acc := acc.push v.x |>.push v.y
      go (i + max stride 1) (if dim == 3 then acc.push v.z else acc)
    else acc
  termination_by p.size - i
  decreasing_by have := Nat.le_max_right stride 1; omega

/-- FNV-1a over the `Float32` bit patterns of `vals` (NaN as `0x7fc00000`), Julia's
`fnv1a32` of `oracle/gallery/grassmann_common.jl`. -/
def fnv1a32 (vals : FloatArray) : UInt64 :=
  vals.foldl (init := 0xcbf29ce484222325) fun h x =>
    let b : UInt32 := if x.isNaN then 0x7fc00000 else x.toFloat32.toBits
    let h := (h ^^^ (b &&& 0xff).toUInt64) * 0x100000001b3
    let h := (h ^^^ ((b >>> 8) &&& 0xff).toUInt64) * 0x100000001b3
    let h := (h ^^^ ((b >>> 16) &&& 0xff).toUInt64) * 0x100000001b3
    (h ^^^ ((b >>> 24) &&& 0xff).toUInt64) * 0x100000001b3

/-- `x` rounded to binary32 and back. -/
@[inline] def r32 (x : Float) : Float := x.toFloat32.toFloat

/-- Largest difference after rounding both sides to binary32 (the Julia dump prints binary32
values in shortest form). -/
def maxDiff32 (lean julia : FloatArray) : Float :=
  let m (a : FloatArray) : FloatArray := a.foldl (fun acc x => acc.push (r32 x)) (FloatArray.emptyWithCapacity a.size)
  maxAbsDiff (m lean) (m julia)

/-- The checks of a streamplot result against Makie's `streamplot_impl` dump. -/
def streamChecks (r : Stream.Result) (j : Lean.Json) : Array Check :=
  let dim := r.dim
  let nan := r.linePoints.xs.foldl (fun k x => if x.isNaN then k + 1 else k) 0
  let lines := flat r.linePoints dim
  let stride := jnat (jget j "stride")
  let fnv := hex16 (fnv1a32 lines)
  let jfnv := jstr (jget j "line_fnv")
  let ap := flat r.arrowPos dim
  let ad := flat r.arrowDir dim
  let sample := flat r.linePoints dim stride
  let jsample := jfloats (jget j "line_points")
  #[eqCheck "arrows" r.arrowPos.size (jnat (jget j "n_arrows")),
    eqCheck "line points" r.linePoints.size (jnat (jget j "n_points")),
    eqCheck "NaN separators" nan (jnat (jget j "n_nan")),
    { label := "all line points (Float32 hash)", ok := fnv == jfnv
      detail := if fnv == jfnv then s!"bit-identical ({fnv})"
                else s!"hash differs; max |Δ| on every {stride}th point = {sci (maxDiff32 sample jsample)}" },
    { label := "arrow positions", ok := ap.size == (jfloats (jget j "arrow_pos")).size && maxDiff32 ap (jfloats (jget j "arrow_pos")) ≤ 1e-6
      detail := s!"max |Δ| = {sci (maxDiff32 ap (jfloats (jget j "arrow_pos")))}" },
    { label := "arrow directions", ok := ad.size == (jfloats (jget j "arrow_dir")).size && maxDiff32 ad (jfloats (jget j "arrow_dir")) ≤ 1e-6
      detail := s!"max |Δ| = {sci (maxDiff32 ad (jfloats (jget j "arrow_dir")))}" }]

/-! ## Plane figures -/

/-- The streamplot of `plane-k` (Makie defaults: `gridsize = (32, 32)`, `stepsize = 0.01`,
`maxsteps = 500`, `density = 1`, a `Float64` box `-1.5..1.5`²). -/
def planeStream (k : Nat) : Stream.Result :=
  let f := planeFieldOf k
  Stream.streamplot2 (fun p => let (u, v) := f p.x p.y; ⟨u, v⟩) (-1.5) (-1.5) 3 3 { gridsize := #[32, 32] }

/-- A plane figure: the coloured streamlines and arrowheads in an `Axis2`. -/
def planeFigure (r : Stream.Result) : Figure :=
  let ax := Axis2.new |>.streamplot r.linePoints2 r.lineColors r.arrowPos2 r.arrowDir2 r.arrowColors
  Figure.new (600, 450) |>.axis 1 1 ax

/-- The Julia versor of each plane figure, for the captions. -/
def planeVersorText : Nat → String
  | 1 => "exp(π*v12/2)" | 2 => "exp((π/2)*v12/2)" | 3 => "exp((π/4)*v12/2)"
  | 4 => "v1*exp((π/4)*v12/2)" | 5 => "exp((π/8)*v12/2)" | _ => "v1*exp((π/4)*v12/2)"

/-- The URL of a Grassmann.jl paper image (`paper/img/<stem>.png`). -/
def paperImg (stem : String) : String :=
  s!"https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/{stem}.png"

/-- The plane entries. -/
def planeEntry (k : Nat) : Entry :=
  { name := s!"grassmann-plane-{k}", group := "Grassmann", upstream := paperImg s!"plane-{k}"
    title := s!"Versor field of {planeVersorText k} on the {if k ≤ 4 then "Euclidean" else "hyperbolic"} plane"
    source := s!"`{if k ≤ 4 then "basis\"2\"" else "@basis S\"+-\""}; streamplot(vectorfield({planeVersorText k}),-1.5..1.5,-1.5..1.5)` (Grassmann.jl `README.md:271-285`)"
    build := fun j? => do
      let r := planeStream k
      return { fig := planeFigure r, checks := match j? with | some j => streamChecks r j | none => #[] } }

/-! ## Curves -/

/-- The checks of a sampled curve against Julia's `points`. -/
def curveChecks (xs ys zs : FloatArray) (j : Lean.Json) : Array Check :=
  let stride := jnat (jget j "stride")
  let sums := jfloats (jget j "sum")
  let sumabs := jfloats (jget j "sumabs")
  let rel (a : Float) (k : Nat) : Float := (a - sums[k]!).abs / (if sumabs[k]! > 1 then sumabs[k]! else 1)
  let d := max (rel (sumFinite xs) 0) (max (rel (sumFinite ys) 1) (rel (sumFinite zs) 2))
  #[eqCheck "points" xs.size (jnat (jget j "n")),
    closeCheck s!"x (every {stride}th point)" (every xs stride) (jfloats (jget j "x")) 1e-9,
    closeCheck s!"y (every {stride}th point)" (every ys stride) (jfloats (jget j "y")) 1e-9,
    closeCheck s!"z (every {stride}th point)" (every zs stride) (jfloats (jget j "z")) 1e-9,
    { label := "Σx, Σy, Σz over all points", ok := d ≤ 1e-9, detail := s!"max |Δ| / Σ|·| = {sci d}" }]

/-- A curve figure: the polyline in an `Axis3` (Makie's default 3D axis). -/
def curveFigure (xs ys zs : FloatArray) : Figure :=
  Figure.new (600, 500) |>.axis3 1 1 (Axis3.new |>.lines xs ys zs)

/-- A curve entry from its sampled coordinates. -/
def curveEntry (name title source : String) (sample : Unit → FloatArray × FloatArray × FloatArray) : Entry :=
  { name, title, source, group := "Grassmann", upstream := paperImg (name.drop 10).toString
    build := fun j? => do
      let (xs, ys, zs) := sample ()
      return { fig := curveFigure xs ys zs, checks := match j? with | some j => curveChecks xs ys zs j | none => #[] } }

/-! ## 3D streamplots -/

/-- A 3D conformal streamplot over `-1.5..1.5`³ with `gridsize = (10, 10, 10)`: the field of
`vectorfield(exp((π/4)*(v12+v∞3)), V(2,3,4), W)` with the input read in chain indices `w`. -/
def sphereStream (w₁ w₂ w₃ : Nat) : Stream.Result :=
  let t := orbVersor
  Stream.streamplot3 (fun p => let (u, v, s) := sphereField t w₁ w₂ w₃ p.x p.y p.z; ⟨u, v, s⟩)
    ⟨-1.5, -1.5, -1.5⟩ ⟨3, 3, 3⟩ { gridsize := #[10, 10, 10] }

/-- A 3D streamplot figure in an `Axis3`. -/
def streamFigure3 (r : Stream.Result) : Figure :=
  let ax := Axis3.new |>.streamplot r.linePoints r.lineColors r.arrowPos r.arrowDir r.arrowColors
  Figure.new (600, 500) |>.axis3 1 1 ax

/-- A 3D stream entry. -/
def streamEntry3 (name title source : String) (w₁ w₂ w₃ : Nat) : Entry :=
  { name, title, source, group := "Grassmann", upstream := paperImg (name.drop 10).toString
    build := fun j? => do
      let r := sphereStream w₁ w₂ w₃
      return { fig := streamFigure3 r, checks := match j? with | some j => streamChecks r j | none => #[] } }

/-! ## Entries -/

/-- The Grassmann README figures. -/
def entries : List Entry :=
  [grassmannWave, grassmannOrb] ++ (List.range 6).map (fun k => planeEntry (k + 1)) ++ [
  curveEntry "grassmann-torus" "Curve on the Riemann sphere S\"∞+++\" (torus)"
    "`@basis S\"∞+++\"; f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))); lines(V(2,3,4).(points(f)))` (`README.md:287-292`)"
    fun _ => Gallery.Versor.points3 torus 1 2 3 pointsRange,
  curveEntry "grassmann-helix" "The same curve in conformal space S\"∞∅+++\" (helix)"
    "`@basis S\"∞∅+++\"; f(t) = (↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))); lines(V(3,4,5).(points(f)))` (`README.md:293-296`)"
    fun _ => Gallery.Versor.points3 helix 2 3 4 pointsRange,
  curveEntry "grassmann-orbit-2" "Orbit of a translating conformal versor (orbit-2)"
    "`f(t) = ↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3)); lines(V(2,3,4).(points(f)))` (`README.md:304-310`)"
    fun _ => Gallery.Versor.points3 orbit2 1 2 3 pointsRange,
  curveEntry "grassmann-orbit-4" "Orbit of a rotating and translating conformal versor (orbit-4)"
    "`f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3)); lines(V(2,3,4).(points(f)))` (`README.md:311-316`)"
    fun _ => Gallery.Versor.points3 orbit4 1 2 3 pointsRange]
where
  /-- The README header figure. -/
  grassmannWave : Entry := streamEntry3 "grassmann-wave" "Conformal versor field read in (v∞, v1, v2) (wave, the README header)"
    "`@basis S\"∞+++\"; streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4),V(1,2,3)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))` (`README.md:63-67, 298-302`)"
    0 1 2
  /-- The orb figure. -/
  grassmannOrb : Entry := streamEntry3 "grassmann-orb" "Conformal versor field on the Riemann sphere (orb)"
    "`@basis S\"∞+++\"; streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,-1.5..1.5,-1.5..1.5,gridsize=(10,10))` (`README.md:298-302`)"
    1 2 3

end Gallery.GrassmannFigs
