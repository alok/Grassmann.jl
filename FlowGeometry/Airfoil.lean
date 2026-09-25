import FlowGeometry.Base

/-!
# Sampled profiles, airfoil surfaces and outlines

The sampled forms of FlowGeometry.jl: `profile(p)`, `profileslope(p)`, `profileangle(p)`
(`profiles.jl:28-36`), the surfaces `upper`/`lower` of an airfoil (`airfoils.jl:37-54, 79-146`), the
closed outline `complex(N)` (`airfoils.jl:56-59`), the homogeneous points (`profiles.jl:44-46`,
`airfoils.jl:60-63`) and the Joukowski map (`airfoils.jl:171-183`).

**Fields.** Every sampled result is a `Cartan.TensorField` over a 1-D grid, as in Julia:
`profile(p)` over `interval(p)`, the surfaces over the camber profile's interval (Julia's field
arithmetic keeps the base of `profile(n.c)`, whatever `c`, `x0`), the outline over
`doubleinterval(interval(N))` with the 1-D torus gluing (Julia's `TorusTopology`, which the release
forgets to import, FG-B1), the Joukowski curve over `range(0, 2π, length = 2p-1)`. Surfaces and
outlines have `Complex Float` fibers (`x + iy`, stored `re, im`).

**Operation order.** Julia builds the American surfaces as
`upper(x + im*yc, im*cis.(atan.(dyc))*yt)` with `upper(z, r) = z + r`, `lower(z, r) = z - r` and the
last point forced to `1 + 0im`; with Julia's `Complex{Bool}` rules (`false*y = copysign(0, y)`) that
is, at every sample,

```
θ = atan(y_c')   (s, c) = sincos(θ)
z = (x + copysign(0, y_c),  y_c)
r = (y_t·(copysign(0, c) - s),  y_t·(copysign(0, s) + c))
upper = z + r,  lower = z - r
```

and the profile form (`SymmetricArc`, `DoubleArc`, arcs) is `x ± y·(c·im)`. The port evaluates
exactly these expressions, so the surfaces match Julia bit for bit.

**Julia defects** (`oracle/flowgeometry/defects.toml`): `British` throws upstream (FG-B2), the port
lays the thickness off perpendicular to the chord (`dyc = 0`); `SymmetricArc`, `DoubleArc` and
`British` have no `interval`, so their outlines throw (FG-B6), the port uses the (upper) profile's
interval (and, for a `DoubleArc` of two sample counts, an explicit base).
-/

namespace FlowGeometry

open JuliaBase Cartan

/-! ## Surface kernels on flat arrays -/

/-- `false * y` in Julia: `copysign(0, y)` (Bool is a strong zero, `base/bool.jl:182`). -/
@[inline] def zeroOf (y : Float) : Float := F64.copysign 0 y

/-- The American (thickness ⟂ camber) surfaces `(upper, lower)`, interleaved `re, im`, at `n`
samples: `upper = z + r`, `lower = z - r` with the camber `c·yc`, its slope `dyc` and the thickness
`c·yt`; the last sample of each is `1 + 0im`. `slope` is `false` for the British construction
(`dyc ≡ 0`, so `θ = 0`). -/
def americanSurfaces (slope : Bool) (xs yc dyc yt : FloatArray) (c : Float) (n : Nat) :
    FloatArray × FloatArray :=
  go n 0 (FloatArray.emptyWithCapacity (2 * n)) (FloatArray.emptyWithCapacity (2 * n))
where
  /-- the fill loop -/
  go : Nat → Nat → FloatArray → FloatArray → FloatArray × FloatArray
    | 0, _, u, l => (u, l)
    | k + 1, i, u, l =>
      if k == 0 then ((u.push 1).push 0, (l.push 1).push 0)
      else
        let x := xs.get! i
        let cy := c * yc.get! i
        let t := c * yt.get! i
        let θ := if slope then F64.atan (dyc.get! i) else 0
        F64.sincosK θ fun s co =>
          let rre := t * (zeroOf co - s)
          let rim := t * (zeroOf s + co)
          let zre := x + zeroOf cy
          go k (i + 1) ((u.push (zre + rre)).push (cy + rim)) ((l.push (zre - rre)).push (cy - rim))

/-- The profile-form surfaces `x ± y·(c·im)` (`airfoils.jl:37`, `upper(interval(z,c,x0),
profile(z)*(c*im))`), `(upper, lower)`, interleaved, last sample `1 + 0im`. -/
def profileSurfaces (xs ys : FloatArray) (c : Float) (n : Nat) : FloatArray × FloatArray :=
  go (zeroOf c) n 0 (FloatArray.emptyWithCapacity (2 * n)) (FloatArray.emptyWithCapacity (2 * n))
where
  /-- the fill loop -/
  go (c0 : Float) : Nat → Nat → FloatArray → FloatArray → FloatArray × FloatArray
    | 0, _, u, l => (u, l)
    | k + 1, i, u, l =>
      if k == 0 then ((u.push 1).push 0, (l.push 1).push 0)
      else
        let y := ys.get! i
        let wre := y * c0
        let wim := y * c
        let x := xs.get! i
        go c0 k (i + 1) ((u.push (x + wre)).push wim) ((l.push (x - wre)).push (-wim))

/-- The elements of an axis. -/
@[inline] def axisData (a : Axis) : FloatArray := axisValues a

/-- The evaluation data and sample count of an analytic profile (`none` for `UpperArc`/`LowerArc`,
whose samples come from an airfoil). -/
def Profile.analytic? : Profile → Option (Eval × Nat)
  | .upperArc _ | .lowerArc _ => none
  | p => some (p.eval, p.samples)

/-- `x0 = 0` and `c = 1` bit for bit (the chord positions are then the profile's own samples). -/
@[inline] def isUnitChord (c x0 : Float) : Bool := c == 1 && x0.toBits == 0

/-- The American/British surfaces of an analytic camber and thickness: the samples are computed
once on the camber's interval and shared by both surfaces. -/
def analyticSurfaces (slope : Bool) (ec et : Eval) (n : Nat) (c x0 : Float) : FloatArray × FloatArray :=
  let base := axisData (FlowGeometry.interval n)
  let xs := if isUnitChord c x0 then base else axisData (FlowGeometry.interval n c x0)
  americanSurfaces slope xs (ec.valuesOn base) (if slope then ec.slopesOn base else .empty) (et.valuesOn base) c n

mutual

/-- Julia `interval(p, c, x0)`: the chord positions of the samples, `range(x0, c, length = P)`;
for `UpperArc`/`LowerArc` the real parts of the wrapped surface (`airfoils.jl:38`, a field in
Julia, an explicit axis here). -/
def Profile.interval : Profile → Float → Float → Axis
  | .upperArc a, c, x0 => .explicit (reParts (a.surfaces c x0).1)
  | .lowerArc a, c, x0 => .explicit (reParts (a.surfaces c x0).2)
  | .flatPlate p, c, x0 | .parabolicArc _ p, c, x0 | .circularArc _ p, c, x0 | .clarkY _ _ p, c, x0
  | .thickness _ _ _ p, c, x0 | .modified _ _ _ p, c, x0 | .naca4 _ p, c, x0 | .naca5 _ p, c, x0
  | .naca6 _ _ p, c, x0 | .naca6A _ p, c, x0 => FlowGeometry.interval p c x0

/-- The base of `profile(p)`: `interval(p)` (`c = 1`, `x0 = 0`), and for an arc the base of the
wrapped surface. -/
def Profile.baseAxis : Profile → Axis
  | .upperArc a => a.upperAxis
  | .lowerArc a => a.lowerAxis
  | .flatPlate p | .parabolicArc _ p | .circularArc _ p | .clarkY _ _ p | .thickness _ _ _ p
  | .modified _ _ _ p | .naca4 _ p | .naca5 _ p | .naca6 _ _ p | .naca6A _ p => FlowGeometry.interval p

/-- The fibers of `profile(p)` (`profiles.jl:28-31`; `FlatPlate`: `range(0, 0, length = p)`;
arcs: `imag.(upper(a))`, `airfoils.jl:39`). -/
def Profile.fieldData : Profile → FloatArray
  | .upperArc a => imParts (a.surfaces 1 0).1
  | .lowerArc a => imParts (a.surfaces 1 0).2
  | .flatPlate p => floatsOfFn p fun _ => 0
  | p@(.parabolicArc _ n) | p@(.circularArc _ n) | p@(.clarkY _ _ n) | p@(.thickness _ _ _ n)
  | p@(.modified _ _ _ n) | p@(.naca4 _ n) | p@(.naca5 _ n) | p@(.naca6 _ _ n) | p@(.naca6A _ n) =>
    p.eval.valuesOn (axisData (FlowGeometry.interval n))

/-- The fibers of `profileslope(p)` (`profiles.jl:32-35`; arcs: Cartan's `gradient` of the
sampled surface, `airfoils.jl:40`). -/
def Profile.slopeData : Profile → FloatArray
  | .upperArc a => gradient1 (axisData a.upperAxis) (imParts (a.surfaces 1 0).1)
  | .lowerArc a => gradient1 (axisData a.lowerAxis) (imParts (a.surfaces 1 0).2)
  | .flatPlate p => floatsOfFn p fun _ => 0
  | p@(.parabolicArc _ n) | p@(.circularArc _ n) | p@(.clarkY _ _ n) | p@(.thickness _ _ _ n)
  | p@(.modified _ _ _ n) | p@(.naca4 _ n) | p@(.naca5 _ n) | p@(.naca6 _ _ n) | p@(.naca6A _ n) =>
    p.eval.slopesOn (axisData (FlowGeometry.interval n))

/-- The base of `upper(a)`. -/
def Airfoil.upperAxis : Airfoil → Axis
  | .american c _ | .british c _ => c.baseAxis
  | .symmetric s => s.baseAxis
  | .double u _ => u.baseAxis

/-- The base of `lower(a)`. -/
def Airfoil.lowerAxis : Airfoil → Axis
  | .american c _ | .british c _ => c.baseAxis
  | .symmetric s => s.baseAxis
  | .double _ l => l.baseAxis

/-- Julia `upperlower(a, c, x0)`: both surfaces, interleaved `re, im` (`airfoils.jl:53, 79-81, 98-99,
119-121, 142-145`). -/
def Airfoil.surfaces : Airfoil → Float → Float → FloatArray × FloatArray
  | .american cp tp, c, x0 =>
    match cp.analytic?, tp.analytic? with
    | some (ec, n), some (et, _) => analyticSurfaces true ec et n c x0
    | _, _ =>
      americanSurfaces true (axisData (cp.interval c x0)) cp.fieldData cp.slopeData tp.fieldData c cp.samples
  | .british cp tp, c, x0 =>
    match cp.analytic?, tp.analytic? with
    | some (ec, n), some (et, _) => analyticSurfaces false ec et n c x0
    | _, _ =>
      americanSurfaces false (axisData (cp.interval c x0)) cp.fieldData .empty tp.fieldData c cp.samples
  | .symmetric s, c, x0 => profileSurfaces (axisData (s.interval c x0)) s.fieldData c s.samples
  | .double u l, c, x0 =>
    ((profileSurfaces (axisData (u.interval c x0)) u.fieldData c u.samples).1,
     (profileSurfaces (axisData (l.interval c x0)) l.fieldData c l.samples).2)

end

/-- Julia `upper(a, c, x0)`, interleaved `re, im`. -/
def Airfoil.upperData (a : Airfoil) (c x0 : Float) : FloatArray := (a.surfaces c x0).1

/-- Julia `lower(a, c, x0)`, interleaved `re, im`. -/
def Airfoil.lowerData (a : Airfoil) (c x0 : Float) : FloatArray := (a.surfaces c x0).2

/-! ## Profiles as fields -/

namespace Profile

/-- Profiles whose fields are their `Eval` on the base points (all but `FlatPlate`, whose field
is a zero range, and the arcs). -/
def sampledDirectly : Profile → Bool
  | .flatPlate _ | .upperArc _ | .lowerArc _ => false
  | _ => true

/-- The 1-D grid of `profile(p)` (Julia `base(profile(p))`). -/
abbrev base (p : Profile) : GridBundle 1 Float := GridBundle.ofAxis p.baseAxis

/-- Julia `profile(p)` (`profiles.jl:28-31`): the profile sampled over `interval(p)`. -/
def field (p : Profile) : TensorField p.base Float :=
  let b := p.base
  if p.sampledDirectly then fieldOf b (p.eval.valuesOn b.space.coords[0]) else fieldOf b p.fieldData

/-- Julia `profileslope(p)` (`profiles.jl:32-35`). -/
def slopeField (p : Profile) : TensorField p.base Float :=
  let b := p.base
  if p.sampledDirectly then fieldOf b (p.eval.slopesOn b.space.coords[0]) else fieldOf b p.slopeData

/-- Julia `profileangle(p) = atan.(profileslope(p))` (`profiles.jl:36`). -/
def angleField (p : Profile) : TensorField p.base Float := p.slopeField.map F64.atan

/-- Julia `points(N::Profile, c, x0)` (`profiles.jl:44-46`): the homogeneous points
`(1, x, y)` with `x` from `interval(N, c, x0)` and `y` the *unscaled* profile. -/
def points (p : Profile) (c : Float := 1) (x0 : Float := 0) : PointCloud (Grassmann.Chain DirectSum.ℝ3 1 Float) :=
  let xs := axisData (p.interval c x0)
  let ys := p.fieldData
  ⟨floatsOfFn (3 * ys.size) fun k =>
    let i := k / 3
    match k % 3 with
    | 0 => 1
    | 1 => xs.get! i
    | _ => ys.get! i, .induced, 0⟩

/-- Julia `initpoints(N::Profile) = initpoints(interval(N))` (FlowGeometry.jl:38, Cartan
`element.jl:69-70`): the 1-D homogeneous points `(1, x)`. -/
def initpoints (p : Profile) : PointCloud (Grassmann.Chain DirectSum.ℝ2 1 Float) :=
  let xs := axisData (p.interval 1 0)
  ⟨floatsOfFn (2 * xs.size) fun k => if k % 2 == 0 then 1 else xs.get! (k / 2), .induced, 0⟩

/-- Julia `initedges(N::Profile)` (FlowGeometry.jl:39, which throws, FG-B7) as intended: Cartan's
`initedges(interval(N))` (`element.jl:61-62`), the chain of edges `(i, i+1)` over the 1-D points. -/
def initedges (p : Profile) : SimplexBundle 2 (Grassmann.Chain DirectSum.ℝ2 1 Float) :=
  let pts := p.initpoints
  let n := pts.size
  ⟨pts, MeshTopology.SimplexTopology.ofElements ((Array.range (n - 1)).map fun i => #v[i + 1, i + 2])
    (p := some n) (i := some (.oneTo n))⟩

/-- Julia `chord(p)` of a profile (`airfoils.jl:45`). -/
def chord (p : Profile) : Axis := FlowGeometry.chord p.samples

end Profile

/-! ## Airfoils -/

namespace Airfoil

/-- The grid of `upper(a)`. -/
abbrev upperBase (a : Airfoil) : GridBundle 1 Float := GridBundle.ofAxis a.upperAxis
/-- The grid of `lower(a)`. -/
abbrev lowerBase (a : Airfoil) : GridBundle 1 Float := GridBundle.ofAxis a.lowerAxis

/-- Julia `upper(a, c = 1, x0 = 0)`: the upper surface `x + iy`, LE to TE, the last point forced
to `1 + 0im` (`airfoils.jl:47`). -/
def upper (a : Airfoil) (c : Float := 1) (x0 : Float := 0) : TensorField a.upperBase (Complex Float) :=
  fieldOf a.upperBase (a.upperData c x0)

/-- Julia `lower(a, c = 1, x0 = 0)`: the lower surface (`airfoils.jl:48`). -/
def lower (a : Airfoil) (c : Float := 1) (x0 : Float := 0) : TensorField a.lowerBase (Complex Float) :=
  fieldOf a.lowerBase (a.lowerData c x0)

/-- Julia `upperlower(a, c, x0) = (upper(a, c, x0), lower(a, c, x0))` (`airfoils.jl:53`). -/
def upperlower (a : Airfoil) (c : Float := 1) (x0 : Float := 0) :
    TensorField a.upperBase (Complex Float) × TensorField a.lowerBase (Complex Float) :=
  (a.upper c x0, a.lower c x0)

/-- Julia `interval(n, c, x0)` of an airfoil: the camber (or upper) profile's
(`airfoils.jl:146`; `SymmetricArc`, `DoubleArc`, `British` have none upstream, FG-B6). -/
def interval (a : Airfoil) (c : Float := 1) (x0 : Float := 0) : Axis :=
  match a with
  | .american cp _ | .british cp _ => cp.interval c x0
  | .symmetric s => s.interval c x0
  | .double u _ => u.interval c x0

/-- The base axis of the closed outline: `doubleinterval(interval(N))`; a `DoubleArc` of two
sample counts gets the upper interval followed by the reflected lower one. -/
def outlineAxis (a : Airfoil) : Axis :=
  match a with
  | .double u l =>
    if u.samples == l.samples then doubleinterval (a.interval 1 0)
    else
      let xu := axisData (u.interval 1 0)
      let xl := axisData (l.interval 1 0)
      let nu := xu.size
      let e := xu.get! (nu - 1)
      .explicit (floatsOfFn (nu + xl.size - 1) fun i =>
        if i < nu then xu.get! i else 2 * e - xl.get! (xl.size - 1 - (i - nu + 1)))
  | _ => doubleinterval (a.interval 1 0)

/-- The grid of `complex(N)`: the outline axis with the 1-D torus gluing (Julia
`TorusTopology(TensorField(doubleinterval(interval(N)), …))`, `airfoils.jl:58`). -/
abbrev outlineBase (a : Airfoil) : GridBundle 1 Float := (GridBundle.ofAxis a.outlineAxis).torus

/-- The closed outline of the surfaces `(U, L)`, interleaved: `U` LE → TE, then `L` TE → LE
without its duplicated trailing edge (`[U; reverse(L)[2:end]]`). -/
def outlineOf (ul : FloatArray × FloatArray) : FloatArray :=
  let (u, l) := ul
  let nl := l.size / 2
  let out := copyInto u 0 u.size (FloatArray.emptyWithCapacity (u.size + l.size - 2))
  goL l out (nl - 1)
where
  /-- append `src[i, i+k)` -/
  copyInto (src : FloatArray) (i : Nat) : Nat → FloatArray → FloatArray
    | 0, acc => acc
    | k + 1, acc => copyInto src (i + 1) k (acc.push (src.get! i))
  /-- append the lower points `j-1, …, 0` -/
  goL (l : FloatArray) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | j + 1 => goL l ((acc.push (l.get! (2 * j))).push (l.get! (2 * j + 1))) j

/-- The closed outline, interleaved (Julia `fiber(complex(N))`). -/
def outlineData (a : Airfoil) : FloatArray := outlineOf (a.surfaces 1 0)

/-- Julia `complex(N::Airfoil)` (`airfoils.jl:56-59`): the closed outline `2P-1` samples from the
leading edge around and back (first and last sample both `0 + 0im`). -/
def complex (a : Airfoil) : TensorField a.outlineBase (Complex Float) := fieldOf a.outlineBase a.outlineData

/-- The first `n` samples of an interleaved complex vector as homogeneous points `(1, x, y)`. -/
def homogeneous (z : FloatArray) (n : Nat) : FloatArray :=
  go 0 (FloatArray.emptyWithCapacity (3 * n)) n
where
  /-- the loop -/
  go (i : Nat) (acc : FloatArray) : Nat → FloatArray
    | 0 => acc
    | k + 1 => go (i + 1) (((acc.push 1).push (z.get! (2 * i))).push (z.get! (2 * i + 1))) k

/-- Julia `points(N::Airfoil)` (`airfoils.jl:60-63`): the `2P-2` distinct outline points as
homogeneous `(1, x, y)`. -/
def points (a : Airfoil) : PointCloud (Grassmann.Chain DirectSum.ℝ3 1 Float) :=
  let z := a.outlineData
  ⟨homogeneous z (z.size / 2 - 1), .induced, 0⟩

/-- Julia `camber(n)` of an American or British airfoil (`airfoils.jl:117, 140`); the upper
profile otherwise. -/
def camber : Airfoil → Profile
  | .american c _ | .british c _ => c
  | .symmetric _ => .flatPlate 0
  | .double u _ => u

/-- Julia `thickness(n)` (`airfoils.jl:118, 141`); the profile itself for `SymmetricArc`. -/
def thicknessProfile : Airfoil → Profile
  | .american _ t | .british _ t => t
  | .symmetric s => s
  | .double _ l => l

end Airfoil

namespace Profile

/-- Julia `upper(z::Profile, c = 1, x0 = 0) = upper(interval(z,c,x0), profile(z)*(c*im))`
(`airfoils.jl:37`): `x + i·c·y`, last point `1 + 0im`. -/
def upper (p : Profile) (c : Float := 1) (x0 : Float := 0) : TensorField p.base (Complex Float) :=
  fieldOf p.base (profileSurfaces (axisData (p.interval c x0)) p.fieldData c p.samples).1

/-- Julia `lower(z::Profile, c = 1, x0 = 0)`: `x - i·c·y`, last point `1 + 0im`. -/
def lower (p : Profile) (c : Float := 1) (x0 : Float := 0) : TensorField p.base (Complex Float) :=
  fieldOf p.base (profileSurfaces (axisData (p.interval c x0)) p.fieldData c p.samples).2

end Profile

/-! ## Joukowski -/

namespace Joukowski

/-- Julia `joukowski(R, f, g, b, p)` (`airfoils.jl:175`). -/
def mk' (R f g b : Num) (p : Nat) : Joukowski := ⟨R, f, g, b, p⟩

/-- Julia `range(0, 2π, length = n)`: `2π` has no small rational form (`rat` fails), so Julia's
`range` falls back to `_linspace(0.0, 2π, n)` (`twiceprecision.jl:668-712`); built directly (the
general `Axis.range` spends about 2 µs in `rat`; `Tests/FlowGeometry/Meshes.lean` checks the two
agree for `n = 1 … 3000`). -/
def angles (n : Nat) : Axis :=
  if n ≥ 2 then .stepLen (JuliaBase.linspaceFloat 0 twoPiF n) else Axis.range 0 twoPiF n

/-- Julia `interval(::Joukowski) = interval(2p-1, 2π)` (`airfoils.jl:177`): the angles
`range(0, 2π, length = 2p-1)`. -/
def interval (j : Joukowski) : Axis := angles (2 * j.p - 1)

/-- The (open) grid of `complex(j)`. -/
abbrev base (j : Joukowski) : GridBundle 1 Float := GridBundle.ofAxis j.interval

/-- The Joukowski map at the angles `θv`. -/
def complexOn (j : Joukowski) (θv : FloatArray) : FloatArray :=
  let R := j.R.toFloat
  -- `g*im` is `Complex(g*false, g*true)`: `0` for an `Int` `g`, `copysign(0, g)` for a float
  let gre : Float := match j.g with | .int _ => 0 | .float g => zeroOf g
  let F := j.f.toFloat - gre
  let G : Float := match j.g with | .int n => Float.ofInt (-n) | .float g => -g
  let b2 := match j.b with | .int n => Float.ofInt (n * n) | .float b => b * b
  go θv R F G b2 θv.size 0 (FloatArray.emptyWithCapacity (2 * θv.size))
where
  /-- the loop over the angles -/
  go (θs : FloatArray) (R F G b2 : Float) : Nat → Nat → FloatArray → FloatArray
    | 0, _, acc => acc
    | k + 1, i, acc =>
      F64.sincosK (θs.get! i) fun s c =>
        let z : Complex Float := ⟨R * c - F, R * s - G⟩
        let w := ComplexF64.inv z
        go θs R F G b2 k (i + 1) ((acc.push (z.re + b2 * w.re)).push (z.im + b2 * w.im))

/-- Julia `complex(::Joukowski)` (`airfoils.jl:179-183`): `w = z + b²/z` for
`z = R·cis(θ) - (f - g·im)`, with Julia's mixed `Int`/`Float64` complex arithmetic and its
`inv(::ComplexF64)`. -/
def complexData (j : Joukowski) : FloatArray := complexOn j (axisValues j.interval)

/-- Julia `complex(::Joukowski)` as a field over the angles. -/
def complex (j : Joukowski) : TensorField j.base (Complex Float) :=
  let b := j.base
  fieldOf b (j.complexOn b.space.coords[0])

/-- Julia `points(j)` (`airfoils.jl:60-63`): the first `2p-2` samples as homogeneous points. -/
def points (j : Joukowski) : PointCloud (Grassmann.Chain DirectSum.ℝ3 1 Float) :=
  let z := j.complexData
  ⟨Airfoil.homogeneous z (z.size / 2 - 1), .induced, 0⟩

end Joukowski

end FlowGeometry
