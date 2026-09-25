import Gallery.Versor
import Gallery.Grassmann.Spaces
import JuliaBase

/-!
# The curves and vector fields of the Grassmann README (`README.md:271-316`)

Every function transcribes one README expression, in Julia's evaluation order:

| figure | Julia (`README.md`, `docs/src/algebra.md:1265-1316`) |
|---|---|
| `plane-1 … plane-4` | `streamplot(vectorfield(t), -1.5..1.5, -1.5..1.5)`, `basis"2"`, `t = exp(π*v12/2)`, `exp((π/2)*v12/2)`, `exp((π/4)*v12/2)`, `v1*exp((π/4)*v12/2)` |
| `plane-5`, `plane-6` | the same over `S"+-"` with `exp((π/8)*v12/2)`, `v1*exp((π/4)*v12/2)` |
| `torus` | `f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))`, `lines(V(2,3,4).(points(f)))` in `S"∞+++"` |
| `helix` | the same `f` in `S"∞∅+++"`, `lines(V(3,4,5).(points(f)))` |
| `orbit-2` | `f(t) = ↓(exp(t*v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2)>>>↑(v1+v2-v3))` |
| `orbit-4` | `f(t) = ↓(exp(t*(v12+0.07v∞*(sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3)/2))>>>↑(v1+v2-v3))` |
| `orb` | `streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4)),-1.5..1.5,…,gridsize=(10,10))` |
| `wave` | `streamplot(vectorfield(exp((π/4)*(v12+v∞3)),V(2,3,4),V(1,2,3)),…)` |

`vectorfield(t, V, W) = p -> V(vector(↓(↑((V∪Manifold(t))(Chain{W,1}(p))) ⊘ t)))`
(`ext/GeometryBasicsExt.jl:30`): the point, read in the generators `W`, is lifted, sandwiched
(`x ⊘ t = (~t)⟑x⟑involute(t)`), projected down and read in the generators `V`. All of it is
the library's: `Chain.expEven`/`Half.exp`, `Chain.up`/`Chain.down` (`↑`/`↓`, the null points
chosen from the space) and `Grassmann.Fields.chainfieldFull`/`vectorfield`.
-/

namespace Gallery.Fields

open Grassmann DirectSum StaticVectors Gallery.Versor

/-- `π` (Julia's `Float64(π)`). -/
def pi : Float := 3.141592653589793

/-- Julia's `3/7`. -/
def threeSevenths : Float := 3 / 7

/-- Julia's `0.07`. -/
def c007 : Float := 0.07

/-! ## Plane fields (`plane-1 … plane-6`) -/

/-- `exp(θ v12)` as a multivector (Julia's `exp` of a bivector term: `cos θ + sin θ v12`
or `cosh θ + sinh θ v12`, `src/composite.jl:136-160`). -/
def expPlane (V : TensorBundle) [Kernels V] (b12 : Submanifold V 2) (θ : Float) : Multivector V Float :=
  toMultivector (Chain.expEven (Chain.ofBlade b12 θ))

/-- `v1 * R` for a plane versor `R`. -/
def timesV1 (V : TensorBundle) [Kernels V] (b1 : Submanifold V 1) (R : Multivector V Float) :
    Multivector V Float :=
  toMultivector (Chain.ofBlade b1 (1 : Float)) * R

/-- `vectorfield(t)` at a planar point `p = x v1 + y v2` (Julia `chainfield(t)`; in a plane
`↑`, `↓` are the identity): `vector(p ⊘ t)`, `x ⊘ t = (~t)⟑x⟑involute(t)`. -/
@[inline] def planeField {V : TensorBundle} [Kernels V] (t : Multivector V Float) (x y : Float) :
    Float × Float :=
  let p : Chain V 1 Float := ⟨Values.ofFn fun i => if i.1 = 0 then x else y⟩
  let v := (Grassmann.Fields.chainfieldFull t p).v
  (getD v 0, getD v 1)

/-- The field of the README figure `plane-k` (`k = 1 … 6`): `vectorfield(t)` for
`t = exp(π*v12/2)`, `exp((π/2)*v12/2)`, `exp((π/4)*v12/2)`, `v1*exp((π/4)*v12/2)` in `ℝ²` and
`exp((π/8)*v12/2)`, `v1*exp((π/4)*v12/2)` in `S"+-"`. -/
def planeFieldOf (k : Nat) : Float → Float → Float × Float :=
  match k with
  | 1 => planeField (expPlane E2.V E2.v12 (pi / 2))
  | 2 => planeField (expPlane E2.V E2.v12 ((pi / 2) / 2))
  | 3 => planeField (expPlane E2.V E2.v12 ((pi / 4) / 2))
  | 4 => planeField (timesV1 E2.V E2.v1 (expPlane E2.V E2.v12 ((pi / 4) / 2)))
  | 5 => planeField (expPlane H2.V H2.v12 ((pi / 8) / 2))
  | _ => planeField (timesV1 H2.V H2.v1 (expPlane H2.V H2.v12 ((pi / 4) / 2)))

/-! ## Riemann-sphere and conformal curves -/

section Curves
open Gallery.Inf3 in
/-- `v1+v2+v3` in `S"∞+++"`. -/
def inf3P : Chain Inf3.V 1 Float := Chain.ofBlade v1 1 + Chain.ofBlade v2 1 + Chain.ofBlade v3 1

open Gallery.Inf3 in
/-- `v1+v2-v3` in `S"∞+++"`. -/
def inf3Q : Chain Inf3.V 1 Float := Chain.ofBlade v1 1 + Chain.ofBlade v2 1 - Chain.ofBlade v3 1

/-- The point at infinity `v∞` of `S"∞+++"`. -/
def inf3Inf : Chain Inf3.V 1 Float := Chain.ofBlade Inf3.vinf 1

open Gallery.Inf3 in
/-- `(3/7)*v12+v∞3` in `S"∞+++"`. -/
def inf3Torus : Chain Inf3.V 2 Float := Chain.ofBlade v12 threeSevenths + Chain.ofBlade vinf3 1

/-- The README torus curve `↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))` (`S"∞+++"`). -/
def torus (t : Float) : Chain Inf3.V 1 Float :=
  let R := Chain.expEven ((pi * t) * inf3Torus)
  Chain.down (R >>> Chain.up inf3P)

open Gallery.Inf3 in
/-- `sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3`. -/
def wobble (t : Float) : Chain Inf3.V 1 Float :=
  Chain.ofBlade v1 (Float.sin (3 * t) * 3) + Chain.ofBlade v2 (Float.cos (2 * t) * 7) -
    Chain.ofBlade v3 (Float.sin (5 * t) * 4)

/-- `v∞ * (…)`, the bivector `v∞ ∧ (…)` as a spinor (`v∞ ⟂ v₁ v₂ v₃`). -/
def infTimes (c : Float) (w : Chain Inf3.V 1 Float) : Spinor Inf3.V Float :=
  (Chain.ofBlade Inf3.vinf c * w : Half Inf3.V ((1 + 1) % 2 == 1) Float)

/-- The README `orbit-2` curve `↓(exp(t*v∞*(…)/2)>>>↑(v1+v2-v3))`. -/
def orbit2 (t : Float) : Chain Inf3.V 1 Float :=
  let R := Half.exp (infTimes t (wobble t) / (2 : Float))
  Chain.down (R >>> Chain.up inf3Q)

/-- The README `orbit-4` curve `↓(exp(t*(v12+0.07v∞*(…)/2))>>>↑(v1+v2-v3))`. -/
def orbit4 (t : Float) : Chain Inf3.V 1 Float :=
  let B : Spinor Inf3.V Float := ofBivector (Chain.ofBlade Inf3.v12 1) + infTimes c007 (wobble t) / (2 : Float)
  let R := Half.exp (t * B)
  Chain.down (R >>> Chain.up inf3Q)

open Gallery.CGA3 in
/-- `v1+v2+v3` in `S"∞∅+++"`. -/
def cga3P : Chain CGA3.V 1 Float := Chain.ofBlade v1 1 + Chain.ofBlade v2 1 + Chain.ofBlade v3 1

open Gallery.CGA3 in
/-- `(3/7)*v12+v∞3` in `S"∞∅+++"`. -/
def cga3Torus : Chain CGA3.V 2 Float := Chain.ofBlade v12 threeSevenths + Chain.ofBlade vinf3 1

/-- `v∞` of conformal space. -/
def cga3Inf : Chain CGA3.V 1 Float := Chain.ofBlade CGA3.vinf 1

/-- `v∅` of conformal space. -/
def cga3Orig : Chain CGA3.V 1 Float := Chain.ofBlade CGA3.vo 1

/-- The README helix: the torus expression evaluated in conformal space `S"∞∅+++"`. -/
def helix (t : Float) : Chain CGA3.V 1 Float :=
  let R := Chain.expEven ((pi * t) * cga3Torus)
  Chain.down (R >>> Chain.up cga3P)

end Curves

/-- Julia's `-2π:0.0001:2π`, the default sample range of `points` (125 664 values). -/
def pointsRange : FloatArray := Grassmann.Fields.pointsRange

/-! ## The 3D versor fields `orb`, `wave` -/

/-- `exp((π/4)*(v12+v∞3))` in `S"∞+++"`. -/
def orbVersor : Spinor Inf3.V Float :=
  Chain.expEven ((pi / 4) * (Chain.ofBlade Inf3.v12 (1 : Float) + Chain.ofBlade Inf3.vinf3 1))

/-- `vectorfield(t, V(2,3,4), W)` at `p`: the point read in generators `W` (0-based chain
indices `w₁ w₂ w₃`) of `S"∞+++"`, lifted, sandwiched by `t`, projected down, read in
`v1 v2 v3`. -/
@[inline] def sphereField (t : Spinor Inf3.V Float) (w₁ w₂ w₃ : Nat) (x y z : Float) :
    Float × Float × Float :=
  let p : Chain Inf3.V 1 Float := ⟨Values.ofFn fun i =>
    if i.1 = w₁ then x else if i.1 = w₂ then y else if i.1 = w₃ then z else 0⟩
  let q := Grassmann.Fields.chainfieldFull t p
  (getD q.v 1, getD q.v 2, getD q.v 3)

end Gallery.Fields
