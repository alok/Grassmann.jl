import Gallery.Grassmann.Spaces
import Cartan

/-!
# The versor curves and fields of Cartan's `fiber.md` sessions

`docs/src/fiber.md:477-523` repeats the Grassmann README curves and fields as Cartan
`TensorField`s (inventory C5-C7). Written here with the library's Julia-exact `exp`
(`Grassmann.Chain.expEven`, `Grassmann.Half.exp`: Grassmann `src/composite.jl:83-160`), sandwich
`⊘` and `>>>`. The Riemann-sphere and conformal maps `↑`/`↓` (Grassmann `src/Grassmann.jl:164-212`)
are written out below until the library's `project`/`reject` land (docs/parity-gaps.json,
`↑/project, ↓/reject`).

| function | Julia |
|---|---|
| `torus`, `orbit2`, `orbit4` | `f(t)` of `fiber.md:482-484` in `S"∞+++"`, read in `V(2,3,4)` |
| `helix` | the first `f` in `S"∞∅+++"`, read in `V(3,4,5)` (`fiber.md:489-491`) |
| `planeField k` | `tensorfield(t)(p) = vector(p ⊘ t)` of the six plane versors (`fiber.md:497-509`) |
| `sphereField w` | `tensorfield(exp((π/4)*(v12+v∞3)), V(2,3,4))` of a point read in the generators `w` (`fiber.md:511-523`) |
-/

namespace Gallery.CartanVersors

open Grassmann DirectSum StaticVectors JuliaBase

/-- `π` (Julia's `Float64(π)`). -/
def pi : Float := f64! 3.141592653589793
/-- Julia's `3/7`. -/
def threeSevenths : Float := 3 / 7
/-- Julia's `0.07`. -/
def c007 : Float := f64! 0.07

variable {V : TensorBundle} [Kernels V]

/-! ## `↑`, `↓` -/

/-- Julia `↑ω` in a space with `∞` alone (`src/Grassmann.jl:172-177`):
`b·(ω²-1)/(ω²+1) + 2ω/(ω²+1)`, `ω² = (~ω)⋅ω`, `b` the point at infinity. -/
def upRiemann (b ω : Chain V 1 Float) : Chain V 1 Float :=
  let ω2 := getD (contraction (~ω) ω : Chain V (1 - 1) Float).v 0
  let iω2 := 1 / (ω2 + 1)
  b * ((ω2 - 1) * iω2) + (2 * iω2) * ω

/-- Julia `↓ω` in a space with `∞` alone (`src/Grassmann.jl:201-204`): `(~(ω∧b)⋅b)/(1 - b⋅ω)`. -/
def downRiemann (b ω : Chain V 1 Float) : Chain V 1 Float :=
  let wb : Chain V (1 + 1) Float := ω ∧ b
  let num : Chain V (1 + 1 - 1) Float := contraction (~wb) b
  let den := 1 - getD (contraction b ω : Chain V (1 - 1) Float).v 0
  (num.cast (by decide)) / den

/-- Julia `↑ω` in conformal space (`src/Grassmann.jl:169`): `(v∞/2)·((~ω)⋅ω) + v∅ + ω`. -/
def upConformal (inf orig ω : Chain V 1 Float) : Chain V 1 Float :=
  let ω2 := getD (contraction (~ω) ω : Chain V (1 - 1) Float).v 0
  (inf * (1 / 2 : Float)) * ω2 + orig + ω

/-- Julia `↓ω` in conformal space (`src/Grassmann.jl:197`): `((v∞∅∧ω)⋅inv(~v∞∅)) / (-ω⋅v∞)`. -/
def downConformal (inf orig ω : Chain V 1 Float) : Chain V 1 Float :=
  let io : Chain V (1 + 1) Float := inf ∧ orig
  let ioInv : Chain V 2 Float := Chain.inv (~io)
  let t : Chain V (1 + 1 + 1) Float := io ∧ ω
  let num : Chain V (1 + 1 + 1 - 2) Float := contraction t ioInv
  let den := -getD (contraction ω inf : Chain V (1 - 1) Float).v 0
  (num.cast (by decide)) / den

/-! ## Curves (`fiber.md:477-493`) -/

section Curves
open Gallery.Inf3

/-- `v1+v2+v3` in `S"∞+++"`. -/
def inf3P : Chain Inf3.V 1 Float := Chain.ofBlade v1 1 + Chain.ofBlade v2 1 + Chain.ofBlade v3 1
/-- `v1+v2-v3` in `S"∞+++"`. -/
def inf3Q : Chain Inf3.V 1 Float := Chain.ofBlade v1 1 + Chain.ofBlade v2 1 - Chain.ofBlade v3 1
/-- `v∞` of `S"∞+++"`. -/
def inf3Inf : Chain Inf3.V 1 Float := Chain.ofBlade vinf 1
/-- `(3/7)*v12+v∞3`. -/
def inf3Torus : Chain Inf3.V 2 Float := Chain.ofBlade v12 threeSevenths + Chain.ofBlade vinf3 1

/-- `f(t) = ↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))` (`fiber.md:482`). -/
def torus (t : Float) : Chain Inf3.V 1 Float :=
  downRiemann inf3Inf (Chain.expEven ((pi * t) * inf3Torus) >>> upRiemann inf3Inf inf3P)

/-- `sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3`. -/
def wobble (t : Float) : Chain Inf3.V 1 Float :=
  Chain.ofBlade v1 (F64.sin (3 * t) * 3) + Chain.ofBlade v2 (F64.cos (2 * t) * 7) -
    Chain.ofBlade v3 (F64.sin (5 * t) * 4)

/-- `c*v∞*w` as a spinor (`v∞ ⟂ v₁ v₂ v₃`). -/
def infTimes (c : Float) (w : Chain Inf3.V 1 Float) : Spinor Inf3.V Float :=
  (Chain.ofBlade vinf c * w : Half Inf3.V ((1 + 1) % 2 == 1) Float)

/-- `f(t) = ↓(exp(t*v∞*(…)/2)>>>↑(v1+v2-v3))` (`fiber.md:483`). -/
def orbit2 (t : Float) : Chain Inf3.V 1 Float :=
  downRiemann inf3Inf (Half.exp (infTimes t (wobble t) / (2 : Float)) >>> upRiemann inf3Inf inf3Q)

/-- `f(t) = ↓(exp(t*(v12+0.07v∞*(…)/2))>>>↑(v1+v2-v3))` (`fiber.md:484`). -/
def orbit4 (t : Float) : Chain Inf3.V 1 Float :=
  let B : Spinor Inf3.V Float := (Half.ofChain (Chain.ofBlade v12 (1 : Float))).cast rfl + infTimes c007 (wobble t) / (2 : Float)
  downRiemann inf3Inf (Half.exp (t * B) >>> upRiemann inf3Inf inf3Q)

end Curves

section Conformal
open Gallery.CGA3

/-- The conformal helix `↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))` in `S"∞∅+++"`
(`fiber.md:489-491`). -/
def helix (t : Float) : Chain CGA3.V 1 Float :=
  let inf : Chain CGA3.V 1 Float := Chain.ofBlade vinf 1
  let orig : Chain CGA3.V 1 Float := Chain.ofBlade vo 1
  let p : Chain CGA3.V 1 Float := Chain.ofBlade v1 1 + Chain.ofBlade v2 1 + Chain.ofBlade v3 1
  let B : Chain CGA3.V 2 Float := Chain.ofBlade v12 threeSevenths + Chain.ofBlade vinf3 1
  downConformal inf orig (Chain.expEven ((pi * t) * B) >>> upConformal inf orig p)

end Conformal

/-- The Euclidean 3-vector of coordinates `i₁, i₂, i₃` (0-based) of a chain (Julia
`V(i₁+1, i₂+1, i₃+1)(x)`). -/
@[inline] def pick3 {W : TensorBundle} (x : Chain W 1 Float) (i₁ i₂ i₃ : Nat) : Chain ℝ3 1 Float :=
  Chain.ofFn fun i => if i.1 = 0 then getD x.v i₁ else if i.1 = 1 then getD x.v i₂ else getD x.v i₃

/-! ## Plane fields (`fiber.md:495-509`) -/

/-- `vector(p ⊘ t)` at `p = x v1 + y v2` (Julia `tensorfield(t)`, `Cartan.jl:861`; in a plane
`↑`, `↓` are the identity). -/
@[inline] def planeAt {W : TensorBundle} [Kernels W] [SandwichKernels W] {q : Bool} (t : Half W q Float) (x y : Float) :
    Chain ℝ2 1 Float :=
  let p : Chain W 1 Float := ⟨Values.ofFn fun i => if i.1 = 0 then x else y⟩
  let w : Chain W 1 Float := p ⊘ t
  Chain.ofFn fun i => getD w.v i.1

/-- `exp(θ*v12)` of a plane (`Chain.expEven`, Julia's closed form). -/
def expPlane {W : TensorBundle} [Kernels W] (b12 : Submanifold W 2) (θ : Float) : Spinor W Float :=
  Chain.expEven (Chain.ofBlade b12 θ)

/-- The field of the six plane versors `exp(π*v12/2)`, `exp((π/2)*v12/2)`, `exp((π/4)*v12/2)`,
`v1*exp((π/4)*v12/2)` (`basis"2"`) and `exp((π/8)*v12/2)`, `v1*exp((π/4)*v12/2)` (`S"+-"`). -/
def planeField (k : Nat) : Float → Float → Chain ℝ2 1 Float :=
  match k with
  | 1 => planeAt (expPlane E2.v12 (pi * (1 / 2 : Float)))
  | 2 => planeAt (expPlane E2.v12 ((pi / 2) * (1 / 2 : Float)))
  | 3 => planeAt (expPlane E2.v12 ((pi / 4) * (1 / 2 : Float)))
  | 4 => planeAt ((Chain.ofBlade E2.v1 (1 : Float) * expPlane E2.v12 ((pi / 4) * (1 / 2 : Float)) : Half E2.V (true ^^ false) Float))
  | 5 => planeAt (expPlane H2.v12 ((pi / 8) * (1 / 2 : Float)))
  | _ => planeAt ((Chain.ofBlade H2.v1 (1 : Float) * expPlane H2.v12 ((pi / 4) * (1 / 2 : Float)) : Half H2.V (true ^^ false) Float))

/-- The Julia versor of plane field `k`, for captions. -/
def planeText : Nat → String
  | 1 => "exp(pi*v12/2)" | 2 => "exp((pi/2)*v12/2)" | 3 => "exp((pi/4)*v12/2)"
  | 4 => "v1*exp((pi/4)*v12/2)" | 5 => "exp((pi/8)*v12/2)" | _ => "v1*exp((pi/4)*v12/2)"

/-! ## Conformal 3-D fields (`fiber.md:511-523`) -/

/-- `exp((π/4)*(v12+v∞3))` in `S"∞+++"`. -/
def orbVersor : Spinor Inf3.V Float :=
  Chain.expEven ((pi / 4) * (Chain.ofBlade Inf3.v12 (1 : Float) + Chain.ofBlade Inf3.vinf3 1))

/-- `tensorfield(exp((π/4)*(v12+v∞3)), V(2,3,4))` at a point whose coordinates are the generators
`w₁ w₂ w₃` (0-based chain indices) of `S"∞+++"`: lifted, sandwiched, projected down, read in
`v1 v2 v3`. -/
@[inline] def sphereAt (w₁ w₂ w₃ : Nat) (x y z : Float) : Chain ℝ3 1 Float :=
  let p : Chain Inf3.V 1 Float := ⟨Values.ofFn fun i =>
    if i.1 = w₁ then x else if i.1 = w₂ then y else if i.1 = w₃ then z else 0⟩
  pick3 (downRiemann inf3Inf (upRiemann inf3Inf p ⊘ orbVersor)) 1 2 3

end Gallery.CartanVersors
