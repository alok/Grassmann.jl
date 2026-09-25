import Tests.Forms.Common

/-!
# `↑`/`↓` (project/reject), the README curves and the versor fields against Julia

Golden `oracle/golden/forms/updown.json` (`oracle/forms/gen_parity.jl`):

* `cases`: random vectors of `S"∞+++"`, `S"∅+++"`, `S"∞∅+++"`, `S"∞∅++"`, `S"+++"`,
  `S"∞++"`: `↑ω`, `↓ω`, `↓(↑ω)`, `project(ω, b)`, `reject(ω, b)`, `project(ω, ∞, ∅)`,
  `reject(ω, ∞, ∅)` as dense vectors (Julia's `↑` of a conformal vector is a `Multivector`
  with a zero scalar; the typed result is the vector with the same coefficients).
  `rtol = 1e-12`: the formulas are Julia's, but Julia's contraction and inverse reach the
  same values through different operation orders in the null spaces.
* `curves`: the README torus, orbit and helix curves at several `t`, through `Chain.expEven`,
  `Half.exp`, `>>>` and the typed `up`/`down` (`rtol = 1e-9`: the rotor's `expm1` series
  stops where Julia's does, the curve's `↓` of Julia's `Multivector` keeps `1e-10` residues).
* `fields`: `chainfield` of the plane rotors (`plane-1 … plane-6`) and of the `orb`/`wave`
  versor at sample points (`rtol = 1e-9`).
-/

namespace Tests.FormsTests.UpDown

open Lean Tests.Units Grassmann DirectSum StaticVectors Tests.FormsTests JuliaBase

/-- Dense coefficients of a vector (Julia's `Multivector` order). -/
def denseOf {V : TensorBundle} (c : Chain V 1 Float) : List Num :=
  (toMultivector c).v.toList.map .flt

/-- The up/down checks of one vector in the space `V`. -/
def caseIn (V : TensorBundle) (t : Tally) (c : Json) (k : Nat) : Tally := Id.run do
  let x := flts (fld c "x")
  let ω : Chain V 1 Float := chainOf V 1 x
  let w := fun (s : String) => fun (_ : Unit) => s!"updown case {k} {V} x={x} {s}"
  let m : Mode := .approx 1e-12
  let mut t := t
  t := t.nums m (denseOf ω.up) (fld c "up") (w "↑")
  t := t.nums m (denseOf ω.down) (fld c "down") (w "↓")
  t := t.nums m (denseOf ω.up.down) (fld c "downup") (w "↓↑")
  -- the generic entry points agree with the typed ones
  t := t.ok ((project ω).v.toList == ω.up.v.toList && (reject ω).v.toList == ω.down.v.toList) (w "project/reject")
  let e1 : Chain V 1 Float := Composite.unitVec V Float 1
  let e2 : Chain V 1 Float := Composite.unitVec V Float 2
  if (fld c "upb") != .null then
    t := t.nums m (denseOf (ω.upWith e1)) (fld c "upb") (w "project(ω, b)")
    t := t.nums m (denseOf (ω.downWith e1)) (fld c "downb") (w "reject(ω, b)")
  if (fld c "uppm") != .null then
    t := t.nums m (denseOf (ω.upPM e1 e2)) (fld c "uppm") (w "project(ω, ∞, ∅)")
    t := t.nums m (denseOf (ω.downPM e1 e2)) (fld c "downpm") (w "reject(ω, ∞, ∅)")
  -- the multivector forms agree with the vector forms on vectors
  let mv := Multivector.up (toMultivector ω)
  t := t.nums m (mv.v.toList.map .flt) (fld c "up") (w "↑ of the multivector")
  let md := Multivector.down (toMultivector ω)
  t := t.nums (.approx 1e-11) (md.v.toList.map .flt) (fld c "down") (w "↓ of the multivector")
  return t

/-- The space of a case. -/
def dispatch (t : Tally) (c : Json) (k : Nat) : Tally :=
  match (fld c "sig").getStr?.toOption.getD "" with
  | "∞+++" => caseIn S!"∞+++" t c k
  | "∅+++" => caseIn S!"∅+++" t c k
  | "∞∅+++" => caseIn S!"∞∅+++" t c k
  | "∞∅++" => caseIn S!"∞∅++" t c k
  | "+++" => caseIn S!"+++" t c k
  | "∞++" => caseIn S!"∞++" t c k
  | s => t.ok false fun _ => s!"unknown space {s}"

/-- `π` (Julia's `Float64(π)`). -/
def pi : Float := f64! 3.141592653589793

section Curves

/-- The Riemann sphere over `ℝ³`. -/
abbrev Inf3 : TensorBundle := S!"∞+++"

/-- The unit vector `e_b` of `Inf3`. -/
def e3 (b : UInt64) (x : Float) : Chain Inf3 1 Float := Chain.ofBlade (⟨b⟩ : Submanifold Inf3 1) x

/-- A bivector blade of `Inf3`. -/
def b3 (b : UInt64) (x : Float) : Chain Inf3 2 Float := Chain.ofBlade (⟨b⟩ : Submanifold Inf3 2) x

/-- `sin(3t)*3v1+cos(2t)*7v2-sin(5t)*4v3` (Julia's order). -/
def wobble (t : Float) : Chain Inf3 1 Float :=
  e3 2 (F64.sin (3 * t) * 3) + e3 4 (F64.cos (2 * t) * 7) - e3 8 (F64.sin (5 * t) * 4)

/-- `v∞ * (x·w)` as a spinor. -/
def infTimes (x : Float) (w : Chain Inf3 1 Float) : Spinor Inf3 Float :=
  (e3 1 x * w : Half Inf3 ((1 + 1) % 2 == 1) Float)

/-- The README torus `↓(exp(π*t*((3/7)*v12+v∞3))>>>↑(v1+v2+v3))`. -/
def torus (t : Float) : Chain Inf3 1 Float :=
  let B : Chain Inf3 2 Float := b3 6 (3 / 7) + b3 9 1
  let R := Chain.expEven ((pi * t) * B)
  Chain.down (R >>> Chain.up (e3 2 1 + e3 4 1 + e3 8 1))

/-- The README `orbit-2` curve. -/
def orbit2 (t : Float) : Chain Inf3 1 Float :=
  let R := Half.exp (infTimes t (wobble t) / (2 : Float))
  Chain.down (R >>> Chain.up (e3 2 1 + e3 4 1 - e3 8 1))

/-- The README `orbit-4` curve. -/
def orbit4 (t : Float) : Chain Inf3 1 Float :=
  let B : Spinor Inf3 Float := (Half.ofChain (b3 6 1)).cast rfl + infTimes 0.07 (wobble t) / (2 : Float)
  let R := Half.exp (t * B)
  Chain.down (R >>> Chain.up (e3 2 1 + e3 4 1 - e3 8 1))

/-- Conformal space over `ℝ³`. -/
abbrev C3 : TensorBundle := S!"∞∅+++"

/-- The README helix (the torus expression in conformal space). -/
def helix (t : Float) : Chain C3 1 Float :=
  let e := fun (b : UInt64) (x : Float) => (Chain.ofBlade (⟨b⟩ : Submanifold C3 1) x : Chain C3 1 Float)
  let B : Chain C3 2 Float := Chain.ofBlade (⟨12⟩ : Submanifold C3 2) (3 / 7) + Chain.ofBlade (⟨17⟩ : Submanifold C3 2) 1
  let R := Chain.expEven ((pi * t) * B)
  Chain.down (R >>> Chain.up (e 4 1 + e 8 1 + e 16 1))

end Curves

/-- One curve sample. -/
def curveCase (t : Tally) (c : Json) (k : Nat) : Tally :=
  let x := match jnum (fld c "t") with | some (.flt f) => f | _ => 0
  let name := (fld c "curve").getStr?.toOption.getD ""
  let got := match name with
    | "torus" => denseOf (torus x)
    | "orbit2" => denseOf (orbit2 x)
    | "orbit4" => denseOf (orbit4 x)
    | _ => denseOf (helix x)
  -- Julia's `↓` of its (series-truncated) Multivector keeps ~1e-10 non-vector residues
  let want := fld c "out"
  let wantVec : Json := .arr ((arr want).zipIdx.map fun (j, i) =>
    let b := (Leibniz.indexBasisAll (if name == "helix" then 5 else 4))[i]!
    if DirectSum.Bits.popcount b == 1 then j else .str "0x0000000000000000")
  t.nums (.approx 1e-8) got wantVec fun _ => s!"curve {name}({x}) case {k}"

/-- One field sample. -/
def fieldCase (t : Tally) (c : Json) (k : Nat) : Tally :=
  let p := flts (fld c "p")
  let name := (fld c "field").getStr?.toOption.getD ""
  let e2 := fun (V : TensorBundle) (b : UInt64) => (Chain.ofBlade (⟨b⟩ : Submanifold V 1) (1 : Float) : Chain V 1 Float)
  let got : List Float := match name with
    | "plane1" =>
      let t := Single.exp (⟨3, pi / 2⟩ : Single S!"++" 2 Float)
      (Fields.chainfieldFull t (chainOf S!"++" 1 p)).v.toList
    | "plane3" =>
      let t := Single.exp (⟨3, pi / 4 / 2⟩ : Single S!"++" 2 Float)
      (Fields.chainfieldFull t (chainOf S!"++" 1 p)).v.toList
    | "plane4" =>
      let R := Single.exp (⟨3, pi / 4 / 2⟩ : Single S!"++" 2 Float)
      let t : Multivector S!"++" Float := toMultivector (e2 S!"++" 1) * toMultivector R
      (Fields.chainfieldFull t (chainOf S!"++" 1 p)).v.toList
    | "plane5" =>
      let t := Single.exp (⟨3, pi / 8 / 2⟩ : Single S!"+-" 2 Float)
      (Fields.chainfieldFull t (chainOf S!"+-" 1 p)).v.toList
    | "plane6" =>
      let R := Single.exp (⟨3, pi / 4 / 2⟩ : Single S!"+-" 2 Float)
      let t : Multivector S!"+-" Float := toMultivector (e2 S!"+-" 1) * toMultivector R
      (Fields.chainfieldFull t (chainOf S!"+-" 1 p)).v.toList
    | _ =>
      let B : Chain Inf3 2 Float := b3 6 1 + b3 9 1
      let t := Chain.expEven ((pi / 4) * B)
      let S := TensorBundle.sub Inf3 [2, 3, 4]
      let W := if name == "orb" then S else TensorBundle.sub Inf3 [1, 2, 3]
      (Fields.vectorfield t S W (Values.ofFn fun i => p[i.1]!)).toList
  t.nums (.approx 1e-9) (got.map .flt) (fld c "out") fun _ => s!"field {name} p={p} case {k}"

/-- Run the suite. -/
def suite : IO Tally := do
  let j ← load "updown"
  let t := (cases j).toList.zipIdx.foldl (fun t (c, k) => dispatch t c k) (Tally.new "forms/updown")
  let t := (arr (fld j "curves")).toList.zipIdx.foldl (fun t (c, k) => curveCase t c k) t
  let t := (arr (fld j "fields")).toList.zipIdx.foldl (fun t (c, k) => fieldCase t c k) t
  -- ↓ of spaces
  let t := t.ok (Composite.rejectSpace S!"∞+++" == TensorBundle.euclidean 3 ||
      (Composite.rejectSpace S!"∞+++").n == 3) fun _ => "↓(∞+++) has 3 generators"
  let t := t.ok ((Composite.rejectSpace S!"∞∅+++").n == 3) fun _ => "↓(∞∅+++) has 3 generators"
  -- points
  let ps := Fields.points (fun x => torus x) ⟨#[0, 0.25, 0.5]⟩
  let t := t.ok (ps.size == 3 && (ps[1]!).v.toList == (torus 0.25).v.toList) fun _ => "points"
  let cols := Fields.pointsCoords (fun x => torus x) #[1, 2, 3] ⟨#[0, 0.25, 0.5]⟩
  let t := t.ok (cols.size == 3 && (cols[0]!).get! 1 == getD (torus 0.25).v 1) fun _ => "pointsCoords"
  let t := t.ok (Fields.pointsRange.size == 125664) fun _ => s!"pointsRange has {Fields.pointsRange.size} samples"
  return t

end Tests.FormsTests.UpDown
