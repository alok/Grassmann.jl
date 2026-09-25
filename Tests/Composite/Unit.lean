/-
Unit tests of `Grassmann.Composite` against the Julia oracle (Julia 1.13, Grassmann
0.8.46). The expected vectors are Julia's full-precision dense coefficients of the
examples of port-notes/grassmann-composite.md §6, abstracttensors-staticvectors.md §6.6
and grassmann-types.md §4.8 (and a few more that exercise every branch), computed with
the oracle environment (`densev(x) = value(Multivector(x))`). They are compared with the
composite suite's rule `‖Δ‖₂ ≤ atol + rtol·max(‖got‖₂, ‖want‖₂)`, tightly (`1e-13`) where
Julia's and the port's algorithms coincide, and with the series tolerance where the port
evaluates a different (but equivalent) branch.

Also: Grassmann's `atanh(y, x)` special cases (port-notes §4.3.4), the Julia defects that
are fixed here (port-notes §8.3), algebraic identities, and the `TensorRing` instances.
-/
import Grassmann.Composite

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase Composite

namespace Tests.Composite.Unit

/-- Pass/fail counts with the first failure messages. -/
structure Tally where
  /-- Checks that passed. -/
  pass : Nat := 0
  /-- Checks that failed. -/
  fail : Nat := 0
  /-- The first failure messages. -/
  msgs : Array String := #[]

/-- Record a check. -/
def Tally.check (t : Tally) (ok : Bool) (msg : Unit → String) : Tally :=
  if ok then { t with pass := t.pass + 1 }
  else { t with fail := t.fail + 1, msgs := if t.msgs.size < 40 then t.msgs.push (msg ()) else t.msgs }

/-- `‖a - b‖₂` against `atol + rtol·max(‖a‖₂, ‖b‖₂)`; equal entries (including infinities
and `NaN`s) contribute nothing. -/
def near (got want : Array Float) (rtol : Float := 1e-13) (atol : Float := 1e-15) : Bool :=
  got.size == want.size &&
    let (d, ng, nw) := (got.zip want).foldl (init := (0.0, 0.0, 0.0)) fun (d, ng, nw) (a, b) =>
      let e := if a == b || (a.isNaN && b.isNaN) then 0.0 else a - b
      (d + e * e, ng + a * a, nw + b * b)
    d.sqrt ≤ atol + rtol * (if ng ≥ nw then ng.sqrt else nw.sqrt)

/-- Compare a computed multivector with Julia's dense vector. -/
def expect {V : TensorBundle} (t : Tally) (name : String) (got : Multivector V Float) (want : List Float)
    (rtol : Float := 1e-13) (atol : Float := 1e-15) : Tally :=
  let g := got.v.toArray
  t.check (near g want.toArray rtol atol) fun _ => s!"{name}: got {g} want {want}"

/-- Compare two computed multivectors. -/
def expectM {V : TensorBundle} (t : Tally) (name : String) (got want : Multivector V Float)
    (rtol : Float := 1e-13) (atol : Float := 1e-15) : Tally :=
  expect t name got want.v.toList rtol atol

/-- Compare a computed scalar with Julia's. -/
def expectF (t : Tally) (name : String) (got want : Float) (rtol : Float := 1e-13) : Tally :=
  t.check (near #[got] #[want] rtol) fun _ => s!"{name}: got {got} want {want}"

/-- The tolerance of `cosh`/`sinh` (and `cos`/`sin`/`tan`/`tanh` built on them) of elements
whose square is a scalar: Julia sums Grassmann's series until the partial sums agree to `√eps`,
the port evaluates the series' limit in closed form (`Couple.cosh`, `Chain.cos`, …); the two
differ by Julia's truncation (`~1e-11` for these inputs). -/
def seriesTol : Float := 1e-9

/-- Exact equality of floats (NaN = NaN, signed zeros distinct). -/
def same (a b : Float) : Bool := F64.isequal a b

/-! ## Spaces and elements -/

/-- Euclidean 2-space `S"++"`. -/
abbrev E2 : TensorBundle := S!"++"
/-- Euclidean 3-space `S"+++"`. -/
abbrev E3 : TensorBundle := S!"+++"
/-- Euclidean 4-space `S"++++"`. -/
abbrev E4 : TensorBundle := S!"++++"
/-- Spacetime `S"-+++"`. -/
abbrev M4 : TensorBundle := S!"-+++"
/-- 3D projective geometric algebra `D"1,1,1,0"` (Julia's `isR301`). -/
abbrev R301 : TensorBundle := D!"1,1,1,0"
/-- Conformal 3-space `S"∞∅+++"`. -/
abbrev CGA3 : TensorBundle := S!"∞∅+++"

instance : EvenDim E4 := ⟨by decide⟩

/-- A chain from its coefficients. -/
def ch (V : TensorBundle) (G : Nat) (xs : List Float) : Chain V G Float := (Chain.ofList? xs).get!
/-- A spinor from its coefficients. -/
def sp (V : TensorBundle) (xs : List Float) : Half V false Float := (Half.ofList? xs).get!
/-- A multivector from its coefficients. -/
def mv (V : TensorBundle) (xs : List Float) : Multivector V Float := (Multivector.ofList? xs).get!

/-! ## Oracle values -/

/-- `ℝ3`: couples, quaternions, chains, terms (port-notes §6). -/
def e3 (t : Tally) : Tally := Id.run do
  let mut t := t
  let c : Couple E3 Float := ⟨3, 1.0, 2.0⟩
  t := expect t "exp(1+2v12)" c.exp.toMultivector [-1.1312043837568135, 0, 0, 0, 2.4717266720048188, 0, 0, 0]
  t := expect t "log(1+2v12)" c.log.toMultivector [0.8047189562170501, 0, 0, 0, 1.1071487177940904, 0, 0, 0]
  t := expect t "sqrt(1+2v12)" c.sqrt.toMultivector [1.272019649514069, 0, 0, 0, 0.7861513777574233, 0, 0, 0]
  t := expect t "cosh(1+2v12)" c.cosh.toMultivector [-0.64214812471552, 0, 0, 0, 1.0686074213827783, 0, 0, 0]
  t := expect t "sinh(1+2v12)" c.sinh.toMultivector [-0.4890562590412937, 0, 0, 0, 1.4031192506220405, 0, 0, 0]
  t := expect t "log1p(1+2v12)" c.log1p.toMultivector [1.0397207708399179, 0, 0, 0, 0.7853981633974483, 0, 0, 0]
  t := expect t "expm1(1+2v12)" c.expm1.toMultivector [-2.131204383756814, 0, 0, 0, 2.471726672004819, 0, 0, 0]
  t := expect t "(1+2v12)^3" (c.pow 3).toMultivector [-11.0, 0, 0, 0, -2.0, 0, 0, 0]
  t := expect t "(1+2v12)^-2" (c.pow (-2)).toMultivector [-0.12000000000000002, 0, 0, 0, -0.16000000000000003, 0, 0, 0]
  t := expect t "inv(1+2v12)" c.inv.toMultivector [0.2, 0, 0, 0, -0.4, 0, 0, 0]
  t := expectF t "radius(1+2v12)" c.radius 2.23606797749979
  t := expect t "angle(1+2v12)" c.angle.toMultivector [0, 0, 0, 0, 1.1071487177940904, 0, 0, 0]
  -- the hyperbolic couple 1 + 0.5v₁
  let c2 : Couple E3 Float := ⟨1, 1.0, 0.5⟩
  t := expect t "exp(1+0.5v1)" c2.exp.toMultivector [3.065205170519096, 1.4164838998189684, 0, 0, 0, 0, 0, 0]
  t := expect t "log(1+0.5v1)" c2.log.toMultivector [-0.14384103622589053, 0.5493061443340549, 0, 0, 0, 0, 0, 0]
  t := expect t "sqrt(1+0.5v1)" c2.sqrt.toMultivector [0.9659258262890682, 0.25881904510252074, 0, 0, 0, 0, 0, 0]
  t := expect t "cbrt(1+0.5v1)" c2.cbrt.toMultivector [0.9692073842687158, 0.17550685828461604, 0, 0, 0, 0, 0, 0]
  t := expect t "cosh(1+0.5v1)" c2.cosh.toMultivector [1.7400177902090013, 0.6123918250026203, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sinh(1+0.5v1)" c2.sinh.toMultivector [1.3251873801254557, 0.8040920746317085, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "log1p(1+0.5v1)" c2.log1p.toMultivector [0.6608779199911597, 0.2554128118829953, 0, 0, 0, 0, 0, 0]
  t := expect t "expm1(1+0.5v1) (series)" c2.expm1.toMultivector [2.065205168660134, 1.4164838979600063, 0, 0, 0, 0, 0, 0]
  t := expect t "(1+0.5v1)^3" (c2.pow 3).toMultivector [1.75, 1.625, 0, 0, 0, 0, 0, 0]
  t := expect t "(1+0.5v1)^9" (c2.pow 9).toMultivector [19.22265625, 19.220703125, 0, 0, 0, 0, 0, 0]
  t := expectF t "radius(1+0.5v1)" c2.radius 0.8660254037844386
  t := expect t "angle(1+0.5v1)" c2.angle.toMultivector [0, 0.5493061443340549, 0, 0, 0, 0, 0, 0]
  -- phasors
  let p : Phasor E3 Float := Phasor.angleOn 2.0 3 0.5
  t := expect t "log(2∠0.5v12)" p.log.toMultivector [0.6931471805599453, 0, 0, 0, 0.5, 0, 0, 0]
  t := expect t "log1p(2∠0.5v12)" p.log1p.toMultivector [1.0706403744156554, 0, 0, 0, 0.3349093296212582, 0, 0, 0]
  t := expect t "complexify(2∠0.5v12)" p.complexify.toMultivector [1.7551651237807455, 0, 0, 0, 0.958851077208406, 0, 0, 0]
  t := expect t "complexify(sqrt(p))" p.sqrt.complexify.toMultivector [1.3702490875349536, 0, 0, 0, 0.34988203456254696, 0, 0, 0]
  t := expect t "complexify(p^2)" (p.pow 2).complexify.toMultivector [2.161209223472559, 0, 0, 0, 3.365883939231586, 0, 0, 0]
  t := expect t "complexify(inv(p))" p.inv.complexify.toMultivector [0.4387912809451864, 0, 0, 0, -0.2397127693021015, 0, 0, 0]
  let pz := (⟨3, 1.0, 1.0⟩ : Couple E3 Float).polarize
  t := expectF t "polarize(1+v12) amplitude" pz.amp 1.4142135623730951
  t := expectF t "polarize(1+v12) angle" pz.angle.im 0.7853981633974483
  -- quaternions
  let q := sp E3 [1.0, 0.3, 0.2, 0.4]
  t := expect t "exp(q)" (toMultivector q.exp) [2.3335646731843487, 0, 0, 0, 0.776637050431162, 0.5177580336207748, 1.0355160672415495, 0]
  t := expect t "log(q)" (toMultivector q.log) [0.1273211091867903, 0, 0, 0, 0.2751915559584776, 0.18346103730565178, 0.36692207461130355, 0]
  t := expect t "sqrt(q)" (toMultivector q.sqrt) [1.0333880367896793, 0, 0, 0, 0.145153606060691, 0.09676907070712736, 0.1935381414142547, 0]
  t := expect t "cbrt(q)" (toMultivector q.cbrt) [1.029241359593854, 0, 0, 0, 0.09527548340234183, 0.06351698893489457, 0.12703397786978915, 0]
  t := expect t "q^3" (toMultivector (q.pow 3)) [0.12999999999999984, 0, 0, 0, 0.8130000000000001, 0.542, 1.084, 0]
  t := expect t "inv(q)" (toMultivector q.invD) [0.7751937984496123, 0, 0, 0, -0.2325581395348837, -0.15503875968992248, -0.31007751937984496, 0]
  t := expect t "log1p(q)" (toMultivector q.log1p) [0.7281433664699628, 0, 0, 0, 0.1465249562720337, 0.09768330418135582, 0.19536660836271164, 0]
  t := expect t "log(-1+0.2v12+0.1v13+0.3v23)" (toMultivector (sp E3 [-1.0, 0.2, 0.1, 0.3]).log)
    [0.06551413120320204, 0, 0, 0, 1.4878719793419293, 0.7439359896709646, 2.231807969012894, 0]
  t := expect t "exp(0.5+0.3v12+0.2v13+0.4v23)" (toMultivector (sp E3 [0.5, 0.3, 0.2, 0.4]).exp)
    [1.415378520708599, 0, 0, 0, 0.4710541825552865, 0.3140361217035244, 0.6280722434070488, 0]
  t := expect t "expm1(0.3v12+0.2v13+0.4v23) (generated series)" (toMultivector (sp E3 [0.0, 0.3, 0.2, 0.4]).expm1)
    [-0.14152953209276206, 0, 0, 0, 0.28570880412104, 0.19047253608069337, 0.38094507216138673, 0]
  -- bivector chain b = 0.3v12 + 0.2v13 + 0.4v23
  let b := ch E3 2 [0.3, 0.2, 0.4]
  t := expect t "exp(b)" b.exp [0.8584704679084777, 0, 0, 0, 0.2857088041056532, 0.1904725360704355, 0.380945072140871, 0]
  t := expect t "expEven(b)" (toMultivector b.expEven) [0.8584704679084777, 0, 0, 0, 0.2857088041056532, 0.1904725360704355, 0.380945072140871, 0]
  t := expect t "expm1(b)" b.expm1 [-0.14152953209276206, 0, 0, 0, 0.28570880412104, 0.19047253608069337, 0.38094507216138673, 0]
  t := expect t "cosh(b)" (toMultivector b.cosh) [0.8584704679072379, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sinh(b)" (toMultivector b.sinh) [0, 0, 0, 0, 0.28570880410562455, 0.19047253607041642, 0.38094507214083284, 0]
  t := expect t "cos(b)" (toMultivector b.cos) [1.1485382162599247, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sin(b)" (toMultivector b.sin) [0, 0, 0, 0, 0.31471170758883643, 0.20980780505922425, 0.4196156101184485, 0]
  t := expect t "tan(b)" (toMultivector b.tan) [0, 0, 0, 0, 0.2740106538323617, 0.18267376922157444, 0.3653475384431489, 0] seriesTol
  t := expect t "log(b)" b.log [-0.6189983495307403, 0, 0, 0, 0.8750112841954446, 0.5833408561302997, 1.1666817122605972, 0]
  t := expect t "sqrt(b)" b.sqrt [0.518911844577261, 0, 0, 0, 0.2890487571693053, 0.1926991714462046, 0.3853983428924085, 0]
  t := expect t "b^3" (b.pow 3) [0, 0, 0, 0, -0.08700000000000001, -0.05800000000000001, -0.11600000000000002, 0]
  t := expect t "b^9" (b.pow 9) [0, 0, 0, 0, 0.0021218430000000013, 0.001414562000000001, 0.002829124000000002, 0]
  -- vector chain w = 0.3v1 + 0.4v2
  let w := ch E3 1 [0.3, 0.4, 0.0]
  t := expect t "exp(w)" w.exp [1.1276259652063807, 0.3126571832962484, 0.41687624439499793, 0, 0, 0, 0, 0]
  t := expect t "cosh(w)" (toMultivector w.cosh) [1.1276259652058704, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sinh(w)" (toMultivector w.sinh) [0, 0.31265718328889713, 0.4168762443851962, 0, 0, 0, 0, 0] seriesTol
  t := expect t "cos(w)" (toMultivector w.cos) [0.8775825618898637, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sin(w)" (toMultivector w.sin) [0, 0.28765532316984954, 0.3835404308931327, 0, 0, 0, 0, -0.0] seriesTol
  t := expect t "w^5" (w.pow 5) [0, 0.01875, 0.025, 0, 0, 0, 0, 0]
  t := expect t "exp(v1+v2+v3)" (ch E3 1 [1.0, 1.0, 1.0]).exp [2.9145774401759277, 1.580586563566668, 1.580586563566668, 1.580586563566668, 0, 0, 0, 0]
  -- multivectors
  t := expect t "exp(v1+2v12)" (mv E3 [0, 1, 0, 0, 2, 0, 0, 0]).exp [-0.6172728764571667, 0.35184490787569894, 0, 0, 0.7036898157513979, 0, 0, 0]
  t := expect t "exp(1+0.3v1+0.2v12+0.1v123)" (mv E3 [1.0, 0.3, 0, 0, 0.2, 0, 0, 0.1]).exp
    [2.7726014944000505, 0.8181892005743616, 3.512913380123986e-19, -0.05472849582850522, 0.5454594670495745, 1.1189305233229307e-18, 0.08209274374275781, 0.27818806071313795]
  let m := mv E3 [0.5, 0.1, 0.2, 0.3, 0.3, 0.2, 0.4, 0.2]
  t := expect t "exp(m)" m.exp [1.46528043494659, 0.009730739529653162, 0.38654736657164557, 0.3595695173500648, 0.5798210498574684, 0.23971301156670988, 0.6629689668895895, 0.44465967448632787]
  t := expect t "expm1(m)" m.expm1 [0.46528043494658994, 0.009730739529653162, 0.38654736657164557, 0.3595695173500648, 0.5798210498574684, 0.23971301156670988, 0.6629689668895895, 0.44465967448632787]
  t := expect t "m^9" (m.pow 9) [0.30112039999999995, 0.234344016, -0.0018751679999999792, 0.279525168, -0.0028127519999999323, 0.186350112, 0.13741862400000007, 0.10557603200000007]
  t := expect t "m^4" (m.pow 4) [-0.41080000000000005, -0.3416, 0.12479999999999997, -0.29760000000000003, 0.18719999999999998, -0.19840000000000002, 0.007200000000000005, 0.07679999999999998]
  let m1 := mv E3 [1.0, 0, 0, 0, 0.2, 0.1, 0.3, 0]
  t := expect t "log(1+0.2v12+0.1v13+0.3v23) (qlog)" m1.log [0.06551413249770295, 0, 0, 0, 0.19137992868351744, 0.09568996434175872, 0.2870698930252761, 0]
  t := expect t "log1p(1+0.2v12+0.1v13+0.3v23) (qlog)" m1.log1p [0.7103478939816238, 0, 0, 0, 0.0988572372008109, 0.04942861860040544, 0.14828585580121634, 0]
  -- terms
  let s1 : Single E3 1 Float := ⟨1, 2.0⟩
  t := expect t "exp(2.0v1)" s1.exp.toMultivector [3.7621956910836314, 3.6268604078470186, 0, 0, 0, 0, 0, 0]
  t := expect t "exp(v1)" (Single.exp (⟨1, 1.0⟩ : Single E3 1 Float)).toMultivector [1.5430806348152437, 1.1752011936438014, 0, 0, 0, 0, 0, 0]
  t := expect t "exp(v12)" (Single.exp (⟨3, 1.0⟩ : Single E3 2 Float)).toMultivector [0.5403023058681398, 0, 0, 0, 0.8414709848078965, 0, 0, 0]
  t := expect t "exp(v123)" (Single.exp (⟨7, 1.0⟩ : Single E3 3 Float)).toMultivector [0.5403023058681398, 0, 0, 0, 0, 0, 0, 0.8414709848078965]
  t := expect t "exp(0.7v123)" (Single.exp (⟨7, 0.7⟩ : Single E3 3 Float)).toMultivector [0.7648421872844885, 0, 0, 0, 0, 0, 0, 0.644217687237691]
  t := expect t "exp(2.0v)" (Single.exp (⟨0, 2.0⟩ : Single E3 0 Float)).toMultivector [7.38905609893065, 0, 0, 0, 0, 0, 0, 0]
  let h : Single E3 2 Float := ⟨3, 0.5⟩
  t := expect t "tan(0.5v12)" (toMultivector h.tan) [0, 0, 0, 0, 0.46211715724935354, 0, 0, 0] seriesTol
  t := expect t "tanh(0.5v12)" (toMultivector h.tanh) [0, 0, 0, 0, 0.5463024898580239, 0, 0, 0] seriesTol
  t := expect t "cosh(0.5v12)" (toMultivector h.cosh) [0.8775825618898637, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sinh(0.5v12)" (toMultivector h.sinh) [0, 0, 0, 0, 0.4794255386164159, 0, 0, 0] seriesTol
  t := expect t "cos(1.0v12)" (toMultivector (Single.cos (⟨3, 1.0⟩ : Single E3 2 Float))) [1.543080634803725, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sin(1.0v12)" (toMultivector (Single.sin (⟨3, 1.0⟩ : Single E3 2 Float))) [0, 0, 0, 0, 1.175201193643034, 0, 0, 0] seriesTol
  t := expect t "cos(1.0v1)" (toMultivector (Single.cos (⟨1, 1.0⟩ : Single E3 1 Float))) [0.5403023058795628, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "sin(1.0v1)" (toMultivector (Single.sin (⟨1, 1.0⟩ : Single E3 1 Float))) [0, 0.8414709848086585, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "cos(0.5v123)" (toMultivector (Single.cos (⟨7, 0.5⟩ : Single E3 3 Float))) [1.1276259652063807, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "sin(0.5v123)" (toMultivector (Single.sin (⟨7, 0.5⟩ : Single E3 3 Float))) [0, 0, 0, 0, 0, 0, 0, 0.5210953054937474]
  t := expect t "cos(1.0v)" (toMultivector (Single.cos (⟨0, 1.0⟩ : Single E3 0 Float))) [0.5403023058795628, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "2^(0.5v12)" (Single.rpow 2.0 h).toMultivector [0.9405421046832438, 0, 0, 0, 0.3396771251026685, 0, 0, 0]
  t := expect t "exp10(0.5v12)" (Single.rpow 10.0 h).toMultivector [0.40730731015394683, 0, 0, 0, 0.9132911666577952, 0, 0, 0]
  t := expect t "log(2.0v)" (Single.log (⟨0, 2.0⟩ : Single E3 0 Float)).toMultivector [0.6931471805599453, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "log(-2.0v)" (Single.log (⟨0, -2.0⟩ : Single E3 0 Float)).toMultivector [0.6931471805599453, 0, 0, 0, 0, 0, 0, 3.141592653589793]
  t := expect t "log(0.5v12)" h.log.toMultivector [-0.6931471805599453, 0, 0, 0, 1.5707963267948966, 0, 0, 0]
  t := expect t "sqrt(0.3v12)" (Single.sqrt (⟨3, 0.3⟩ : Single E3 2 Float)).toMultivector [0.3872983346207417, 0, 0, 0, 0.38729833462074165, 0, 0, 0]
  t := expect t "sqrt(-4.0+0.0v12)" (Couple.sqrt (⟨3, -4.0, 0.0⟩ : Couple E3 Float)).toMultivector [0, 0, 0, 0, 2.0, 0, 0, 0]
  t := expect t "log1p(1.0v) (series)" (Single.log1p (⟨0, 1.0⟩ : Single E3 0 Float)).toMultivector [0.6931471795482411, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "(0.5v12)^5" (h.pow 5).toMultivector [0, 0, 0, 0, 0.03125, 0, 0, 0]
  t := expect t "(0.5v12)^-3" (h.pow (-3)).toMultivector [0, 0, 0, 0, 8.0, 0, 0, 0]
  -- AbstractTensors' family through the multivector (Julia evaluates these on the term: agreement to the series tolerance)
  let hm := toMultivector h
  t := expect t "asinh(0.5v12)" h.asinh.toMultivector [-5.551115123125783e-17, 0, 0, 0, 0.5235987755982989, 0, 0, 0]
  t := expect t "atanh(0.5v12)" h.atanh.toMultivector [0, 0, 0, 0, 0.4636476090008061, 0, 0, 0]
  t := expect t "acosh(2.0+0.5v12)" (Couple.acosh (⟨3, 2.0, 0.5⟩ : Couple E3 Float)).toMultivector [1.3618009008578458, 0, 0, 0, 0.27775425655771396, 0, 0, 0]
  t := expect t "asin(0.5v12)" (toMultivector h.asin) [0, 0, 0, 0, 0.4812118250596034, 0, 0, 0]
  t := expect t "asin(0.5v1)" (toMultivector (Single.asin (⟨1, 0.5⟩ : Single E3 1 Float))) [0, 0.5235987755982989, 0, 0, 0, 0, 0, 5.551115123125783e-17] 1e-13 1e-15
  t := expect t "asinh(0.5v1)" (Single.asinh (⟨1, 0.5⟩ : Single E3 1 Float)).toMultivector [0, 0.4812118250596034, 0, 0, 0, 0, 0, 0]
  t := expect t "atanh(0.5v1)" (Single.atanh (⟨1, 0.5⟩ : Single E3 1 Float)).toMultivector [0, 0.5493061443340549, 0, 0, 0, 0, 0, 0]
  t := expect t "atanh(0.25v12)" (Single.atanh (⟨3, 0.25⟩ : Single E3 2 Float)).toMultivector [0, 0, 0, 0, 0.24497866312686414, 0, 0, 0]
  t := expect t "atan(0.5v12)" (toMultivector h.atan) [0, 0, 0, 0, 0.5493061443340549, 0, 0, -0.0]
  t := expect t "atan(0.5v1)" (toMultivector (Single.atan (⟨1, 0.5⟩ : Single E3 1 Float))) [0, 0.4636476090008061, 0, 0, 0, 0, 0, -0.0]
  -- through the multivector (qlog series: agreement to the series tolerance)
  t := expect t "asinh(0.5v12) (multivector)" hm.asinh [-5.551115123125783e-17, 0, 0, 0, 0.5235987755982989, 0, 0, 0] 1e-7 1e-9
  t := expect t "atanh(0.5v12) (multivector)" hm.atanh [0, 0, 0, 0, 0.4636476090008061, 0, 0, 0] 1e-7 1e-9
  t := expect t "log2(1+0.5v12)" (Multivector.addScalar 1.0 hm).log2 [0.16096404744368117, 0, 0, 0, 0.6689021062254881, 0, 0, 0] 1e-7 1e-9
  t := expect t "log10(1+0.5v12)" (Multivector.addScalar 1.0 hm).log10 [0.04845500650402821, 0, 0, 0, 0.20135959813668655, 0, 0, 0] 1e-7 1e-9
  t := expect t "tanh(0.5v12) (multivector)" hm.tanh [0, 0, 0, 0, 0.5463024898580239, 0, 0, 0] 1e-9 1e-12
  t := expect t "exp2(1.0v12)" (toMultivector (⟨3, 1.0⟩ : Single E3 2 Float)).exp2 [0.7692389013639721, 0, 0, 0, 0.6389612763136348, 0, 0, 0]
  -- pseudo-couples and co-spinors
  let pc : PseudoCouple E3 Float := ⟨0, 1.0, 2.0⟩
  t := expect t "exp(1.0v+2.0v123)" pc.exp [-1.1312043837568135, 0, 0, 0, 0, 0, 0, 2.4717266720048188]
  t := expect t "log(1.0v+2.0v123)" pc.log [0.8047189562170501, 0, 0, 0, 0, 0, 0, 1.1071487177940904]
  t := expect t "log1p(1.0v+2.0v123)" pc.log1p [1.0397207708399179, 0, 0, 0, 0, 0, 0, 0.7853981633974483]
  t := expect t "expm1(1.0v+2.0v123)" pc.expm1 [-2.1312043837568133, 0, 0, 0, 0, 0, 0, 2.4717266720048188]
  let pc3 : PseudoCouple E3 Float := ⟨4, 1.0, 2.0⟩
  t := expect t "exp(1.0v3+2.0v123) (series)" pc3.exp [-0.6421481248556042, 0, 0, -0.48905626147518083, 1.0686074211144896, 0, 0, 1.4031192506619508]
  t := expect t "expm1(1.0v3+2.0v123) (series)" pc3.expm1 [-1.6421481248556042, 0, 0, -0.48905626147518083, 1.0686074211144896, 0, 0, 1.4031192506619508]
  let cs : CoSpinor E3 Float := (Half.ofList? [0.3, -0.2, 0.1, 0.4]).get!
  t := expect t "exp(CoSpinor)" (CoSpinor.exp cs) [0.9862909824513748, 0.28281100790489416, -0.18854067193659613, 0.09427033596829806, 0.039856858772278674, 0.07971371754455735, 0.11957057631683597, 0.41699713906895947]
  t := expect t "expm1(CoSpinor)" (CoSpinor.expm1 cs) [-0.013709017548625229, 0.28281100790489416, -0.18854067193659613, 0.09427033596829806, 0.039856858772278674, 0.07971371754455735, 0.11957057631683597, 0.41699713906895947]
  -- hyperbolic couples (series) and the inverse functions of couples
  let hc : Couple E3 Float := ⟨1, 0.5, 0.2⟩
  t := expect t "cosh(0.5+0.2v1)" hc.cosh.toMultivector [1.1502537598798628, 0.10491524575100228, 0, 0, 0, 0, 0, 0]
  t := expect t "sinh(0.5+0.2v1)" hc.sinh.toMultivector [0.5315519976425583, 0.22703170419541568, 0, 0, 0, 0, 0, 0] seriesTol
  -- Julia divides hyperbolic couples with the elliptic formula (defect couple-inv-hyperbolic);
  -- the true tanh splits over the idempotents: (tanh 0.7 ± tanh 0.3)/2
  t := expect t "tanh(0.5+0.2v1) (fixed)" hc.tanh.toMultivector
    [(Float.tanh 0.7 + Float.tanh 0.3) / 2, (Float.tanh 0.7 - Float.tanh 0.3) / 2, 0, 0, 0, 0, 0, 0] 1e-9 1e-12
  t := expect t "asinh(0.5+0.2v12)" (Couple.asinh (⟨3, 0.5, 0.2⟩ : Couple E3 Float)).toMultivector [0.4884827894227804, 0, 0, 0, 0.17925945451498054, 0, 0, 0]
  t := expect t "acosh(2.0+0.3v12)" (Couple.acosh (⟨3, 2.0, 0.3⟩ : Couple E3 Float)).toMultivector [1.3338227904809452, 0, 0, 0, 0.17070047143619652, 0, 0, 0]
  t := expect t "atanh(0.5+0.2v12)" (Couple.atanh (⟨3, 0.5, 0.2⟩ : Couple E3 Float)).toMultivector [0.5166065433919413, 0, 0, 0, 0.2565289547045195, 0, 0, 0]
  t := expect t "acoth(2.0+0.2v12)" (Couple.acoth (⟨3, 2.0, 0.2⟩ : Couple E3 Float)).toMultivector [0.540609615312701, 0, 0, 0, -0.06541369803702848, 0, 0, 0]
  t := expect t "asinh(0.5+0.2v1)" (Couple.asinh hc).toMultivector [0.47416980682288906, 0.17849675925946665, 0, 0, 0, 0, 0, 0]
  t := expect t "atanh(0.5+0.2v1)" (Couple.atanh hc).toMultivector [0.5884100659485825, 0.2788904617454707, 0, 0, 0, 0, 0, 0]
  -- the co/pseudo family
  t := expect t "pseudoexp(0.5v3)" (ch E3 1 [0, 0, 0.5]).coexp [0, 0, 0, 0.479425538604203, 0, 0, 0, 0.8775825618903728]
  t := expect t "pseudoabs(3v1+4v2)" (toMultivector (ch E3 1 [3.0, 4.0, 0]).coabs) [0, 0, 0, 0, 0, 0, 0, 5.0]
  t := expect t "pseudoinv(2v12)" (toMultivector (ch E3 2 [2.0, 0, 0]).coinv) [0, 0, 0, 0, 0.5, 0, 0, 0]
  t := expect t "pseudosin(0.5v3)" (ch E3 1 [0, 0, 0.5]).cosin [0, 0, 0, 0.5210953054814953, 0, 0, 0, 0] seriesTol
  t := expect t "pseudocosh(0.5v3)" (ch E3 1 [0, 0, 0.5]).cocosh [0, 0, 0, 0, 0, 0, 0, 0.8775825618898637] seriesTol
  t := expect t "geomabs(3v1+4v123)" (mv E3 [0, 3.0, 0, 0, 0, 0, 0, 4.0]).geomabs [5.0, 0, 0, 0, 0, 0, 0, 5.0]
  t := expect t "unitize(3v1+4v123)" (mv E3 [0, 3.0, 0, 0, 0, 0, 0, 4.0]).unitize [0, 0.6000000000000001, 0, 0, 0, 0, 0, 0.8]
  return t

/-- Other spaces: `ℝ2`, `ℝ4`, spacetime, 3D PGA, conformal 3-space. -/
def spaces (t : Tally) : Tally := Id.run do
  let mut t := t
  -- ℝ2: I = v₁₂ is the couple's blade, so its trigonometric functions are complex
  let z : Couple E2 Float := ⟨3, 1.0, 0.5⟩
  t := expect t "E2 cos(1+0.5v12)" z.cos [0.6092589091577942, 0, 0, -0.4384865798925953]
  t := expect t "E2 sin(1+0.5v12)" z.sin [0.948864531437168, 0, 0, 0.28154899513533443]
  t := expect t "E2 tan(1+0.5v12)" z.tan [0.8068774121630847, 0, 0, 1.042830728344361]
  t := expect t "E2 cos(0.3v1+0.4v2)" (toMultivector (ch E2 1 [0.3, 0.4]).cos) [1.1276259652058704, 0, 0, 0] seriesTol
  -- ℝ4: I² = +1
  let bb := ch E4 2 [0.3, 0.2, 0.1, 0.4, 0.5, 0.7]
  t := expect t "E4 exp(bivector) (series)" bb.exp [0.5269074368582443, 0, 0, 0, 0, 0.21935060373512008, 0.18972844044841117, 0.06561778090739673, 0.32996290666837663, 0.42707685299387516, 0.5718107714164264, 0, 0, 0, 0, 0.1253537950370727]
  t := expect t "E4 cosh(bivector)" (toMultivector bb.cosh) [0.526907436813054, 0, 0, 0, 0, 5.801997060957461e-18, 0, 0, 0, 0, -3.1221221146036047e-19, 0, 0, 0, 0, 0.12535379508086913] 1e-13 1e-16
  t := expect t "E4 sinh(bivector)" (toMultivector bb.sinh) [-5.794953248061134e-19, 0, 0, 0, 0, 0.21935060419470212, 0.1897284403181839, 0.06561778113586925, 0.32996290690476016, 0.42707685314256144, 0.5718107718865565, 0, 0, 0, 0, 1.438002236516593e-18] 1e-13 1e-16
  t := expect t "E4 cos(1.0v) = cosh(1) (quirk B2)" (toMultivector (Single.cos (⟨0, 1.0⟩ : Single E4 0 Float))) [1.543080634803725, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] seriesTol
  t := expect t "E4 log(-2.0v) (sign lost, I² = +1)" (Single.log (⟨0, -2.0⟩ : Single E4 0 Float)).toMultivector [0.6931471805599453, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "E4 exp(vector)" (ch E4 1 [0.3, 0.4, 0.1, 0.2]).exp [1.1537877015640245, 0.3152266138575838, 0.4203021518101118, 0.10507553795252796, 0.2101510759050559, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "E4 log(1+0.1v12) (qlog)" (toMultivector (sp E4 [1.0, 0.1, 0, 0, 0, 0, 0, 0]).log) [0.004975165426397965, 0, 0, 0, 0, 0.09966865249077625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  -- spacetime
  let z16 := fun (i : Nat) (x : Float) (j : Nat) (y : Float) =>
    (List.range 16).map fun k => if k == i then x else if k == j then y else 0.0
  t := expect t "M4 exp(0.5v1)" (Single.exp (⟨1, 0.5⟩ : Single M4 1 Float)).toMultivector (z16 0 0.8775825618903728 1 0.479425538604203)
  t := expect t "M4 exp(0.5v2)" (Single.exp (⟨2, 0.5⟩ : Single M4 1 Float)).toMultivector (z16 0 1.1276259652063807 2 0.5210953054937474)
  t := expect t "M4 exp(0.5v12)" (Single.exp (⟨3, 0.5⟩ : Single M4 2 Float)).toMultivector (z16 0 1.1276259652063807 5 0.5210953054937474)
  t := expect t "M4 exp(0.5v23)" (Single.exp (⟨6, 0.5⟩ : Single M4 2 Float)).toMultivector (z16 0 0.8775825618903728 8 0.479425538604203)
  t := expect t "M4 exp(0.3v1+0.4v2)" (ch M4 1 [0.3, 0.4, 0, 0]).exp [1.035204643651505, 0.30351227043652884, 0.4046830272487052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "M4 exp(0.5v1+0.4v2)" (ch M4 1 [0.5, 0.4, 0, 0]).exp [0.9553364891256061, 0.4925336777688993, 0.39402694221511947, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "M4 exp(0.4v1+0.4v2) (null)" (ch M4 1 [0.4, 0.4, 0, 0]).exp [1.0, 0.4, 0.4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "M4 exp(0.3v12+0.4v23)" (ch M4 2 [0.3, 0, 0, 0.4, 0, 0]).exp [0.965203690872801, 0, 0, 0, 0, 0.29651222960317025, 0, 0, 0.39534963947089374, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "M4 log(2.0+0.5v1)" (Couple.log (⟨1, 2.0, 0.5⟩ : Couple M4 Float)).toMultivector (z16 0 0.7234594914681627 1 0.24497866312686414)
  t := expect t "M4 log(2.0+0.5v12) (hyperbolic)" (Couple.log (⟨3, 2.0, 0.5⟩ : Couple M4 Float)).toMultivector (z16 0 0.6608779199911597 5 0.2554128118829953)
  -- 3D PGA ⟨1,1,1,0⟩: Julia's closed form
  t := expect t "PGA exp(bivector)" (ch R301 2 [0.3, 0.2, 0.1, 0.4, 0.5, 0.7]).exp [0.8584704679084777, 0, 0, 0, 0, 0.28570880410565325, 0.1904725360704355, 0.07581029304686612, 0.380945072140871, 0.4858943276702645, 0.6520843950052605, 0, 0, 0, 0, 0.1428544020528266]
  t := expect t "PGA exp(0.3v12+0.4v34)" (ch R301 2 [0.3, 0, 0, 0, 0, 0.4]).exp [0.955336489125606, 0, 0, 0, 0, 0.29552020666133955, 0, 0, 0, 0, 0.38213459565024244, 0, 0, 0, 0, 0.11820808266453582]
  t := expect t "PGA exp(ideal bivector)" (ch R301 2 [0, 0, 0.3, 0, 0.2, 0]).exp [1.0, 0, 0, 0, 0, 0, 0, 0.3, 0, 0.2, 0, 0, 0, 0, 0, 0]
  -- conformal 3-space (null basis)
  let z32 := fun (i : Nat) (x : Float) (j : Nat) (y : Float) =>
    (List.range 32).map fun k => if k == i then x else if k == j then y else 0.0
  t := expect t "CGA3 exp(0.5v∞1) (null)" (Single.exp (⟨5, 0.5⟩ : Single CGA3 2 Float)).toMultivector (z32 0 1.0 7 0.5)
  t := expect t "CGA3 exp(0.5v∞∅)" (Single.exp (⟨3, 0.5⟩ : Single CGA3 2 Float)).toMultivector (z32 0 1.1276259652063807 6 0.5210953054937474)
  t := expect t "CGA3 exp(bivector)" (ch CGA3 2 [0.1, 0.2, 0, 0, 0.3, 0, 0, 0, 0, 0.1]).exp [1.0603831280039682, 0, 0, 0, 0, 0, 0.1016703153968254, 0.2033406307936508, 0, 0, 0.30501094619047614, 0, 0, 0, 0, 0.10639319317460318, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0.01020105774603175, 0.0204021154920635, 0.030603173238095235, 0]
  t := expect t "CGA3 (0.5v∞∅)^3" (Single.pow (⟨3, 0.5⟩ : Single CGA3 2 Float) 3).toMultivector (z32 6 0.125 6 0.125)
  return t

/-! ## Grassmann's `atanh(y, x)` (port-notes §4.3.4) -/

/-- The special cases and goldens of the two-argument hyperbolic arctangent. -/
def atanh2Tests (t : Tally) : Tally := Id.run do
  let mut t := t
  let inf := F64.inf
  let cases : List (Float × Float × Float) :=
    [(0.5, 1.0, 0.5493061443340549), (0.5, -1.0, 0.5493061443340549), (-0.5, 2.0, -0.2554128118829953),
     (0.5, -2.0, 0.2554128118829953), (0.0, 1.0, 0.0), (2.0, inf, 0.0), (-2.0, -inf, -0.0),
     (inf, inf, inf), (1.0, 2.0, 0.5493061443340549)]
  for (y, x, want) in cases do
    t := t.check (same (atanh2 y x) want) fun _ => s!"atanh({y}, {x}) = {atanh2 y x}, want {want}"
  -- Julia `DomainError`s are `NaN` here
  for (y, x) in [(3.0, 1.0), (1.0, 0.0), (inf, 2.0), (F64.nan, 1.0)] do
    t := t.check (atanh2 y x).isNaN fun _ => s!"atanh({y}, {x}) = {atanh2 y x}, want NaN"
  return t

/-! ## Julia defects fixed here (port-notes §8.3) -/

/-- The fixes of port-notes §8.3 items 1, 2, 5, 8, 11, 13 and the term powers. -/
def fixes (t : Tally) : Tally := Id.run do
  let mut t := t
  let e := F64.exp 1.0
  -- item 1: exp(Multivector(2.0)) is e² (Julia 3e²); exp(1 + 0.5v₁₄) in ⟨1,1,1,0⟩ is e(1 + 0.5v₁₄)
  t := expect t "exp(Multivector(2.0))" (mv E3 [2.0, 0, 0, 0, 0, 0, 0, 0]).exp [F64.exp 2.0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "exp(Spinor(-2.0))" (toMultivector (sp E3 [-2.0, 0, 0, 0]).exp) [F64.exp (-2.0), 0, 0, 0, 0, 0, 0, 0]
  t := expect t "exp(1+0.5v14) parabolic" (Couple.exp (⟨9, 1.0, 0.5⟩ : Couple R301 Float)).toMultivector
    [e, 0, 0, 0, 0, 0, 0, e * 0.5, 0, 0, 0, 0, 0, 0, 0, 0]
  -- item 2: a zero angle is not NaN
  t := expect t "exp(1+0v12)" (Couple.exp (⟨3, 1.0, 0.0⟩ : Couple E3 Float)).toMultivector [e, 0, 0, 0, 0, 0, 0, 0]
  -- item 5: a single PGA bivector (Julia NaN)
  t := expect t "PGA exp(0.3v12)" (Single.exp (⟨3, 0.3⟩ : Single R301 2 Float)).toMultivector
    [0.955336489125606, 0, 0, 0, 0, 0.29552020666133955, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  -- item 8: cbrt of an elliptic couple (Julia MethodError): the principal cube root
  let cb := (Couple.cbrt (⟨3, 1.0, 2.0⟩ : Couple E3 Float))
  t := expect t "cbrt(1+2v12)^3" (cb.pow 3).toMultivector [1.0, 0, 0, 0, 2.0, 0, 0, 0] 1e-14
  -- item 11: exp of a phasor is exp of its complexification
  let p : Phasor E3 Float := Phasor.angleOn 2.0 3 0.5
  t := expectM t "complexify(exp(p))" p.exp.complexify.toMultivector p.complexify.exp.toMultivector 1e-15
  -- item 13: expm1 of a negative pure-scalar spinor
  t := expect t "expm1(Spinor(-2.0))" (toMultivector (sp E3 [-2.0, 0, 0, 0]).expm1) [F64.expm1 (-2.0), 0, 0, 0, 0, 0, 0, 0]
  -- term powers: null blades vanish, negative powers invert
  t := expect t "(0.5v∞)^2" (Single.pow (⟨1, 0.5⟩ : Single CGA3 1 Float) 2).toMultivector ((List.range 32).map fun _ => 0.0)
  t := expect t "(0.5v∞)^5" (Single.pow (⟨1, 0.5⟩ : Single CGA3 1 Float) 5).toMultivector ((List.range 32).map fun _ => 0.0)
  t := expect t "(2v1)^-1" (Single.pow (⟨1, 2.0⟩ : Single E3 1 Float) (-1)).toMultivector [0, 0.5, 0, 0, 0, 0, 0, 0]
  t := expect t "(0.3v1+0.4v2)^-1" ((ch E3 1 [0.3, 0.4, 0]).pow (-1)) [0, 1.2, 1.6, 0, 0, 0, 0, 0] 1e-15
  -- quaternion log/sqrt of a positive real quaternion (Julia NaN)
  t := expect t "log(Q(2,0,0,0))" (toMultivector (sp E3 [2.0, 0, 0, 0]).log) [F64.log 2.0, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "sqrt(Q(4,0,0,0))" (toMultivector (sp E3 [4.0, 0, 0, 0]).sqrt) [2.0, 0, 0, 0, 0, 0, 0, 0]
  return t

/-! ## Identities -/

/-- Inverse pairs and algebraic identities on assorted elements. -/
def identities (t : Tally) : Tally := Id.run do
  let mut t := t
  -- exp ∘ log on couples (closed forms, both signs of B²)
  for z in [(⟨3, 1.0, 2.0⟩ : Couple E3 Float), ⟨1, 1.0, 0.5⟩, ⟨7, -0.3, 0.8⟩, ⟨3, 0.2, -1.5⟩] do
    t := expectM t s!"exp(log {z.re}+{z.im}B)" z.log.exp.toMultivector z.toMultivector 1e-14
    t := expectM t s!"sqrt²" (z.sqrt.pow 2).toMultivector z.toMultivector 1e-14
    t := expectM t s!"log1p = log(1+z)" z.log1p.toMultivector (Couple.log ⟨z.bits, 1 + z.re, z.im⟩).toMultivector 1e-14
  -- exp ∘ log on quaternions and spinors
  let q := sp E3 [0.3, -0.7, 0.2, 0.5]
  t := expectM t "exp(log q) (polar)" (toMultivector q.log.exp) (toMultivector q) 1e-14
  t := expectM t "sqrt(q)²" (toMultivector (q.sqrt.pow 2)) (toMultivector q) 1e-14
  t := expect t "q·inv(q)" (toMultivector (Half.smul' q q.invD)) [1, 0, 0, 0, 0, 0, 0, 0] 1e-15 1e-15
  let s4 := sp E4 [1.0, 0.1, -0.2, 0.0, 0.05, 0.0, 0.0, 0.0]
  t := expectM t "E4 exp(log s) (qlog series)" (toMultivector s4.log.exp) (toMultivector s4) 1e-7
  -- trigonometric identities of vectors in ℝ3 (true trig: I⟑v squares to -|v|²)
  let v : Single E3 1 Float := ⟨2, 0.7⟩
  let (c, s) := (v.cos.val, v.sin.val)
  t := t.check (near #[c * c + s * s] #[1.0] 1e-9) fun _ => s!"sin² + cos² = {c * c + s * s}"
  t := expectF t "cos(0.7v2)" c (Float.cos 0.7) 1e-9
  -- cosh² - sinh² for a hyperbolic couple (series)
  let h : Couple E3 Float := ⟨1, 0.4, 0.3⟩
  let (ch', sh') := (h.cosh, h.sinh)
  t := expect t "cosh² - sinh²" ((ch'.pow 2).toMultivector - (sh'.pow 2).toMultivector) [1, 0, 0, 0, 0, 0, 0, 0] 1e-9 1e-9
  -- multivector powers are repeated products
  let m := mv E3 [0.5, 0.1, 0.2, 0.3, 0.3, 0.2, 0.4, 0.2]
  t := expect t "m^3 = m*m*m" (m.pow 3) (m * m * m).v.toList 1e-15
  let bv := mv E3 [1.0, 0, 0, 0, 0, 0, 0, 0.5]
  t := expect t "(1+0.5I)^-2 = inv²" (bv.pow (-2)) (bv.invD * bv.invD).v.toList 1e-15
  t := expect t "q^-2 = inv(q)²" (toMultivector (q.pow (-2))) (toMultivector (Half.smul' q.invD q.invD)).v.toList 1e-15
  -- exp = 1 + expm1 on the series path
  t := expect t "exp = 1 + expm1" m.exp (Multivector.addScalar 1.0 m.expm1).v.toList 1e-15
  -- sin/cos of a chain against the multivector route
  let b := ch E3 2 [0.3, 0.2, 0.4]
  t := expect t "cos(b) = Multivector cos" (toMultivector b.cos) (toMultivector b).cos.v.toList seriesTol
  t := expect t "sin(b) = Multivector sin" (toMultivector b.sin) (toMultivector b).sin.v.toList 1e-12
  -- spinor trig (odd I) against the multivector route
  t := expect t "cos(q) = Multivector cos" (toMultivector q.cos) (toMultivector q).cos.v.toList 1e-12
  t := expect t "sin(q) = Multivector sin" (toMultivector q.sin) (toMultivector q).sin.v.toList 1e-12
  -- the spinor TensorRing of ℝ4 agrees with the multivector one
  t := expect t "E4 Generic.cos spinor" (toMultivector (Generic.cos s4)) (toMultivector s4).cos.v.toList 1e-12
  t := expect t "E4 Half.cos spinor" (toMultivector s4.cos) (toMultivector s4).cos.v.toList 1e-12
  t := expect t "E4 Generic.tanh spinor" (toMultivector (Generic.tanh s4)) (toMultivector s4).tanh.v.toList 1e-12
  -- Julia's log(b, t) = log(t)/log(b) (bug B1 fixed)
  let l := (Multivector.addScalar 1.0 (toMultivector (⟨3, 0.5⟩ : Single E3 2 Float)))
  t := expect t "logBase 2 = log2" (l.logBase 2.0) l.log2.v.toList 1e-15
  -- log_fast / logh_fast (Julia values: port-notes §4.3.3)
  let r := Couple.exp (⟨3, 0.0, 0.5⟩ : Couple E3 Float)
  match r.logFast, r.loghFast with
  | some a, some b =>
    t := expect t "log_fast(exp(0.5v12))" a.toMultivector [-1.3515494402519288e-16, 0, 0, 0, 0.5, 0, 0, 0] 1e-13 1e-15
    t := expect t "logh_fast(exp(0.5v12))" b.toMultivector [-1.11102447327775e-17, 0, 0, 0, 0.5, 0, 0, 0] 1e-13 1e-15
  | _, _ => t := t.check false fun _ => "log_fast(exp(0.5v12)) did not converge"
  let mm := mv E3 [0.1, 0, 0, 0, 0.2, 0, 0.1, 0]
  match mm.exp.logFast with
  | some a => t := expectM t "log_fast(exp(m))" a mm 1e-12 1e-15
  | none => t := t.check false fun _ => "log_fast(exp(m)) did not converge"
  t := t.check ((⟨1, -0.034, -0.454⟩ : Couple E3 Float).logFast.isNone) fun _ =>
    "log_fast of a couple outside the light cone must fail (Julia hangs)"
  match q.logFast with
  | some a => t := expectM t "log_fast(q) = log(q)" (toMultivector a) (toMultivector q.log) 1e-12
  | none => t := t.check false fun _ => "log_fast(q) did not converge"
  -- spinor inverse hyperbolic functions and real powers
  t := expectM t "sinh(asinh(q))" (toMultivector q.asinh.sinh) (toMultivector q) 1e-7
  t := expectM t "tanh(atanh(q/2))" (toMultivector (Half.sdiv q 2.0).atanh.tanh) (toMultivector (Half.sdiv q 2.0)) 1e-7
  t := expectM t "(q^0.5)^2 = q" (toMultivector ((q.powf 0.5).pow 2)) (toMultivector q) 1e-13
  t := expectM t "q^0.5 = sqrt(q)" (toMultivector (q.powf 0.5)) (toMultivector q.sqrt) 1e-13
  t := expectM t "Couple exp2 = 2^z" (Couple.exp2 (⟨3, 0.3, 0.7⟩ : Couple E3 Float)).toMultivector
    (Couple.rpow 2.0 (⟨3, 0.3, 0.7⟩ : Couple E3 Float)).toMultivector 1e-15
  -- phasor round trips
  let z : Couple E3 Float := ⟨3, 1.2, -0.7⟩
  t := expectM t "complexify(polarize z)" z.polarize.complexify.toMultivector z.toMultivector 1e-15
  return t

/-- `^` on every kind (`Grassmann.Composite.Pow`): the notation reaches the kind's `pow`,
`powf` and `rpow` (bit for bit), and Julia's values of `v12^2 = -1`, `v12^-1 = -v12`,
`(v1+v2)^3 = 2v1 + 2v2`, `(v1+v2+v3)^4 = 9`, `q^-1 = inv(q)`, `2^v12 = cos(log 2) + sin(log 2)v12`. -/
def powers (t : Tally) : Tally := Id.run do
  let mut t := t
  let b : Single E3 2 Float := ⟨3, 1.0⟩
  let c : Chain E3 1 Float := ch E3 1 [1, 1, 0]
  let q : Half E3 false Float := sp E3 [0.3, 0.5, -0.2, 0.7]
  let m : Multivector E3 Float := mv E3 [0.2, 0.1, -0.3, 0.4, 0.5, -0.1, 0.2, 0.3]
  let z : Couple E3 Float := ⟨3, 1.2, -0.7⟩
  let ph : Phasor E3 Float := z.polarize
  let same' := fun {V : TensorBundle} (a b : Multivector V Float) => (a.v.toArray.zip b.v.toArray).all fun (x, y) => same x y
  t := t.check (same' (b ^ 2 : Couple E3 Float).toMultivector (b.pow 2).toMultivector) fun _ => "v12 ^ 2"
  t := t.check (same' (b ^ (-1 : Int) : Couple E3 Float).toMultivector (b.pow (-1)).toMultivector) fun _ => "v12 ^ -1"
  t := t.check (same' (c ^ 3 : Multivector E3 Float) (c.pow 3)) fun _ => "(v1+v2) ^ 3"
  t := t.check (same' (Half.toMultivector (q ^ 5)) (Half.toMultivector (q.pow 5))) fun _ => "q ^ 5"
  t := t.check (same' (Half.toMultivector (q ^ (0.5 : Float))) (Half.toMultivector (q.powf 0.5))) fun _ => "q ^ 0.5"
  t := t.check (same' (m ^ 9) (m.pow 9)) fun _ => "m ^ 9"
  t := t.check (same' (m ^ (-2 : Int)) (m.pow (-2))) fun _ => "m ^ -2"
  t := t.check (same' (m ^ (0.5 : Float)) (m.powf 0.5)) fun _ => "m ^ 0.5"
  t := t.check (same' (z ^ 3).toMultivector (z.pow 3).toMultivector) fun _ => "z ^ 3"
  t := t.check (same' (z ^ (0.25 : Float)).toMultivector (z.powf 0.25).toMultivector) fun _ => "z ^ 0.25"
  t := t.check (same' (ph ^ 3).complexify.toMultivector (ph.pow 3).complexify.toMultivector) fun _ => "phasor ^ 3"
  t := t.check (same' ((2 : Nat) ^ b : Couple E3 Float).toMultivector (Single.rpow 2.0 b).toMultivector) fun _ => "2 ^ v12"
  t := t.check (same' ((2.0 : Float) ^ m) (m.rpow 2.0)) fun _ => "2.0 ^ m"
  t := t.check (same' ((3 : Nat) ^ c : Multivector E3 Float) (Chain.rpow 3.0 c)) fun _ => "3 ^ (v1+v2)"
  -- the unboxed complex power (`BPair.cPow`) is `JuliaBase.powBySquaring` at `Complex Float`
  let zc : Couple E3 Float := ⟨3, 0.9, -0.7⟩
  for k in List.range 41 do
    let w := JuliaBase.powBySquaring (· * ·) (⟨1, 0⟩ : JuliaBase.Complex Float) zc.toComplex k
    let got := zc.pow k
    t := t.check (same got.re w.re && same got.im w.im) fun _ => s!"elliptic couple ^ {k}: {got.re} {got.im} vs {w.re} {w.im}"
  -- Julia's values
  t := expect t "v12^2" (b ^ 2 : Couple E3 Float).toMultivector [-1, 0, 0, 0, 0, 0, 0, 0]
  t := expect t "v12^-1" (b ^ (-1 : Int) : Couple E3 Float).toMultivector [0, 0, 0, 0, -1, 0, 0, 0]
  t := expect t "(v1+v2)^3" (c ^ 3 : Multivector E3 Float) [0, 2, 2, 0, 0, 0, 0, 0]
  t := expect t "(v1+v2+v3)^4" (ch E3 1 [1, 1, 1] ^ 4 : Multivector E3 Float) [9, 0, 0, 0, 0, 0, 0, 0]
  t := expectM t "q^-1 = inv(q)" (Half.toMultivector (q ^ (-1 : Int))) (Half.toMultivector q.invD)
  let l2 := Float.log 2.0
  t := expect t "2^v12" ((2 : Nat) ^ b : Couple E3 Float).toMultivector [Float.cos l2, 0, 0, 0, Float.sin l2, 0, 0, 0] 1e-15
  return t

/-- The closed forms of the one-blade `cosh`/`sinh` against Grassmann's series
(`BPair.cosh`/`BPair.sinh`, Julia's loop and stopping rule): equal to the series' `√eps`
truncation, for every sign and size of `β = B²`. -/
def closedSeries (t : Tally) : Tally := Id.run do
  let mut t := t
  for β in [1.0, -1.0, 0.0, 2.5, -0.3, 4.0] do
    for (a, b) in [(0.5, 0.3), (-1.2, 0.7), (0.0, 1.5), (2.0, -0.4), (0.1, 0.0)] do
      let z : BPair := ⟨a, b⟩
      let c := BPair.coshClosed β z
      let cs := BPair.cosh β z
      let s := BPair.sinhClosed β z
      let ss := BPair.sinh β z
      t := t.check (near #[c.re, c.im] #[cs.re, cs.im] 1e-8 1e-12) fun _ =>
        s!"cosh closed/series β={β} z=({a}, {b}): {c.re}, {c.im} vs {cs.re}, {cs.im}"
      t := t.check (near #[s.re, s.im] #[ss.re, ss.im] 1e-8 1e-12) fun _ =>
        s!"sinh closed/series β={β} z=({a}, {b}): {s.re}, {s.im} vs {ss.re}, {ss.im}"
  return t

/-- The complex-like accessors, `∠`, `hyperplanes`, `𝕚 𝕛 𝕜`, `isdiag` (`Grassmann.Composite.Phasor`)
against Julia's values. -/
def phasorApi (t : Tally) : Tally := Id.run do
  let mut t := t
  let z : Couple E3 Float := ⟨3, 1.0, 2.0⟩
  t := t.check (z.vectorizeChain.v.toList == [1.0, 2.0] && (Forms.restrict E3 z.bits).n == 2) fun _ =>
    s!"vectorize(1+2v12) = {z.vectorizeChain.v.toList}"
  t := t.check (z.reim == (1.0, 2.0)) fun _ => "reim(1+2v12)"
  let p : Phasor E3 Float := (2.0 : Float) ∠ (⟨3, F64.pi / 3⟩ : Single E3 2 Float)
  t := t.check (p.realvalue == 2.0 && same p.imagvalue 1.0471975511965976 && p.amplitude == 2.0 &&
      p.phase == 0.0 && p.unitangle.bits == 3 && p.unitangle.val == 1.0) fun _ =>
    s!"2 ∠ (π/3)v12: {p.realvalue} {p.imagvalue} {p.amplitude} {p.phase}"
  t := t.check (p.vectorizeChain.v.toList == [2.0, F64.pi / 3]) fun _ => "vectorize(2 ∠ (π/3)v12)"
  let pt := p 0.5
  t := t.check (pt.amp == 2.0 && pt.angle.im == F64.pi / 3 * 0.5) fun _ => "z(t)"
  let q := (⟨3, 1.0⟩ : Single E3 2 Float).polarize
  t := t.check (q.amp == 1.0 && q.angle.bits == 3 && q.angle.re == 0.0 && q.angle.im == 1.0) fun _ => "polarize(v12)"
  let q2 := (⟨3, 2.0⟩ : Single E3 2 Float).polarize
  t := t.check (q2.amp == 1.0 && q2.angle.im == 2.0) fun _ => "polarize(2v12) = 1 ∠ 2v12"
  t := expectF t "radius(v1+v2)" (ch E3 1 [1, 1, 0]).radius 1.4142135623730951
  t := expectF t "radius(2v12)" (⟨3, 2.0⟩ : Single E3 2 Float).radius 2.0
  t := expectF t "radius(Multivector(1+2v12))" (toMultivector z).radius 2.23606797749979
  let a := (ch E2 1 [1, 1]).angle
  t := t.check (a.bits == 3 && a.re == 0.0 && same a.im 0.7853981633974483) fun _ => s!"angle(v1+v2) = {a.im}"
  let s2 := sp E2 [1, 2]
  t := t.check (s2.toComplex.re == 1.0 && s2.toComplex.im == 2.0) fun _ => "Complex(1+2v12)"
  t := t.check (s2.toCouple.bits == 3 && s2.toCouple.re == 1.0 && s2.toCouple.im == 2.0) fun _ => "Couple(1+2v12)"
  -- hyperplanes (docs 16, 38) and the quaternion units (docs 37)
  let hs := fun (V : TensorBundle) => (Composite.hyperplanes V).map fun h => (h.bits, h.val)
  t := t.check (hs E3 == [(6, 1.0), (5, -1.0), (3, 1.0)]) fun _ => s!"hyperplanes(ℝ^3) = {hs E3}"
  t := t.check (hs E2 == [(2, -1.0), (1, 1.0)]) fun _ => s!"hyperplanes(ℝ^2) = {hs E2}"
  t := t.check (hs E4 == [(14, -1.0), (13, 1.0), (11, -1.0), (7, 1.0)]) fun _ => s!"hyperplanes(ℝ^4) = {hs E4}"
  t := t.check ((Composite.hyperplanes ℝ3).map (fun h => (h.bits, h.val)) == [(𝕚.bits, 𝕚.val), (𝕛.bits, 𝕛.val), (𝕜.bits, 𝕜.val)])
    fun _ => "𝕚, 𝕛, 𝕜 = hyperplanes(ℝ3)"
  let m := fun (x y : Single ℝ3 2 Float) => (toMultivector x * toMultivector y : Multivector ℝ3 Float).v.toList
  t := t.check (m 𝕚 𝕛 == [0, 0, 0, 0, -1, 0, 0, 0] && m 𝕛 𝕜 == [0, 0, 0, 0, 0, 0, -1, 0] &&
      m 𝕜 𝕚 == [0, 0, 0, 0, 0, 1, 0, 0]) fun _ => s!"𝕚𝕛, 𝕛𝕜, 𝕜𝕚 = {m 𝕚 𝕛} {m 𝕛 𝕜} {m 𝕜 𝕚}"
  -- isdiag
  let D : Endomorphism E3 (.chain 1) Float := TensorOperator.ofFn fun i j => if i.1 = j.1 then 2.0 else 0.0
  let N : Endomorphism E3 (.chain 1) Float := TensorOperator.ofFn fun i j => if i.1 ≤ j.1 then 1.0 else 0.0
  t := t.check (D.isdiag && !N.isdiag) fun _ => "isdiag"
  return t

/-- The derived functions on every kind (`Grassmann.Composite.Kinds`): Julia's values where
Julia computes them (`cot(0.5v₁₂) = -2.16395v₁₂`, `sech(0.3v₁ + 0.4v₂) = 0.886819`), and the
reciprocal identities on the kinds where Julia throws. -/
def kindsTests (t : Tally) : Tally := Id.run do
  let mut t := t
  t := expect t "cot(0.5v12)" ((⟨3, 0.5⟩ : Single E3 2 Float).cot) [0, 0, 0, 0, -2.1639534137885525, 0, 0, 0] seriesTol
  t := expect t "sech(0.3v1+0.4v2)" ((ch E3 1 [0.3, 0.4, 0]).sech) [0.8868188839704753, 0, 0, 0, 0, 0, 0, 0] seriesTol
  let z : Couple E3 Float := ⟨3, 1.0, 0.5⟩
  let one : Multivector E3 Float := mv E3 [1, 0, 0, 0, 0, 0, 0, 0]
  t := expectM t "cot(z)·tan(z) = 1" (z.cot * toMultivector z.tan) one 1e-9
  t := expectM t "sec(z)·cos(z) = 1" (z.sec * z.cos) one 1e-9
  let q : Half E3 false Float := sp E3 [0.5, 0.3, 0, 0]
  t := expectM t "tanh(atanh(q))" (Multivector.tanh (Half.atanh q |> Half.toMultivector)) (Half.toMultivector q) 1e-7
  let p : Phasor E3 Float := z.polarize
  t := expectM t "sin(phasor) = sin(complexify)" p.sin z.sin 1e-12
  -- Julia `exph(1.0 + 0.5v₁)` (`exph` of a spinor or multivector is an `UndefVarError` there)
  t := expect t "exph(1+0.5v1)" (Couple.exph (⟨1, 1.0, 0.5⟩ : Couple E3 Float)).toMultivector
    [3.065205170334457, 1.4164838996343287, 0, 0, 0, 0, 0, 0] seriesTol
  t := expectM t "exph(q) = exp(q) for q spinor" (Half.toMultivector (Half.exph q)) (Half.toMultivector (Half.exp q)) 1e-9
  let w : PseudoCouple E3 Float := ⟨0, 1.0, 0.5⟩
  t := expectM t "sqrt(pseudo)²" (w.sqrt * w.sqrt) (toMultivector w) 1e-7
  return t

/-- Run the unit tests; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  let t := kindsTests (phasorApi (closedSeries (powers (identities (fixes (atanh2Tests (spaces (e3 {}))))))))
  IO.println s!"[composite/unit] pass={t.pass} fail={t.fail}"
  for m in t.msgs do IO.eprintln s!"[composite/unit]   FAIL {m}"
  return (t.pass, t.fail)

end Tests.Composite.Unit
