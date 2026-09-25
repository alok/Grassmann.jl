import Tests.Golden.Registry
import Tests.Golden.Space
import Grassmann.Composite

/-!
# The composite statements of the docs suite (`oracle/golden/docs/*.json`)

The docs suite (docs/port-notes/oracle-schema.md §8.8) evaluates README/documentation
statements REPL-style in a Julia sandbox; its evaluators see only the statement text. This
module evaluates the statements whose value is a composite function (`exp`, `log`, `sqrt`,
`inv`, `^`, `complexify`, `vectorize`, …) or a rotation built from one (`~R*a*R`,
`R >>> v₁`), keyed by the shard and the statement (and the case index where the statement
depends on an earlier assignment, e.g. `R = exp(π/8*v12)` then `R>>>v1`). The space is the
output's `V` display (`Tests.ElementOracle.parseHandle?`). Values are compared
componentwise (`rtol = 1e-12`, `atol = 1e-14`: products of closed forms round differently
from Julia's unrolled kernels in the last bit); kinds and strings are not compared.

Not evaluated: `inv(2+v1)` in `45-norms-metrics` (Julia's elliptic formula for a hyperbolic
couple, the defect `couple-inv-hyperbolic` that `defects.json` tags only in the composite
suite; integrator request), statements of display-only values (`Phasor`, functions,
tuples) and the non-composite statements.
-/

namespace Tests.ElementOracle.CompositeDocs

open Tests.ElementOracle Grassmann DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

/-- A docs statement as a function of the space. -/
abbrev DocFn := (V : TensorBundle) → Multivector V Float

/-- `π`. -/
def π : Float := F64.pi

variable {V : TensorBundle}

/-- The unit blade `e_b` as a multivector. -/
def e (V : TensorBundle) (b : UInt64) : Multivector V Float :=
  ⟨Values.ofFn fun i => if (Leibniz.indexBasisAll V.n)[i.1]! == b then 1.0 else 0.0⟩

/-- The term `v12`. -/
def v12 (V : TensorBundle) : Single V 2 Float := ⟨3, 1.0⟩

/-- `c·e_b` as a multivector. -/
def ce (V : TensorBundle) (c : Float) (b : UInt64) : Multivector V Float :=
  ⟨Values.ofFn fun i => if (Leibniz.indexBasisAll V.n)[i.1]! == b then c else 0.0⟩

/-- A chain from its coefficients. -/
def ch (V : TensorBundle) (G : Nat) (xs : List Float) : Chain V G Float := (Chain.ofList? xs).get!

variable [Kernels V]

/-- `exp(c·e_b)` of a bivector term as a multivector. -/
def expB (V : TensorBundle) [Kernels V] (b : UInt64) (c : Float) : Multivector V Float :=
  (Single.exp (⟨b, c⟩ : Single V 2 Float)).toMultivector

/-- Julia `~R*a*R`. -/
def rot (R a : Multivector V Float) : Multivector V Float := R.reverse * a * R

/-- The statements, by shard and input (independent of earlier assignments). -/
def byInput : List (String × String × DocFn) := [
  ("09-algebra.md-436", "complexify(Chain(1,2))", fun V => (Chain.complexify (ch V 1 [1, 2])).toMultivector),
  ("09-algebra.md-436", "vectorize(Couple(1,2))", fun V =>
    let w := (Couple.vectorize (⟨lowMask V.n, 1.0, 2.0⟩ : Couple V Float))
    toMultivector ((Chain.ofList? w.toList : Option (Chain V 1 Float)).getD Chain.zero)),
  ("23-algebra.md-1175", "exp(π/4*v12)*v1*~exp(π/4*v12)", fun V =>
    let R := expB V 3 (π / 4)
    R * e V 1 * R.reverse),
  ("23-algebra.md-1175", "~exp(π/4*v12)*v1*exp(π/4*v12)", fun V => rot (expB V 3 (π / 4)) (e V 1)),
  ("28-algebra.md-1436-Int-field-variant", "inv(3*v1)", fun V =>
    toMultivector (Single.inv (⟨1, 3.0⟩ : Single V 1 Float))),
  ("30-quick-start.md-5", "R = exp(π/4*v12)", fun V => expB V 3 (π / 4)),
  ("30-quick-start.md-5", "~R*v1*R", fun V => rot (expB V 3 (π / 4)) (e V 1)),
  ("31-algebra-of-space.md-7", "R = exp(θ*v23)", fun V => expB V 6 (π / 4)),
  ("31-algebra-of-space.md-7", "inv(n)*a*n", fun V =>
    toMultivector (Single.inv (⟨1, 3.0⟩ : Single V 1 Float)) * (e V 1 + e V 2 + e V 4) * ce V 3.0 1),
  ("31-algebra-of-space.md-7", "n\\a*n", fun V =>
    toMultivector (Single.inv (⟨1, 3.0⟩ : Single V 1 Float)) * (e V 1 + e V 2 + e V 4) * ce V 3.0 1),
  ("31-algebra-of-space.md-7", "R = exp(π/4*v12)", fun V => expB V 3 (π / 4)),
  ("31-algebra-of-space.md-7", "~R*v1*R", fun V => rot (expB V 3 (π / 4)) (e V 1)),
  ("31-algebra-of-space.md-7", "R = R12(π/2)", fun V => expB V 3 (π / 2 / 2)),
  ("31-algebra-of-space.md-7", "~R*a*R", fun V => rot (expB V 3 (π / 2 / 2)) (e V 1 + e V 2 + e V 4)),
  ("31-algebra-of-space.md-7", "Rxy = R_B(π/4*v12)", fun V => expB V 3 (π / 4 / 2)),
  ("31-algebra-of-space.md-7", "Ryz = R_B(π/5*v23)", fun V => expB V 6 (π / 5 / 2)),
  ("31-algebra-of-space.md-7", "R_B(π/6*(v23+v12))", fun V => (ch V 2 [π / 6 / 2, 0, π / 6 / 2]).exp),
  ("31-algebra-of-space.md-7", "R(a)", fun V =>
    rot (ch V 2 [π / 6 / 2, 0, π / 6 / 2]).exp (e V 1 + e V 2 + e V 4)),
  ("31-algebra-of-space.md-7", "Rxy(Ryz(Rxz(a)))", fun V =>
    let r := fun (b : UInt64) => expB V b (π / 3 / 2)
    rot (r 3) (rot (r 6) (rot (r 5) (e V 1 + e V 2 + e V 4)))),
  ("31-algebra-of-space.md-7", "R(v1)", fun V =>
    let R := expB V 6 (π / 2 / 2) * expB V 3 (π / 2 / 2) *
      (Single.exp (⟨1, 1.0 / 2.0⟩ : Single V 1 Float)).toMultivector
    rot R (e V 1)),
  ("37-display-edge-cases", "exp(v12)", fun V => expB V 3 1.0),
  ("37-display-edge-cases", "exp(2v12+v13)", fun V => (ch V 2 [2, 1, 0]).exp),
  ("37-display-edge-cases", "log(exp(0.5v12))", fun V =>
    (Single.exp (⟨3, 0.5⟩ : Single V 2 Float)).log.toMultivector),
  ("37-display-edge-cases", "sqrt(4+v12)", fun V => (Couple.sqrt (⟨3, 4.0, 1.0⟩ : Couple V Float)).toMultivector),
  ("37-display-edge-cases", "R = exp(π/4*𝕜)", fun V => expB V 3 (π / 4)),
  ("37-display-edge-cases", "R = exp(π/8*v12)", fun V => expB V 3 (π / 8)),
  ("43-orb", "t = exp((π/4)*(v12+v∞3))", fun V => (ch V 2 [0, 0, π / 4, π / 4, 0, 0]).exp),
  ("45-norms-metrics", "inv(a)", fun V => toMultivector (Chain.inv (ch V 1 [1, 2, 3]))),
  ("45-norms-metrics", "a/a", fun V => toMultivector (ch V 1 [1, 2, 3]) * toMultivector (Chain.inv (ch V 1 [1, 2, 3]))),
  ("45-norms-metrics", "inv(1+v12)", fun V => (Couple.inv (⟨3, 1.0, 1.0⟩ : Couple V Float)).toMultivector),
  ("45-norms-metrics", "abs(1+v12)", fun V => Multivector.scalar (Float.sqrt (Couple.abs2 (⟨3, 1.0, 1.0⟩ : Couple V Float)))),
  ("52-exp-special-cases", "exp(0.5v1)", fun V => (Single.exp (⟨1, 0.5⟩ : Single V 1 Float)).toMultivector),
  ("52-exp-special-cases", "exp(0.5v12)", fun V => expB V 3 0.5),
  ("52-exp-special-cases", "exp(0.5v∞1)", fun V => expB V 5 0.5),
  ("52-exp-special-cases", "exp(0.5v∞∅)", fun V => expB V 3 0.5),
  ("54-sandwich-scaling", "inv(3v1)*v2*(3v1)", fun V =>
    toMultivector (Single.inv (⟨1, 3.0⟩ : Single V 1 Float)) * e V 2 * ce V 3.0 1),
  ("54-sandwich-scaling", "exp(π/8*v12)", fun V => expB V 3 (π / 8)),
  ("54-sandwich-scaling", "exp(π/8*v12)^2", fun V =>
    (Single.exp (⟨3, π / 8⟩ : Single V 2 Float) ^ 2 : Couple V Float).toMultivector),
  ("54-sandwich-scaling", "2^v12", fun V => ((2 : Nat) ^ v12 V : Couple V Float).toMultivector),
  ("54-sandwich-scaling", "v12^2", fun V => (v12 V ^ 2 : Couple V Float).toMultivector),
  ("54-sandwich-scaling", "(v1+v2)^3", fun V => ch V 1 [1, 1, 0] ^ 3),
  ("54-sandwich-scaling", "v12^-1", fun V => (v12 V ^ (-1 : Int) : Couple V Float).toMultivector),
  ("58-dims", "complexify(Phasor(2.0, π/3))", fun V =>
    (Phasor.complexify (⟨2.0, ⟨0, π / 3, 0.0⟩⟩ : Phasor V Float)).toMultivector)
]

/-- Statements that depend on an earlier assignment, by shard and case index (the input
is checked too). -/
def byIndex : List (String × Nat × String × DocFn) := [
  ("37-display-edge-cases", 76, "R>>>v1", fun V => expB V 3 (π / 4) >>> (⟨1, 1.0⟩ : Single V 1 Float)),
  ("37-display-edge-cases", 77, "v1⊘R", fun V => toMultivector ((⟨1, 1.0⟩ : Single V 1 Float) ⊘ expB V 3 (π / 4))),
  ("37-display-edge-cases", 80, "R>>>v1", fun V => expB V 3 (π / 8) >>> (⟨1, 1.0⟩ : Single V 1 Float)),
  ("37-display-edge-cases", 81, "v1⊘R", fun V => toMultivector ((⟨1, 1.0⟩ : Single V 1 Float) ⊘ expB V 3 (π / 8))),
  ("37-display-edge-cases", 82, "sandwich(v1,R)", fun V => toMultivector ((⟨1, 1.0⟩ : Single V 1 Float) ⊘ expB V 3 (π / 8))),
  ("37-display-edge-cases", 83, "~R*v1*R", fun V => rot (expB V 3 (π / 8)) (e V 1)),
  ("37-display-edge-cases", 84, "R*v1*~R", fun V => let R := expB V 3 (π / 8); R * e V 1 * R.reverse)
]

end CompositeDocs

open CompositeDocs in
/-- The docs evaluator for the composite statements (module docstring). -/
def compositeDocsEval : Evaluator := fun ctx _ => do
  let c := ctx.case
  let input ← c.input
  let f ← (byIndex.find? fun (s, i, inp, _) => s == ctx.shard && i == c.idx && inp == input).map (·.2.2.2)
    <|> (byInput.find? fun (s, inp, _) => s == ctx.shard && inp == input).map (·.2.2)
  let out ← c.out
  -- the space: the output's `V`, or Julia's default `Phasor` space `Submanifold(2)`
  let V ← match out.V with
    | some v => (parseHandle? v).map (·.1)
    | none => some (DirectSum.TensorBundle.euclidean 2)
  let m := f V
  -- no `T`: some statements are Julia `Int64` values computed here over `Float` (exactly)
  some { kind := .multivector, dense := some (.float m.v.data) }

/-- The composite docs registration. -/
def compositeDocsRegistration : Registration :=
  { name := "grassmann/composite-docs", suite := "docs", op := "docs", eval := compositeDocsEval
    aspects := { kind := false, str := false, compact := false }
    floatTol := some (1e-12, 1e-14) }

initialize register compositeDocsRegistration

end Tests.ElementOracle
