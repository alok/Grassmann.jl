import MeshTopology
import Tests.AbstractLattices.Harness

/-!
Shared helpers for the MeshTopology golden tests (`oracle/golden/meshtopology/*.json`, written
by `oracle/meshtopology/gen.jl`).

Every golden value is either the value computed by the (fixed) Julia package, or
`{"fixed": v, "julia": u}` when upstream differs (a documented defect, `u` possibly
`{"error": …}`), or `{"error": …}` when both throw. The Lean port must equal the fixed value;
both-error cases are skipped. Lean values are encoded with the generator's conventions
(`common.jl`) and compared as compressed JSON (object keys sorted on both sides).
-/

open Lean MeshTopology Tests.Small

namespace Tests.MeshTopology

/-- The value the port must reproduce (`fixed` when upstream differs). -/
def expected (j : Json) : Json :=
  match j.getObjVal? "fixed" with
  | .ok v => v
  | .error _ => j

/-- `true` when the (expected) golden value records a Julia exception. -/
def isError (j : Json) : Bool := (j.getObjVal? "error").isOk

/-- Compare a Lean value (already encoded) with a golden entry. Skips both-error goldens. -/
def checkJ (label : String) (got : Json) (golden : Json) : TestM Unit := do
  let e := expected golden
  if isError e then return
  let (g, x) := (got.compress, e.compress)
  check label (g == x) fun _ =>
    s!"\n    got      {g.take 400}\n    expected {x.take 400}"

/-- Like `checkJ` for a Lean computation that may be undefined (`none` must match a
Julia error). -/
def checkOptJ (label : String) (got : Option Json) (golden : Json) : TestM Unit := do
  let e := expected golden
  match got with
  | some g => checkJ label g golden
  | none => check label (isError e) fun _ => s!"Lean has no value, expected {e.compress.take 300}"

/-- Naturals of a golden array. -/
def natsOf (j : Json) : TestM (Array Nat) := jNats j

/-- Integers of a golden array. -/
def intsOf (j : Json) : TestM (Array Int) := do (← jArr j).mapM jInt

/-! ## Encoders (common.jl conventions) -/

/-- Integer. -/
def jint (i : Int) : Json := toJson i
/-- Natural. -/
def jnat (n : Nat) : Json := toJson n
/-- Array of naturals. -/
def jnats (a : Array Nat) : Json := toJson a
/-- Array of integers. -/
def jints (a : Array Int) : Json := toJson a
/-- A static vector of integers. -/
def jvec {n : Nat} (v : Vector Int n) : Json := toJson v.toArray
/-- A static vector of naturals. -/
def jvecN {n : Nat} (v : Vector Nat n) : Json := toJson v.toArray
/-- A list of `Values`. -/
def jvecs {n : Nat} (vs : Array (Vector Int n)) : Json := Json.arr (vs.map jvec)
/-- A list of `Values` of naturals. -/
def jvecsN {n : Nat} (vs : Array (Vector Nat n)) : Json := Json.arr (vs.map jvecN)
/-- An N-D grid `{dims, colmajor}`. -/
def jgrid (dims : List Nat) (entries : Array Json) : Json :=
  Json.mkObj [("dims", toJson dims.toArray), ("colmajor", Json.arr entries)]
/-- A pair `a => b`. -/
def jpair (a b : Nat) : Json := Json.arr #[jnat a, jnat b]
/-- A Bool. -/
def jbool (b : Bool) : Json := toJson b
/-- A string. -/
def jstr (s : String) : Json := toJson s

/-- One axis of a product topology (`axj`). -/
def jaxis : AxisMap → Json
  | .oneTo n => Json.mkObj [("kind", "OneTo"), ("n", jnat n)]
  | .unitRange a b => Json.mkObj [("kind", "UnitRange"), ("start", jint a), ("stop", jint b)]
  | .stepRange a s b =>
    Json.mkObj [("kind", "StepRange"), ("start", jint a), ("step", jint s), ("stop", jint b)]
  | .cross n => Json.mkObj [("kind", "CrossRange"), ("n", jnat n)]
  | .vec v => Json.mkObj [("kind", "Vector"), ("vals", jints v)]

/-- A product topology (`ptj`). -/
def jproduct {N : Nat} (p : ProductTopology N) : Json := Json.arr (p.axes.toArray.map jaxis)

/-- A quotient topology as Julia tables (`qtj`). -/
def jquotient {N : Nat} (m : QuotientTopology N) : Json :=
  let (p, q, r) := m.toTable
  Json.mkObj [("p", jnats p),
    ("q", Json.arr (q.map fun x => if N ≤ 1 then Json.null else jproduct x)),
    ("r", jnats r), ("s", jvecN m.size),
    ("c", Json.arr (m.collapse.toArray.map fun b => jnat (if b then 1 else 0)))]

/-- A (quotient) topology of runtime dimension. -/
structure SomeQuotient where
  /-- Dimension. -/
  N : Nat
  /-- The topology. -/
  m : QuotientTopology N

/-- A vector from an array of the right length. -/
def vecOf {α : Type} (a : Array α) (n : Nat) : TestM (Vector α n) :=
  if h : a.size = n then return ⟨a, h⟩ else throw <| IO.userError s!"expected {n} entries"

/-- Build a named Julia topology (`Torus`, `Mobius`, …) of the given sizes. -/
def namedTopology (fam : String) (s : Array Nat) : TestM SomeQuotient := do
  let n := s.size
  let v ← vecOf s n
  let generic : Option SomeQuotient := match fam with
    | "Open" => some ⟨n, .openTop v⟩
    | "Mirror" => some ⟨n, .mirror v⟩
    | "Clamped" => some ⟨n, .clamped v⟩
    | "Torus" => some ⟨n, .torus v⟩
    | "Ball" | "Polar" => some ⟨n, .ball v⟩
    | "Sphere" => some ⟨n, .sphere v⟩
    | _ => none
  if let some q := generic then return q
  if h : s.size = 2 then
    let v2 : Vector Nat 2 := ⟨s, h⟩
    match fam with
    | "Cylinder" => return ⟨2, .cylinder v2⟩
    | "Mobius" => return ⟨2, .mobius v2⟩
    | "Wing" => return ⟨2, .wing v2⟩
    | "Hopf" => return ⟨2, .hopf2 v2⟩
    | "Klein" => return ⟨2, .klein v2⟩
    | "Cone" => return ⟨2, .cone v2⟩
    | "Tube" | "Revolved" => return ⟨2, .tube2 v2⟩
    | "Geographic" => return ⟨2, .geographic v2⟩
    | _ => pure ()
  if h : s.size = 3 then
    let v3 : Vector Nat 3 := ⟨s, h⟩
    match fam with
    | "Hopf" => return ⟨3, .hopf3 v3⟩
    | "Tube" => return ⟨3, .tube3 v3⟩
    | _ => pure ()
  throw <| IO.userError s!"unknown topology {fam}{s}"

/-- Parse a golden case name `Fam(a, b, …)` into the family and sizes. -/
def parseName (name : String) : Option (String × Array Nat) := do
  let parts := name.splitOn "("
  let fam ← parts[0]?
  let rest ← parts[1]?
  let inner := (rest.splitOn ")")[0]!
  let sizes ← (inner.splitOn ",").mapM fun t => t.trimAscii.toString.toNat?
  return (fam, sizes.toArray)

end Tests.MeshTopology
