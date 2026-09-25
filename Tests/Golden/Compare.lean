import Tests.Golden.Registry

/-!
# Comparators (docs/port-notes/oracle-schema.md §11)

* **Kind** (rule 2): the result's kind tag, and `grade`/`bits`/`T` where the golden has
  them. Not for composite, not against `ref`.
* **Values** (rule 3): exact for `Int64`/`Rational`/`Bool`; bitwise for `Float64` (every
  NaN equal, the sign of zero kept), or the registration's documented tolerance; composite
  uses the shard's `‖out − expect‖₂ ≤ atol + rtol·max(‖out‖₂, ‖expect‖₂)`. A Number
  compares its `value`, an element its `dense`.
* **Strings** (rule 4): `str` and `compact_str` exactly.

Each comparison yields `none` (agreement) or the reasons for disagreement.
-/

namespace Tests.Golden

/-- The expected value of a case after the defect policy (schema §10, §11). -/
inductive Expect where
  /-- Compare with Julia's output. -/
  | out (e : GoldenElem)
  /-- Compare values only with the independent reference (policy `ref`). -/
  | ref (v : Coeffs)
  deriving Inhabited

/-- The coefficient vector an element carries (`dense`, or a Number's `value`). -/
def GoldenElem.values? (e : GoldenElem) : Option Coeffs :=
  match e.dense with
  | some d => some d
  | none => e.value

/-- A one-coefficient vector `s` as the dense vector of `s·One` of length `N`. -/
def embedScalar (w : Coeffs) (N : Nat) : Coeffs :=
  let fz := FloatArray.mk (Array.replicate N 0)
  match w with
  | .exact v => .exact ((Array.replicate N 0).set! 0 (v[0]?.getD 0))
  | .float v => .float (fz.set! 0 (v[0]?.getD 0))
  | .complexExact re im =>
    .complexExact ((Array.replicate N 0).set! 0 (re[0]?.getD 0)) ((Array.replicate N 0).set! 0 (im[0]?.getD 0))
  | .complexFloat re im => .complexFloat (fz.set! 0 (re[0]?.getD 0)) (fz.set! 0 (im[0]?.getD 0))
  | .raw v => .raw ((Array.replicate N (Lean.Json.str "0")).set! 0 (v[0]?.getD .null))

/-- Compare an evaluator result with Julia's output element. `mode` is the value
comparison; `composite` disables kind and string checks (they are informational there). -/
def compareWithOut (asp : Aspects) (mode : ValueMode) (composite : Bool) (got want : GoldenElem) :
    Array String := Id.run do
  let mut why : Array String := #[]
  if want.kind == .error then
    return #["Julia rejects the operation"]
  if got.kind == .error then
    return #[s!"port rejects ({got.msg.getD ""}) but Julia returns {want.kind}"]
  if asp.kind && !composite then
    if got.kind != want.kind then why := why.push s!"kind {got.kind} vs {want.kind}"
    if got.grade != want.grade && (got.grade.isSome || want.grade.isSome) then
      why := why.push s!"grade {got.grade} vs {want.grade}"
    if got.bits != want.bits && (got.bits.isSome || want.bits.isSome) then
      why := why.push s!"bits {got.bits} vs {want.bits}"
    if got.V != want.V then why := why.push s!"V {got.V} vs {want.V}"
  if asp.values then
    if let (some gT, some wT) := (got.T, want.T) then
      if gT != wT && !composite then why := why.push s!"T {gT.name} vs {wT.name}"
    match got.values?, want.values? with
    | some g, some w =>
      -- a plain-number result is that number times One (schema §8.2)
      let w := if want.dense.isNone && w.size == 1 && g.size != 1 then embedScalar w g.size else w
      if let some r := compareCoeffs mode g w then why := why.push s!"values: {r}"
    | some _, none => why := why.push "values: Julia's result has none"
    | none, _ => pure ()
  if asp.str && !composite then
    if let .val s := got.str then
      match want.str with
      | .val t => if s != t then why := why.push s!"str `{s}` vs `{t}`"
      | _ => why := why.push s!"str `{s}` vs none"
  if asp.compact && !composite then
    if let .val s := got.compactStr then
      match want.compactStr with
      | .val t => if s != t then why := why.push s!"compact_str `{s}` vs `{t}`"
      | .absent => pure ()  -- only construct/docs outputs carry compact_str
      | .null => why := why.push s!"compact_str `{s}` vs null"
  return why

/-- Compare an evaluator result's values with a `ref` vector (policy `ref`: kind and
strings are not checked, Julia's are wrong). -/
def compareWithRef (mode : ValueMode) (got : GoldenElem) (ref : Coeffs) : Array String :=
  if got.kind == .error then #[s!"port rejects ({got.msg.getD ""}); the reference has a value"]
  else match got.values? with
    | some g => match compareCoeffs mode g ref with
      | some r => #[s!"values vs ref: {r}"]
      | none => #[]
    | none => #["result has no values to compare with ref"]

/-- Compare against an expectation. -/
def compareExpect (asp : Aspects) (mode : ValueMode) (composite : Bool) (got : GoldenElem) :
    Expect → Array String
  | .out e => compareWithOut asp mode composite got e
  | .ref v => compareWithRef mode got v

end Tests.Golden
