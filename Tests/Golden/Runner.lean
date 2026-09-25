import Tests.Golden.Compare

/-!
# The consumer algorithm (docs/port-notes/oracle-schema.md §11)

For every suite: load the manifest, stream its shards, and for each shard

1. **validate the schema**: file size and manifest entry, top-level keys, `meta`, the space
   descriptor (decoded to a `DirectSum.TensorBundle` and checked against DirectSum's printing
   and tables, `Tests.Golden.Space`), every input and output element (field presence, dense
   length `2ⁿ`, storage support, `native`, the encode/decode round trip), case references,
   flags and `ref`, the committed defect tags (re-derived from `defects.json`) and the
   `stats` recount;
2. **evaluate** every case with the registered evaluators under the defect policy: `skip`
   cases are skipped (counted per defect id), `ref` cases with a `ref` compare values with
   it, untagged Julia errors are counted separately (rule 5), and every other case compares
   with Julia's output (rules 2–4). Ops without an evaluator count as unimplemented.

The report gives, per suite, the schema check counts, pass/fail/unimplemented/skipped
counts, the per-defect and per-evaluator breakdown and the first failures.
-/

namespace Tests.Golden

open Lean

/-- Per-suite results. -/
structure Report where
  /-- Suite name. -/
  suite : String
  /-- Shards processed. -/
  shards : Nat := 0
  /-- Cases processed. -/
  cases : Nat := 0
  /-- Schema checks that held. -/
  checksPass : Nat := 0
  /-- Schema checks that failed. -/
  checksFail : Nat := 0
  /-- Evaluated cases that agree with the golden. -/
  evalPass : Nat := 0
  /-- Evaluated cases that disagree. -/
  evalFail : Nat := 0
  /-- Cases with no evaluator (or whose evaluators returned `none`). -/
  unimplemented : Nat := 0
  /-- Cases skipped by a defect policy (`skip`, or `ref` with a Julia error and no `ref`). -/
  skippedDefect : Nat := 0
  /-- Untagged Julia errors (rule 5): no value to compare. -/
  juliaErrors : Nat := 0
  /-- … of which the port also rejects. -/
  portRejects : Nat := 0
  /-- … of which the port computes a value. -/
  portComputes : Nat := 0
  /-- Cases compared against `ref`. -/
  refCompared : Nat := 0
  /-- Cases without a value to compare (docs statements returning `nothing`). -/
  noValue : Nat := 0
  /-- Defect id ↦ (skipped, compared with ref). -/
  defects : Array (String × Nat × Nat) := #[]
  /-- Evaluator name ↦ (pass, fail). -/
  evaluators : Array (String × Nat × Nat) := #[]
  /-- The first failure messages. -/
  failures : Array String := #[]
  /-- Wall time in milliseconds. -/
  ms : Nat := 0
  deriving Inhabited

namespace Report

/-- Maximum failure messages kept per suite. -/
def maxFailures : Nat := 25

/-- Record a failure message. -/
def note (r : Report) (msg : String) : Report :=
  if r.failures.size < maxFailures then { r with failures := r.failures.push msg } else r

/-- Record one schema check. -/
def check (r : Report) (ok : Bool) (msg : Unit → String) : Report :=
  if ok then { r with checksPass := r.checksPass + 1 }
  else { r.note (msg ()) with checksFail := r.checksFail + 1 }

/-- Bump a keyed pair counter. -/
def bump (xs : Array (String × Nat × Nat)) (k : String) (first : Bool) : Array (String × Nat × Nat) :=
  match xs.findIdx? (·.1 == k) with
  | some i => xs.modify i fun (k, a, b) => if first then (k, a + 1, b) else (k, a, b + 1)
  | none => xs.push (k, if first then 1 else 0, if first then 0 else 1)

/-- Passed checks overall (schema + evaluation). -/
def passed (r : Report) : Nat := r.checksPass + r.evalPass

/-- Failed checks overall. -/
def failed (r : Report) : Nat := r.checksFail + r.evalFail

/-- Print the report. -/
def print (r : Report) : IO Unit := do
  let tag := s!"golden/{r.suite}"
  IO.println s!"  [{tag}] {r.shards} shards, {r.cases} cases, {r.ms} ms: schema {r.checksPass} ok / {r.checksFail} bad; eval pass={r.evalPass} fail={r.evalFail} unimplemented={r.unimplemented} skipped(defect)={r.skippedDefect} julia-errors={r.juliaErrors} (port rejects {r.portRejects}, computes {r.portComputes}) vs-ref={r.refCompared} no-value={r.noValue}"
  for (k, p, f) in r.evaluators do IO.println s!"  [{tag}]   evaluator {k}: {p} pass, {f} fail"
  for (k, s, c) in r.defects.qsort (·.1 < ·.1) do
    IO.println s!"  [{tag}]   defect {k}: {s} skipped, {c} compared with ref"
  for m in r.failures do IO.eprintln s!"  [{tag}]   FAIL {m}"
  if r.failed > r.failures.size then
    IO.eprintln s!"  [{tag}]   … {r.failed - r.failures.size} more failures"

end Report

/-- The `n` of a shard's elements (per-space suites). -/
def shardN (s : Shard) : Option Nat := s.space.map (·.n)

/-- Guess the coefficient type of a `ref` vector from its grammar (its `T` is that of the
promoted operands, which the schema does not record): `Int64`, then `Rational{Int64}`, then
`Float64`, complex when the entries are pairs. -/
def sniffRefType (js : Array Json) : CoeffType :=
  let isPair := js.any fun j => match j with | .arr _ => true | _ => false
  let reals : Array String := js.foldl (fun acc j => match j with
    | .str s => acc.push s
    | .arr #[.str a, .str b] => (acc.push a).push b
    | _ => acc) #[]
  let t : CoeffType :=
    if reals.all (parseInt64? · |>.isSome) then .int64
    else if reals.all (parseRational? · |>.isSome) then .rational
    else .float64
  if isPair then .complex t else t

/-- The match-language view of a case (schema §10). -/
def matchSubject (s : Shard) (c : GoldenCase) : MatchSubject :=
  let out := match c.out with | some o => o.kind.name | none => "Nothing"
  let msg := match c.out with
    | some o => if o.kind == .error then o.msg else none
    | none => none
  let args := #[c.a, c.b].filterMap fun i? => i?.bind fun i => (s.inputs[i]?).map Operand.ofElem
  let (block, input, file) := match s.suite with
    | "construct" => (c.label, c.src, none)
    | "docs" => (c.block, c.input, some (s.sourceStem.getD ""))
    | _ => (none, none, none)
  { suite := s.suite, space := (s.space.map (·.name)).getD "", op := c.op, out, msg, block, input,
    file, args, spaceN := (s.space.map (·.n)).getD 0, spaceGrade := (s.space.map (·.grade)).getD 0,
    conformal := (s.space.map (·.conformal)).getD false, isq := s.space.bind (·.Isq) }

/-- Schema violations of one case (beyond its decode problems). -/
def caseProblems (s : Shard) (defects : DefectTable) (c : GoldenCase) : Array String := Id.run do
  let mut ps := c.problems
  let n := shardN s
  let perSpace := s.suite != "floats" && s.suite != "docs" && s.suite != "construct"
  if perSpace then
    unless s.ops.any (·.1 == c.op) do ps := ps.push s!"op {c.op} not in ops"
    if c.a.isNone then ps := ps.push "no operand a"
    if c.op == "pow" && c.k.isNone then ps := ps.push "pow without k"
  if s.suite == "construct" then
    unless c.label.isSome && c.src.isSome do ps := ps.push "construct case without label/src"
  if s.suite == "docs" then
    unless c.block.isSome && c.input.isSome do ps := ps.push "docs case without block/input"
    if !c.isError && !c.display.isPresent then ps := ps.push "successful statement without display"
  if s.suite != "floats" then
    match c.out with
    | some o =>
      let strict := c.defects.isEmpty
      ps := ps ++ (o.validate n strict).map ("out: " ++ ·)
      if s.suite == "docs" && o.kind.isElement && o.V.isNone then ps := ps.push "docs element without V"
    | none => if s.suite != "docs" then ps := ps.push "case without out"
  unless c.flags.all (· == "ref_mismatch") do ps := ps.push s!"unknown flags {c.flags}"
  if c.ref.isSome != c.isMismatch then ps := ps.push "ref present iff ref_mismatch fails"
  if let some r := c.ref then
    if let some n := n then
      if r.size != 2 ^ n then ps := ps.push s!"ref length {r.size} != 2^{n}"
    if let .error e := Coeffs.decode (sniffRefType r) r then ps := ps.push s!"ref: {e}"
  for id in c.defects do
    if (defects.policy? id).isNone then ps := ps.push s!"unknown defect id {id}"
  -- the committed tags are exactly those the table assigns (floats cases are never tagged)
  let tags := if s.suite == "floats" then #[] else defects.tags (matchSubject s c)
  if tags != c.defects then ps := ps.push s!"defect tags {c.defects} but the table gives {tags}"
  -- floats: the show string round-trips to the exact bits (NaN to some NaN)
  if s.suite == "floats" then
    if let some o := c.out then
      if o.T == some .float64 then
        match o.str?.bind parseJuliaFloat?, o.value.map (·.get 0) with
        | some y, some (Scalar.float x) =>
          unless floatSame x y do ps := ps.push s!"show {o.str?.getD ""} does not round-trip"
        | _, _ => ps := ps.push s!"show {o.str?.getD ""} is not a Julia Float64 literal"
  return ps

/-- Recount a shard's statistics from its cases (schema §9). -/
def recount (s : Shard) : Stats := Id.run do
  let mut st : Stats := { cases := s.cases.size }
  for c in s.cases do
    let err := c.isError
    let mis := c.isMismatch
    if err then st := { st with errors := st.errors + 1 }
    if mis then st := { st with refMismatch := st.refMismatch + 1 }
    if (err || mis) && c.defects.isEmpty then st := { st with unexplained := st.unexplained + 1 }
    for d in c.defects do st := st.addDefect d
  return st.normalize

/-- Validate one shard's schema (everything but the per-case checks). -/
def checkShard (r : Report) (e : ShardEntry) (s : Shard) (bytes : Nat) : Report := Id.run do
  let mut r := r
  r := r.check (bytes == e.bytes && bytes ≤ 4 * 1024 * 1024) fun _ =>
    s!"{e.file}: size {bytes} vs manifest {e.bytes} (limit 4 MiB)"
  let want := shardKeys s.suite
  r := r.check (s.keys.length == want.length && want.all s.keys.contains) fun _ =>
    s!"{e.file}: top-level keys {s.keys}"
  let metaOk := s.metaJ.getObjValD "schema" == (1 : Nat) && s.metaJ.getObjValD "suite" == Json.str s.suite
    && s.name == e.shard
  r := r.check metaOk fun _ => s!"{e.file}: meta {s.metaJ.compress}"
  r := r.check s.problems.isEmpty fun _ => s!"{e.file}: {s.problems.toList.take 3}"
  if let some d := s.space then
    r := r.check (d.name == e.shard && e.space == some d.name) fun _ => s!"{e.file}: space name {d.name}"
    for c in checkSpace d do
      r := r.check c.ok fun _ => s!"{e.file}: space {c.what}: {c.detail}"
  -- the input pool: labels and sources, unique labels, element invariants
  let labels := s.inputs.filterMap (·.label)
  r := r.check (labels.size == s.inputs.size && s.inputs.all (·.src.isSome)) fun _ =>
    s!"{e.file}: inputs without label/src"
  r := r.check ((labels.qsort (· < ·)).toList.eraseDups.length == labels.size) fun _ =>
    s!"{e.file}: duplicate input labels"
  for x in s.inputs do
    let ps := x.validate (shardN s)
    r := r.check ps.isEmpty fun _ => s!"{e.file}: input {x.label.getD "?"}: {ps}"
  -- statistics
  let st := recount s
  r := r.check (st == s.stats.normalize) fun _ => s!"{e.file}: stats {repr s.stats} vs recount {repr st}"
  r := r.check (e.stats.cases == st.cases && e.stats.errors == st.errors
      && e.stats.refMismatch == st.refMismatch && e.stats.unexplained == st.unexplained) fun _ =>
    s!"{e.file}: manifest counts {repr e.stats} vs shard {repr st}"
  return r

/-- The value comparison mode of a case. -/
def valueMode (s : Shard) (reg : Registration) (op : String) : ValueMode :=
  if s.suite == "composite" then
    match s.tol? op with
    | some t => .norm2 t.rtol t.atol
    | none => .norm2 0 0
  else match reg.floatTol with
    | some (rtol, atol) => .componentwise rtol atol
    | none => .exact

/-- Evaluate one case under the defect policy and record the outcome. -/
def evalCase (r : Report) (s : Shard) (defects : DefectTable) (regs : Array Registration)
    (c : GoldenCase) : Report := Id.run do
  let mut r := r
  let policy := defects.strongest c.defects
  if policy == some .skip then
    r := { r with skippedDefect := r.skippedDefect + 1 }
    for id in c.defects do
      if defects.policy? id == some .skip then r := { r with defects := Report.bump r.defects id true }
    return r
  let ctx : EvalCtx := { suite := s.suite, shard := s.name, op := c.op, space := s.space, k := c.k, case := c }
  let result := evaluate regs ctx c.args
  -- policy `ref` with a reference: values only
  if policy == some .ref then
    if let some rj := c.ref then
      r := { r with refCompared := r.refCompared + 1 }
      for id in c.defects do r := { r with defects := Report.bump r.defects id false }
      let some (reg, got) := result | return { r with unimplemented := r.unimplemented + 1 }
      let ref := (Coeffs.decode (sniffRefType rj) rj).toOption.getD (.raw rj)
      let why := compareWithRef (valueMode s reg c.op) got ref
      return record r reg c why
    if c.isError then
      r := { r with skippedDefect := r.skippedDefect + 1 }
      for id in c.defects do r := { r with defects := Report.bump r.defects id true }
      return r
  let some out := c.out | return { r with noValue := r.noValue + 1 }
  if out.kind == .error then
    -- rule 5: Julia rejects; nothing to compare
    r := { r with juliaErrors := r.juliaErrors + 1 }
    return match result with
      | some (_, got) =>
        if got.kind == .error then { r with portRejects := r.portRejects + 1 }
        else { r with portComputes := r.portComputes + 1 }
      | none => r
  let some (reg, got) := result | return { r with unimplemented := r.unimplemented + 1 }
  let why := compareWithOut reg.aspects (valueMode s reg c.op) (s.suite == "composite") got out
  return record r reg c why
where
  /-- Record a pass or a failure of evaluator `reg`. -/
  record (r : Report) (reg : Registration) (c : GoldenCase) (why : Array String) : Report :=
    if why.isEmpty then
      { r with evalPass := r.evalPass + 1, evaluators := Report.bump r.evaluators reg.name true }
    else
      let where_ := match c.a, c.b with
        | some a, some b => s!"a={a} b={b}"
        | some a, none => s!"a={a}"
        | _, _ => (c.label <|> c.input).getD ""
      { (r.note s!"{reg.name} {c.op} case {c.idx} ({where_}): {why}") with
        evalFail := r.evalFail + 1, evaluators := Report.bump r.evaluators reg.name false }

/-- Process one shard: schema checks, then every case. -/
def runShard (defects : DefectTable) (regs : Array Registration) (r : Report) (e : ShardEntry)
    (loaded : Except String (Shard × Nat)) : Report := Id.run do
  let mut r := { r with shards := r.shards + 1 }
  match loaded with
  | .error err => return r.check false fun _ => s!"{e.file}: {err}"
  | .ok (s, bytes) =>
    r := checkShard r e s bytes
    -- the applicable registrations, once per op
    let mut byOp : Array (String × Array Registration) := #[]
    for c in s.cases do
      let ps := caseProblems s defects c
      r := r.check ps.isEmpty fun _ => s!"{e.file} case {c.idx} ({c.op}): {ps.toList.take 4}"
      let regsOp ← match byOp.find? (·.1 == c.op) with
        | some (_, rs) => pure rs
        | none => do
          let rs := applicable regs s.suite c.op
          byOp := byOp.push (c.op, rs)
          pure rs
      r := evalCase r s defects regsOp c
    return { r with cases := r.cases + s.cases.size }

/-- Run one suite end to end. -/
def runSuite (root : System.FilePath) (defects : DefectTable) (regs : Array Registration)
    (suite : String) : IO Report := do
  let t0 ← IO.monoMsNow
  let mut r : Report := { suite }
  let m ← try pure (some (← loadManifest root suite)) catch err => do
    r := r.check false fun _ => s!"{suite}.json: {err}"
    pure none
  let some m := m | return r
  r := r.check (m.schema == 1 && m.suite == suite) fun _ => s!"{suite}.json: meta"
  r ← forEachShard root m r fun r e loaded => pure (runShard defects regs r e loaded)
  -- totals and the shard files on disk
  let sum := m.shards.foldl (fun acc e => acc.add e.stats) ({} : Stats)
  r := r.check (sum.cases == m.totals.cases && sum.errors == m.totals.errors
      && sum.refMismatch == m.totals.refMismatch && sum.unexplained == m.totals.unexplained) fun _ =>
    s!"{suite}.json: totals {repr m.totals} vs sum {repr sum}"
  r := r.check (m.totals.unexplained == 0) fun _ => s!"{suite}.json: {m.totals.unexplained} unexplained cases"
  let listed := m.shards.map fun e => (System.FilePath.mk e.file).fileName.getD ""
  let onDisk ← try
      let ents ← (root / suite).readDir
      pure (ents.filterMap fun d => if d.fileName.endsWith ".json" then some d.fileName else none)
    catch _ => pure #[]
  let stray := onDisk.filter (!listed.contains ·)
  r := r.check stray.isEmpty fun _ => s!"{suite}: shard files not in the manifest: {stray}"
  let t1 ← IO.monoMsNow
  return { r with ms := t1 - t0 }

/-- Check the per-defect totals of every suite manifest against the shard tags. -/
def checkDefectTotals (r : Report) (m : Manifest) (tagCounts : Stats) : Report :=
  r.check (m.totals.normalize.defects == tagCounts.normalize.defects) fun _ =>
    s!"{m.suite}.json: defect totals"

end Tests.Golden
