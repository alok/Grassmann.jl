import Tests.Golden.Defects

/-!
# Manifests, shards and case records

Streaming loaders for the element oracle (docs/port-notes/oracle-schema.md §3, §4, §8): a
suite manifest lists its shards; each shard is loaded, decoded, checked and evaluated on its
own and then dropped, so memory stays bounded by the largest shard (about 2.6 MB of JSON).

Decoding never aborts a shard: a malformed case is kept as a `GoldenCase` with its decode
errors recorded, and the harness counts it as a schema failure.
-/

namespace Tests.ElementOracle

open Lean

/-- The seven element suites, in the consumer's order (schema §11). -/
def elementSuites : List String := ["construct", "arith", "products", "unary", "composite", "floats", "docs"]

/-- Top-level keys of a shard per suite (schema §4). -/
def shardKeys : String → List String
  | "construct" => ["meta", "space", "cases", "stats"]
  | "composite" => ["meta", "space", "ops", "tolerance", "inputs", "cases", "stats"]
  | "floats" => ["meta", "encoding", "fields", "cases", "stats"]
  | "docs" => ["meta", "sandbox", "cases", "stats"]
  | _ => ["meta", "space", "ops", "reference", "inputs", "cases", "stats"]

/-- Shard or suite statistics (schema §4 `stats`, §3 `totals`). -/
structure Stats where
  /-- Number of cases. -/
  cases : Nat := 0
  /-- Cases whose output is an Error. -/
  errors : Nat := 0
  /-- Cases flagged `ref_mismatch`. -/
  refMismatch : Nat := 0
  /-- Errors or mismatches without a defect tag. -/
  unexplained : Nat := 0
  /-- Defect id ↦ number of tagged cases, sorted by id. -/
  defects : Array (String × Nat) := #[]
  deriving BEq, Repr, Inhabited

namespace Stats

/-- Decode a `stats`/`totals` object. -/
def decode (j : Json) : Except String Stats := do
  let n := fun (k : String) => match (j.getObjValD k).getNat? with
    | .ok v => pure v
    | .error _ => throw s!"stats.{k}: natural number expected"
  let ds ← match j.getObjValD "defects" with
    | .obj kvs => kvs.toList.toArray.mapM fun (k, v) => match v.getNat? with
      | .ok c => pure (k, c)
      | .error _ => throw s!"stats.defects.{k}: natural number expected"
    | _ => throw "stats.defects: object expected"
  return { cases := ← n "cases", errors := ← n "errors", refMismatch := ← n "ref_mismatch",
           unexplained := ← n "unexplained", defects := ds.qsort (·.1 < ·.1) }

/-- Add a defect count. -/
def addDefect (s : Stats) (id : String) (c : Nat := 1) : Stats :=
  match s.defects.findIdx? (·.1 == id) with
  | some i => { s with defects := s.defects.modify i fun (k, v) => (k, v + c) }
  | none => { s with defects := s.defects.push (id, c) }

/-- Sum of two statistics. -/
def add (a b : Stats) : Stats :=
  let base := { a with cases := a.cases + b.cases, errors := a.errors + b.errors,
                       refMismatch := a.refMismatch + b.refMismatch,
                       unexplained := a.unexplained + b.unexplained }
  b.defects.foldl (fun s (k, v) => s.addDefect k v) base

/-- Canonical form: defects sorted by id. -/
def normalize (s : Stats) : Stats := { s with defects := s.defects.qsort (·.1 < ·.1) }

end Stats

/-- One case record (schema §8), decoded. Suite-specific fields are `none` elsewhere. -/
structure GoldenCase where
  /-- Position in the shard. -/
  idx : Nat
  /-- The op key (`construct`, `docs`, `show` for the floats suite). -/
  op : String
  /-- First input (0-based index into the shard's `inputs`). -/
  a : Option Nat := none
  /-- Second input. -/
  b : Option Nat := none
  /-- Exponent of `pow` (composite). -/
  k : Option Int := none
  /-- The result (absent: docs statements returning `nothing`). -/
  out : Option GoldenElem := none
  /-- `flags` (only `ref_mismatch`). -/
  flags : Array String := #[]
  /-- `ref`: the independent reference dense vector (raw; its `T` is the operands'
  promoted type). -/
  ref : Option (Array Json) := none
  /-- Defect ids. -/
  defects : Array String := #[]
  /-- Construct `label`. -/
  label : Option String := none
  /-- Construct `src`. -/
  src : Option String := none
  /-- Docs `block`. -/
  block : Option String := none
  /-- Docs `input`. -/
  input : Option String := none
  /-- Docs `display` (`null` for `;`/`nothing`, absent when evaluation threw). -/
  display : Field String := .absent
  /-- Docs `stdout`. -/
  stdout : Option String := none
  /-- The evaluator arguments: the input elements (arith/products/unary/composite), the
  output stripped to its constructor data (construct: `kind`, `grade`, `bits`, `T`,
  `native`), the number itself (floats), none (docs). -/
  args : Array GoldenElem := #[]
  /-- Decode problems (a nonempty list makes the case a schema failure). -/
  problems : Array String := #[]
  deriving Inhabited

namespace GoldenCase

/-- Whether the output is a Julia error. -/
def isError (c : GoldenCase) : Bool := match c.out with
  | some o => o.kind == .error
  | none => false

/-- Whether the case is flagged `ref_mismatch`. -/
def isMismatch (c : GoldenCase) : Bool := c.flags.contains "ref_mismatch"

end GoldenCase

/-- A composite tolerance (schema §8.5). -/
structure Tolerance where
  /-- Relative tolerance. -/
  rtol : Float
  /-- Absolute tolerance. -/
  atol : Float
  deriving Inhabited, Repr

/-- One decoded shard. -/
structure Shard where
  /-- Suite name. -/
  suite : String
  /-- Shard name (`meta.shard`). -/
  name : String
  /-- The raw `meta` object. -/
  metaJ : Json := .null
  /-- Top-level keys present. -/
  keys : List String := []
  /-- The space descriptor (per-space suites). -/
  space : Option SpaceDesc := none
  /-- Op key ↦ Julia template. -/
  ops : Array (String × String) := #[]
  /-- Composite tolerances by op. -/
  tolerance : Array (String × Tolerance) := #[]
  /-- The input pool. -/
  inputs : Array GoldenElem := #[]
  /-- The cases. -/
  cases : Array GoldenCase := #[]
  /-- The committed statistics. -/
  stats : Stats := {}
  /-- Docs `meta.source` file stem (`algebra` for `oracle/docs/algebra.txt`). -/
  sourceStem : Option String := none
  /-- Shard-level decode problems. -/
  problems : Array String := #[]
  deriving Inhabited

/-- The space dimension of a shard, if it has a space. -/
def Shard.n? (s : Shard) : Option Nat := s.space.map (·.n)

/-- The tolerance of an op (composite). -/
def Shard.tol? (s : Shard) (op : String) : Option Tolerance := (s.tolerance.find? (·.1 == op)).map (·.2)

/-! ## Decoding -/

/-- A `Float` from 16 hex digits of its IEEE-754 bit pattern (floats suite). -/
def floatOfHex? (s : String) : Option Float :=
  if s.length != 16 then none else
  (s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c && c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)).map fun n => Float.ofBits n.toUInt64

/-- Decode a floats-suite case `{T, value, show, compact}` into a Number (or Bool) output
with the value, and the bare number as the evaluator argument (schema §8.6). -/
def decodeFloatCase (idx : Nat) (j : Json) : GoldenCase := Id.run do
  let s := fun (k : String) => (j.getObjValD k).getStr?.toOption
  let T := CoeffType.ofName ((s "T").getD "")
  let v := j.getObjValD "value"
  let hex := fun (x : Json) => match x with
    | .str h => (floatOfHex? h).map Scalar.float
    | _ => none
  let dec := fun (x : Json) => match x with
    | .str d => decodeReal? T.realPart d
    | _ => none
  let val : Option Scalar := match T, v with
    | .float64, _ => hex v
    | .complex .float64, .arr #[re, im] => do pure (.complex (← hex re) (← hex im))
    | .rational, .arr #[.str p, .str q] => do
      let num ← parseInt64? p
      let den ← parseInt64? q
      if den ≤ 0 then none else pure (.exact ((num : Rat) / (den : Rat)))
    | .complex r, .arr #[re, im] => do
      let dr := fun (x : Json) => match x with | .str d => decodeReal? r d | _ => none
      pure (.complex (← dr re) (← dr im))
    | _, _ => dec v
  let kind : Kind := if T == .bool then .bool else .number
  let some x := val
    | return { idx, op := "show", problems := #[s!"bad {T.name} value {v.compress}"] }
  let num : GoldenElem := { kind, T := some T, value := some (Coeffs.ofScalars T #[x]) }
  let out := { num with str := match s "show" with | some t => .val t | none => .absent,
                        compactStr := match s "compact" with | some t => .val t | none => .absent }
  let problems := if (s "show").isNone || (s "compact").isNone then #["floats case without show/compact"] else #[]
  return { idx, op := "show", out := some out, args := #[num], problems }

/-- Strip an output to the data a constructor needs (construct suite, schema §8.1): kind,
grade, bits, T, `V`, `native` and a Number's value (plus Phasor parts). -/
def constructorData (e : GoldenElem) : GoldenElem :=
  { kind := e.kind, T := e.T, V := e.V, grade := e.grade, bits := e.bits, native := e.native,
    value := e.value, amp := e.amp, angle := e.angle }

/-- Decode one case of a non-floats suite. -/
def decodeCase (suite : String) (inputs : Array GoldenElem) (idx : Nat) (j : Json) : GoldenCase := Id.run do
  let mut problems : Array String := #[]
  let str? := fun (k : String) => (j.getObjValD k).getStr?.toOption
  let nat? := fun (k : String) => match j.getObjVal? k with
    | .ok v => v.getNat?.toOption
    | .error _ => none
  let out ← match j.getObjVal? "out" with
    | .error _ => pure none
    | .ok o => match GoldenElem.decode o with
      | .ok e => do
        -- encode ∘ decode is the identity (bit-exact coefficients, every field kept)
        unless e.encode == o do problems := problems.push "out: encode (decode out) != out"
        pure (some e)
      | .error err => do problems := problems.push s!"out: {err}"; pure none
  let op := match suite with
    | "construct" | "docs" => suite
    | _ => (str? "op").getD ""
  let a := nat? "a"
  let b := nat? "b"
  let k := match j.getObjVal? "k" with
    | .ok v => v.getInt?.toOption
    | .error _ => none
  let flags := match j.getObjValD "flags" with
    | .arr fs => fs.filterMap (·.getStr?.toOption)
    | _ => #[]
  let ref := match j.getObjValD "ref" with
    | .arr r => some r
    | _ => none
  let defects := match j.getObjValD "defects" with
    | .arr ds => ds.filterMap (·.getStr?.toOption)
    | _ => #[]
  let display : Field String := match j.getObjVal? "display" with
    | .error _ => .absent
    | .ok .null => .null
    | .ok (.str s) => .val s
    | .ok _ => .absent
  let args : Array GoldenElem := match suite with
    | "construct" => match out with | some o => #[constructorData o] | none => #[]
    | "docs" => #[]
    | _ => #[a, b].filterMap fun i? => i?.bind (inputs[·]?)
  for (key, i?) in [("a", a), ("b", b)] do
    if let some i := i? then
      if i ≥ inputs.size then problems := problems.push s!"input index {key} = {i} out of range"
  return { idx, op, a, b, k, out, flags, ref, defects, label := str? "label", src := str? "src",
           block := str? "block", input := str? "input", display, stdout := str? "stdout",
           args, problems }

/-- Decode a whole shard JSON object. -/
def Shard.decode (suite : String) (j : Json) : Shard := Id.run do
  let mut problems : Array String := #[]
  let keys := match j with
    | .obj kvs => kvs.toList.map (·.1)
    | _ => []
  let metaJ := j.getObjValD "meta"
  let name := ((metaJ.getObjValD "shard").getStr?.toOption).getD ""
  let space ← match j.getObjVal? "space" with
    | .error _ => pure none
    | .ok s => match SpaceDesc.decode s with
      | .ok d => pure (some d)
      | .error e => do problems := problems.push s!"space: {e}"; pure none
  let ops := match j.getObjValD "ops" with
    | .obj kvs => kvs.toList.toArray.map fun (k, v) => (k, (v.getStr?.toOption).getD "")
    | _ => #[]
  let tolerance := match j.getObjValD "tolerance" with
    | .obj kvs => kvs.toList.toArray.map fun (k, v) =>
      let f := fun (key : String) => match (v.getObjValD key).getNum? with
        | .ok x => x.toFloat
        | .error _ => 0
      (k, ({ rtol := f "rtol", atol := f "atol" } : Tolerance))
    | _ => #[]
  let mut inputs : Array GoldenElem := #[]
  for (x, i) in (((j.getObjValD "inputs").getArr?.toOption).getD #[]).zipIdx do
    match GoldenElem.decode x with
    | .ok e =>
      unless e.encode == x do problems := problems.push s!"inputs[{i}]: encode (decode x) != x"
      inputs := inputs.push e
    | .error e => problems := problems.push s!"inputs[{i}]: {e}"; inputs := inputs.push { kind := .error }
  let raw := ((j.getObjValD "cases").getArr?.toOption).getD #[]
  let cases := raw.zipIdx.map fun (c, i) =>
    if suite == "floats" then decodeFloatCase i c else decodeCase suite inputs i c
  let stats ← match Stats.decode (j.getObjValD "stats") with
    | .ok s => pure s
    | .error e => do problems := problems.push e; pure {}
  let sourceStem := ((metaJ.getObjValD "source").getStr?.toOption).map fun p =>
    let base := (System.FilePath.mk p).fileName.getD p
    if base.endsWith ".txt" then (base.dropEnd 4).toString else base
  return { suite, name, metaJ, keys, space, ops, tolerance, inputs, cases, stats, sourceStem, problems }

/-- One manifest entry (schema §3). -/
structure ShardEntry where
  /-- Shard name. -/
  shard : String
  /-- Path relative to `oracle/golden/`. -/
  file : String
  /-- Committed counts. -/
  stats : Stats
  /-- File size in bytes. -/
  bytes : Nat
  /-- The space name (per-space suites). -/
  space : Option String := none
  deriving Inhabited

/-- A suite manifest (schema §3). -/
structure Manifest where
  /-- Suite name (`meta.suite`). -/
  suite : String
  /-- `meta.schema`. -/
  schema : Nat
  /-- Suite totals. -/
  totals : Stats
  /-- The shards in manifest order. -/
  shards : Array ShardEntry
  deriving Inhabited

/-- Decode a manifest. -/
def Manifest.decode (j : Json) : Except String Manifest := do
  let metaJ := j.getObjValD "meta"
  let suite ← match metaJ.getObjValD "suite" with
    | .str s => pure s
    | _ => throw "manifest meta.suite missing"
  let schema := ((metaJ.getObjValD "schema").getNat?.toOption).getD 0
  let totals ← Stats.decode (j.getObjValD "totals")
  let some sh := (j.getObjValD "shards").getArr?.toOption | throw "manifest without shards"
  let shards ← sh.mapM fun e => do
    let s := fun (k : String) => ((e.getObjValD k).getStr?.toOption)
    let n := fun (k : String) => ((e.getObjValD k).getNat?.toOption).getD 0
    let some shard := s "shard" | throw "manifest entry without shard"
    let some file := s "file" | throw "manifest entry without file"
    pure { shard, file, bytes := n "bytes", space := s "space",
           stats := { cases := n "cases", errors := n "errors", refMismatch := n "ref_mismatch",
                      unexplained := n "unexplained" } }
  return { suite, schema, totals, shards }

/-! ## Loading -/

/-- The golden root, relative to the repository root (where `lake test` runs). -/
def goldenRoot : System.FilePath := "oracle" / "golden"

/-- Read and parse one JSON file. -/
def loadJson (path : System.FilePath) : IO Json := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: bad JSON: {e}")

/-- Load a suite manifest. -/
def loadManifest (root : System.FilePath) (suite : String) : IO Manifest := do
  match Manifest.decode (← loadJson (root / s!"{suite}.json")) with
  | .ok m => pure m
  | .error e => throw (IO.userError s!"{suite}.json: {e}")

/-- Load the defect table. -/
def loadDefects (root : System.FilePath) : IO DefectTable := do
  match DefectTable.decode (← loadJson (root / "defects.json")) with
  | .ok t => pure t
  | .error e => throw (IO.userError s!"defects.json: {e}")

/-- Stream the shards of a suite: load, decode and hand each one to `f` in manifest order
(only one shard is alive at a time). -/
def forEachShard {σ : Type} (root : System.FilePath) (m : Manifest) (init : σ)
    (f : σ → ShardEntry → Except String (Shard × Nat) → IO σ) : IO σ := do
  let mut st := init
  for e in m.shards do
    let path := root / e.file
    let r ← try
        let md ← path.metadata
        let j ← loadJson path
        pure (Except.ok (Shard.decode m.suite j, md.byteSize.toNat))
      catch err => pure (Except.error (toString err))
    st ← f st e r
  return st

end Tests.ElementOracle
