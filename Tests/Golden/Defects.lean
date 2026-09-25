import Tests.Golden.Space

/-!
# The defect table (`oracle/golden/defects.json`)

Documented Julia defects (docs/port-notes/oracle-schema.md §10): each entry has an `id`, a
`policy` (`skip` > `ref` > `replicate`) and `match` tables. The element suites already carry
the tags (`case.defects`), so consumers only need the policies; this module also implements
the full match language (globs with `|` alternatives and `*`, operand kind patterns
`Kind[:g|:n]`, and the named `when` predicates) so that

* the harness can re-derive every committed tag from the table (a check that the table and
  the goldens agree), and
* consumers of the untagged blade-level goldens (`golden/blades/*.jsonl`) can classify their
  records with `suite = "blades"`.

The semantics follow the generator's `defect_ids` (`oracle/common.jl`), which is itself
specified by schema §10.
-/

namespace Tests.Golden

open Lean

/-- A defect policy (schema §10). -/
inductive Policy where
  /-- Julia's value is the intended one: compare with `out`. -/
  | replicate
  /-- Compare values with the case's `ref` when present. -/
  | ref
  /-- No trustworthy expected value. -/
  | skip
  deriving BEq, Repr, Inhabited, DecidableEq

namespace Policy

/-- Decode a policy name. -/
def ofName? : String → Option Policy
  | "replicate" => some .replicate
  | "ref" => some .ref
  | "skip" => some .skip
  | _ => none

/-- Strength order `skip > ref > replicate`. -/
def strength : Policy → Nat
  | .replicate => 0
  | .ref => 1
  | .skip => 2

/-- The stronger of two policies. -/
def max (a b : Policy) : Policy := if a.strength ≥ b.strength then a else b

end Policy

/-! ## Globs -/

/-- One glob alternative: a literal string (no `*`) or a wildcard pattern as characters. -/
inductive GlobAlt where
  /-- Matches exactly this string. -/
  | lit (s : String)
  /-- A pattern containing `*` (any run of characters, including none). -/
  | wild (p : Array Char)
  deriving Inhabited, Repr

/-- A compiled glob: `|`-separated alternatives (schema §10). -/
structure Glob where
  /-- The alternatives. -/
  alts : Array GlobAlt
  deriving Inhabited, Repr

/-- Compile a glob pattern. -/
def Glob.compile (pat : String) : Glob :=
  ⟨((pat.splitOn "|").map fun alt =>
    if alt.contains '*' then GlobAlt.wild alt.toList.toArray else .lit alt).toArray⟩

/-- Wildcard matching of `p` against the whole of `s` (the classic greedy algorithm with
backtracking to the last `*`): `i`, `j` index `s`, `p`; `star` is the position after the
last `*` seen and `mark` the position in `s` it was matched from. Tail-recursive. -/
def wildMatch (p s : Array Char) (i j : Nat) (star : Option Nat) (mark : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if i < s.size then
      if j < p.size && p[j]! != '*' && p[j]! == s[i]! then wildMatch p s (i + 1) (j + 1) star mark fuel
      else if j < p.size && p[j]! == '*' then wildMatch p s i (j + 1) (some (j + 1)) i fuel
      else match star with
        | some st => wildMatch p s (mark + 1) st star (mark + 1) fuel
        | none => false
    else (p.extract j p.size).all (· == '*')

/-- Whether the glob matches the whole string. -/
def Glob.test (g : Glob) (s : String) : Bool :=
  g.alts.any fun
    | .lit l => l == s
    | .wild p =>
      let cs := s.toList.toArray
      wildMatch p cs 0 0 none 0 ((cs.size + 1) * (p.size + 1) + 1)

/-! ## Match tables -/

/-- One operand kind pattern alternative: a kind name and an optional grade (`n` = the
space's `grade`). -/
structure KindAlt where
  /-- Kind name. -/
  kind : String
  /-- Required grade: `some (some g)` for `:g`, `some none` for `:n`. -/
  grade : Option (Option Nat) := none
  deriving Inhabited, Repr

/-- An operand pattern: `*` (`none`) or alternatives. -/
abbrev KindPat := Option (Array KindAlt)

/-- Compile an operand pattern such as `Chain:0|Chain:n` or `*`. -/
def KindPat.compile (s : String) : KindPat :=
  if s == "*" then none else
  some ((s.splitOn "|").toArray.map fun alt =>
    match alt.splitOn ":" with
    | [k, "n"] => { kind := k, grade := some none }
    | [k, g] => { kind := k, grade := some g.toNat? }
    | _ => { kind := alt })

/-- One `match` table (schema §10): every present field must match. -/
structure MatchTable where
  /-- Suite glob. -/
  suite : Option Glob := none
  /-- Space-name glob. -/
  space : Option Glob := none
  /-- Op glob. -/
  op : Option Glob := none
  /-- Output kind glob (`Nothing` when `out` is absent). -/
  out : Option Glob := none
  /-- Error message glob (never matches a non-Error case). -/
  msg : Option Glob := none
  /-- Construct `label` / docs `block` glob. -/
  block : Option Glob := none
  /-- Construct `src` / docs `input` glob. -/
  input : Option Glob := none
  /-- Docs source file / blade dump file glob. -/
  file : Option Glob := none
  /-- One pattern per operand. -/
  kinds : Option (Array KindPat) := none
  /-- A named predicate. -/
  when : Option String := none
  deriving Inhabited

/-- One defect entry. -/
structure Defect where
  /-- Unique id. -/
  id : String
  /-- Consumer policy. -/
  policy : Policy
  /-- Prose title. -/
  title : String := ""
  /-- Julia file:line. -/
  source : String := ""
  /-- What the port does instead. -/
  correct : String := ""
  /-- The match tables. -/
  tables : Array MatchTable := #[]
  deriving Inhabited

/-- The loaded defect table, in table order. -/
structure DefectTable where
  /-- Entries in table order. -/
  entries : Array Defect := #[]
  deriving Inhabited

/-- The fields a match table may have (schema §10). -/
def matchKeys : List String :=
  ["suite", "space", "op", "kinds", "when", "out", "msg", "block", "input", "file"]

/-- The named `when` predicates (schema §10). -/
def whenNames : List String :=
  ["same_bits", "diff_bits", "couple_rev_plus", "null_blade", "mixed_parity_first", "Isq_plus"]

/-- Decode one match table. -/
def MatchTable.decode (j : Json) : Except String MatchTable := do
  let .obj kvs := j | throw "match table is not an object"
  for (k, _) in kvs.toList do
    unless matchKeys.contains k do throw s!"unknown match field {k}"
  let g := fun (k : String) => match j.getObjVal? k with
    | .ok (.str s) => .ok (some (Glob.compile s))
    | .ok _ => .error s!"match.{k}: string expected"
    | .error _ => .ok none
  let kinds ← match j.getObjVal? "kinds" with
    | .ok (.arr a) => do
      let ps ← a.mapM fun (x : Json) => match x with
        | Json.str s => (pure (KindPat.compile s) : Except String KindPat)
        | _ => throw "match.kinds entry: string expected"
      pure (some ps)
    | .ok _ => throw "match.kinds: array expected"
    | .error _ => pure none
  let when ← match j.getObjVal? "when" with
    | .ok (.str s) => if whenNames.contains s then pure (some s) else throw s!"unknown predicate {s}"
    | .ok _ => throw "match.when: string expected"
    | .error _ => pure none
  return { suite := ← g "suite", space := ← g "space", op := ← g "op", out := ← g "out",
           msg := ← g "msg", block := ← g "block", input := ← g "input", file := ← g "file",
           kinds, when }

/-- Decode `golden/defects.json` (ids unique, policies valid). -/
def DefectTable.decode (j : Json) : Except String DefectTable := do
  let metaJ := j.getObjValD "meta"
  unless metaJ.getObjValD "schema" == (1 : Nat) do throw "defects.json: schema != 1"
  let some ds := (j.getObjValD "defects").getArr?.toOption | throw "defects.json: no defects array"
  let mut out : Array Defect := #[]
  for d in ds do
    let some id := (d.getObjValD "id").getStr?.toOption | throw "defect without id"
    if out.any (·.id == id) then throw s!"duplicate defect id {id}"
    let some pol := ((d.getObjValD "policy").getStr?.toOption).bind Policy.ofName?
      | throw s!"defect {id}: bad policy"
    let ms ← match d.getObjValD "match" with
      | .arr a => a.mapM MatchTable.decode
      | _ => throw s!"defect {id}: match is not an array"
    let s := fun (k : String) => ((d.getObjValD k).getStr?.toOption).getD ""
    out := out.push { id, policy := pol, title := s "title", source := s "source",
                      correct := s "correct", tables := ms }
  return ⟨out⟩

namespace DefectTable

/-- The policy of an id (`none` if unknown). -/
def policy? (t : DefectTable) (id : String) : Option Policy :=
  (t.entries.find? (·.id == id)).map (·.policy)

/-- The strongest policy of a case's tags (`none` if untagged). Unknown ids count as
`skip` (the harness reports them separately). -/
def strongest (t : DefectTable) (ids : Array String) : Option Policy :=
  ids.foldl (fun acc id =>
    let p := (t.policy? id).getD .skip
    some (match acc with | some q => q.max p | none => p)) none

end DefectTable

/-! ## Evaluating the match language -/

/-- An operand as the matcher sees it: kind name, grade and bits (schema §10 uses only
these). -/
structure Operand where
  /-- Kind name (`Number` for plain numbers). -/
  kind : String
  /-- `grade` field. -/
  grade : Option Nat := none
  /-- `bits` field. -/
  bits : Option UInt64 := none
  deriving Inhabited, Repr

/-- The operand view of an element. -/
def Operand.ofElem (e : GoldenElem) : Operand := { kind := e.kind.name, grade := e.grade, bits := e.bits }

/-- Everything the match language reads about one case. -/
structure MatchSubject where
  /-- Suite name (`blades` for the blade dumps). -/
  suite : String
  /-- The shard's `space.name` (empty for docs/floats). -/
  space : String := ""
  /-- The case op (the suite name for construct/docs). -/
  op : String
  /-- Output kind (`Nothing` when absent). -/
  out : String
  /-- Error message, only for Error outputs. -/
  msg : Option String := none
  /-- Construct label / docs block. -/
  block : Option String := none
  /-- Construct src / docs input. -/
  input : Option String := none
  /-- Docs source file name (no directory, no `.txt`) / blade dump file name. -/
  file : Option String := none
  /-- The operands `a`, `b` (inputs). -/
  args : Array Operand := #[]
  /-- The shard space's descriptor fields the predicates read: `n`, `grade`,
  `conformal`, `Isq`. -/
  spaceN : Nat := 0
  /-- `space.grade` (the `:n` of kind patterns). -/
  spaceGrade : Nat := 0
  /-- `space.conformal`. -/
  conformal : Bool := false
  /-- `space.Isq`. -/
  isq : Option Int := none
  deriving Inhabited

/-- Does an operand pattern match an operand? -/
def KindPat.test (p : KindPat) (topGrade : Nat) (a : Operand) : Bool :=
  match p with
  | none => true
  | some alts => alts.any fun alt =>
    alt.kind == a.kind &&
      match alt.grade with
      | none => true
      | some none => a.grade == some topGrade
      | some (some g) => a.grade == some g

/-- The named predicates of schema §10. -/
def whenHolds (name : String) (s : MatchSubject) : Bool :=
  let pc := fun (b : UInt64) => DirectSum.Bits.popcount b
  match name with
  | "same_bits" => s.args.size == 2 &&
      (match s.args[0]!.bits, s.args[1]!.bits with | some a, some b => a == b | _, _ => false)
  | "diff_bits" => s.args.size == 2 &&
      (match s.args[0]!.bits, s.args[1]!.bits with | some a, some b => a != b | _, _ => false)
  | "couple_rev_plus" => s.args.any fun a =>
      a.kind == "Couple" && (pc (a.bits.getD 0) % 4 == 0 || pc (a.bits.getD 0) % 4 == 1)
  | "null_blade" => s.conformal && s.args.any fun a =>
      match a.bits with
      | some b => (b &&& 1 != 0) != (b &&& 2 != 0)
      | none => false
  | "mixed_parity_first" =>
      match s.args[0]? with
      | some a =>
        let odd := pc (a.bits.getD 0) % 2 == 1
        if a.kind == "Couple" then odd
        else if a.kind == "PseudoCouple" then odd != (s.spaceN % 2 == 1)
        else false
      | none => false
  | "Isq_plus" => match s.isq with | some q => q > 0 | none => false
  | _ => false

/-- Does a match table match? -/
def MatchTable.test (m : MatchTable) (s : MatchSubject) : Bool :=
  let g := fun (pat : Option Glob) (v : Option String) => match pat with
    | none => true
    | some p => match v with | some x => p.test x | none => false
  g m.suite (some s.suite) && g m.space (some s.space) && g m.op (some s.op)
    && (match m.kinds with
        | none => true
        | some ks => ks.size == s.args.size &&
            (ks.zip s.args).all fun (p, a) => p.test s.spaceGrade a)
    && (match m.when with | none => true | some w => whenHolds w s)
    && g m.out (some s.out) && g m.msg s.msg && g m.block s.block && g m.input s.input
    && g m.file s.file

/-- The ids (in table order) of the defects matching a case. -/
def DefectTable.tags (t : DefectTable) (s : MatchSubject) : Array String :=
  t.entries.filterMap fun d => if d.tables.any (·.test s) then some d.id else none

end Tests.Golden
