import DeMorgan.TruthValues

/-!
# Truth tables: the truth-table magma

Julia source: `DeMorgan.jl src/DeMorgan.jl` (DM:60-172). A `TruthTable{N,M}` is an
expression together with every sub-expression it has met, grouped into `M` classes of
equal truth column, each class carrying the names ("aliases") it was seen under, in
insertion order. `(i, j)` selects the class and alias of the expression itself. Binary
connectives merge the two operands' class lists with `combine` (DM:103-146).

Lean design:
* `TruthTable N` keeps the variable count `N` in the type (Julia's `N`); the class count
  `M` is runtime (`classes.size`). Indices `i`, `j` are **0-based** (Julia's are 1-based).
* `combine` is transcribed literally, including two Julia defects (port-notes §4.3.3,
  Appendix A #3): membership is tested against the *original* left operand, so classes can
  be duplicated, and after a projection class has been inserted in the middle, a later
  alias is appended at the *stale* index (a different class). `TruthTable.Clean` provides
  the fixed merge (dedup and indices against the current list).
* Julia's PrettyTables-based `show` (DM:161-172, PrettyTables v2) is reproduced by
  `render` without the dependency; `Repr` uses it.
-/

namespace DeMorgan

open AbstractLattices

/-- Julia's connectives beyond `∧`/`∨` (DM:52-58), shared by columns and tables so the
scoped notation works for both. -/
class Connectives (α : Type) where
  /-- `¬p` (Julia `!`/`¬`) -/
  not : α → α
  /-- `p → q` (Julia `-->`/`→`) -/
  imp : α → α → α
  /-- `p ← q` (Julia `<--`/`←`) -/
  rimp : α → α → α
  /-- `p ↔ q` (Julia `<-->`/`↔`) -/
  iff : α → α → α

/-- Julia `¬` (DM:58); overloads Lean's `¬` by type within `open DeMorgan`. -/
scoped prefix:max "¬" => Connectives.not
/-- Julia `-->` / `→` (DM:52, 58). Right-associative, below `∧`/`∨` as in Julia. -/
scoped infixr:25 " ⇒ " => Connectives.imp
/-- Julia `<--` / `←` (DM:53, 58). -/
scoped infixr:25 " ⇐ " => Connectives.rimp
/-- Julia `<-->` / `↔` (DM:54, 58). -/
scoped infixr:25 " ⇔ " => Connectives.iff

instance {N : Nat} : Connectives (TruthValues N) where
  not := TruthValues.not
  imp := TruthValues.imp
  rimp := TruthValues.rimp
  iff := TruthValues.iff

/-- One class of a truth table: a column and the aliases it was seen under
(Julia `p[c]` and `n[c]`, DM:61-62). -/
structure TruthTable.Class (N : Nat) where
  /-- The truth column shared by every alias of the class. -/
  col : TruthValues N
  /-- The aliases, in insertion order. -/
  names : Array String
  deriving DecidableEq

instance {N : Nat} : Inhabited (TruthTable.Class N) := ⟨⟨TruthValues.bot, #[]⟩⟩

/-- Julia `TruthTable{N,M}` (DM:60-65), with `M = classes.size` and 0-based `i`, `j`. -/
structure TruthTable (N : Nat) where
  /-- The classes, in Julia's order (projections first, then first appearance). -/
  classes : Array (TruthTable.Class N)
  /-- The class of the expression (0-based; Julia `i - 1`). -/
  i : Nat
  /-- The alias of the expression within its class (0-based; Julia `j - 1`). -/
  j : Nat
  deriving DecidableEq

namespace TruthTable

variable {N : Nat}

/-- Julia `TruthTable{N}(p::UInt, s::String)` (DM:67): a one-class table. -/
def ofColumn (col : TruthValues N) (name : String) : TruthTable N := ⟨#[⟨col, #[name]⟩], 0, 0⟩

/-- The projection table of variable `m` named `name`, as bound by `@truthtable`
(DM:87-91). -/
def proj (N : Nat) (m : Fin N) (name : String) : TruthTable N :=
  ofColumn (TruthValues.proj m) name

/-- The projection tables of `@truthtable names...` (DM:87-91). -/
def vars (N : Nat) (names : Fin N → String) : Array (TruthTable N) :=
  Array.ofFn fun m => proj N m (names m)

/-- The class of the expression. -/
@[inline] def current (t : TruthTable N) : Class N := t.classes[t.i]!

/-- The truth column of the expression. -/
@[inline] def value (t : TruthTable N) : TruthValues N := t.current.col

/-- Julia `string(t) = t.n[t.i][t.j]` (DM:70): the expression's own name. -/
protected def toString (t : TruthTable N) : String := t.current.names[t.j]?.getD ""

instance : ToString (TruthTable N) := ⟨TruthTable.toString⟩

/-- Julia `parstring(s)` (DM:71-78): keep `s` bare iff it is one character long or of the
form `¬(…)` with a parenthesis-free inside (the regex `^¬\((?:[^()]+|(?R))*\)$`, whose
anchored recursion can never match, so the inside may also be empty); otherwise wrap it
in parentheses. -/
def parstring (s : String) : String :=
  let cs := s.toList
  let negated := match cs with
    | '¬' :: '(' :: rest => rest.getLast? == some ')' && (rest.dropLast.all fun c => c != '(' && c != ')')
    | _ => false
  if cs.length == 1 || negated then s else "(" ++ s ++ ")"

/-- The projection columns of `N` variables (Julia `select(N)`, DM:84). -/
def projections (N : Nat) : Array (TruthValues N) :=
  (Array.range N).map fun n => TruthValues.ofUInt64 N (select (n + 1) N)

/-- Julia `combine(p, q, r, n)` (DM:103-146), transcribed literally: merge the classes of
`q` (then the new class `(r, n)`) into `p`. Membership and alias tests use `p`'s
**original** classes and indices (Julia quirk, port-notes §4.3.3). -/
def combine (p : TruthTable N) (q : Array (Class N)) (r : TruthValues N) (n : Array String) :
    TruthTable N := Id.run do
  let orig := p.classes
  let sN := projections N
  let mut rp := p.classes
  let mut out : Nat × Nat := (0, 0)
  let qs := q.push ⟨r, n⟩
  for h : idx in [0:qs.size] do
    let last := idx + 1 == qs.size
    let c := qs[idx]
    match orig.findIdx? (·.col == c.col) with
    | some k =>
      for s in c.names do
        match orig[k]!.names.idxOf? s with
        | some jj => if last then out := (k, jj)
        | none =>
          -- `rn[k]` indexes the *current* list with the *original* index (Julia quirk)
          rp := rp.modify k fun cl => { cl with names := cl.names.push s }
          if last then out := (k, rp[k]!.names.size - 1)
    | none =>
      let names :=
        if c.col == TruthValues.bot then #["⊥"] ++ c.names
        else if c.col == TruthValues.top then #["⊤"] ++ c.names
        else c.names
      if sN.contains c.col then
        let l := (rp.findIdx? fun cl => !sN.contains cl.col).getD rp.size
        rp := if hl : l ≤ rp.size then rp.insertIdx l ⟨c.col, names⟩ hl else rp.push ⟨c.col, names⟩
        if last then out := (l, 0)
      else
        rp := rp.push ⟨c.col, names⟩
        if last then out := (rp.size - 1, 0)
  return ⟨rp, out.1, out.2⟩

/-- A binary connective on tables (DM:148-159): combine the operands under the name
`parstring(p) * sym * parstring(q)`. -/
def binop (sym : String) (f : TruthValues N → TruthValues N → TruthValues N)
    (p q : TruthTable N) : TruthTable N :=
  combine p q.classes (f p.value q.value) #[parstring p.toString ++ sym ++ parstring q.toString]

/-- Julia `p ∧ q` (DM:148, `'∧'`). -/
def and : TruthTable N → TruthTable N → TruthTable N := binop "∧" TruthValues.and
/-- Julia `p ∨ q` (DM:148, `'∨'`). -/
def or : TruthTable N → TruthTable N → TruthTable N := binop "∨" TruthValues.or
/-- Julia `p --> q` (DM:148, `'→'`). -/
def imp : TruthTable N → TruthTable N → TruthTable N := binop "→" TruthValues.imp
/-- Julia `p <-- q` (DM:148, `'←'`). -/
def rimp : TruthTable N → TruthTable N → TruthTable N := binop "←" TruthValues.rimp
/-- Julia `p <--> q` (DM:148, `'↔'`). -/
def iff : TruthTable N → TruthTable N → TruthTable N := binop "↔" TruthValues.iff

/-- Julia `!(p::TruthTable)` (DM:95-98): the new name is `¬(` + the **last** alias of the
expression's class + `)`, never passed through `parstring` (quirk #4). -/
def not (p : TruthTable N) : TruthTable N :=
  combine p #[] p.value.not #["¬(" ++ (p.current.names.back?.getD "") ++ ")"]

instance : HWedge (TruthTable N) (TruthTable N) (TruthTable N) := ⟨and⟩
instance : HVee (TruthTable N) (TruthTable N) (TruthTable N) := ⟨or⟩
/-- Julia `&` (DM:93). -/
instance : AndOp (TruthTable N) := ⟨and⟩
/-- Julia `|` (DM:94). -/
instance : OrOp (TruthTable N) := ⟨or⟩
instance : Complement (TruthTable N) := ⟨not⟩
instance : Connectives (TruthTable N) := ⟨not, imp, rimp, iff⟩

/-! ## The fixed merge -/

namespace Clean

/-- `combine` with the two Julia defects fixed: classes and aliases are looked up in the
list being built, so no class is duplicated and indices never go stale. -/
def combine (p : TruthTable N) (q : Array (Class N)) (r : TruthValues N) (n : Array String) :
    TruthTable N := Id.run do
  let sN := projections N
  let mut rp := p.classes
  let mut out : Nat × Nat := (0, 0)
  let qs := q.push ⟨r, n⟩
  for h : idx in [0:qs.size] do
    let last := idx + 1 == qs.size
    let c := qs[idx]
    match rp.findIdx? (·.col == c.col) with
    | some k =>
      for s in c.names do
        match rp[k]!.names.idxOf? s with
        | some jj => if last then out := (k, jj)
        | none =>
          rp := rp.modify k fun cl => { cl with names := cl.names.push s }
          if last then out := (k, rp[k]!.names.size - 1)
    | none =>
      let names :=
        if c.col == TruthValues.bot then #["⊥"] ++ c.names
        else if c.col == TruthValues.top then #["⊤"] ++ c.names
        else c.names
      if sN.contains c.col then
        let l := (rp.findIdx? fun cl => !sN.contains cl.col).getD rp.size
        rp := if hl : l ≤ rp.size then rp.insertIdx l ⟨c.col, names⟩ hl else rp.push ⟨c.col, names⟩
        if last then out := (l, 0)
      else
        rp := rp.push ⟨c.col, names⟩
        if last then out := (rp.size - 1, 0)
  return ⟨rp, out.1, out.2⟩

/-- Binary connective with the fixed merge. -/
def binop (sym : String) (f : TruthValues N → TruthValues N → TruthValues N)
    (p q : TruthTable N) : TruthTable N :=
  combine p q.classes (f p.value q.value) #[parstring p.toString ++ sym ++ parstring q.toString]

/-- `∧` with the fixed merge. -/
def and : TruthTable N → TruthTable N → TruthTable N := binop "∧" TruthValues.and
/-- `∨` with the fixed merge. -/
def or : TruthTable N → TruthTable N → TruthTable N := binop "∨" TruthValues.or
/-- `→` with the fixed merge. -/
def imp : TruthTable N → TruthTable N → TruthTable N := binop "→" TruthValues.imp
/-- `←` with the fixed merge. -/
def rimp : TruthTable N → TruthTable N → TruthTable N := binop "←" TruthValues.rimp
/-- `↔` with the fixed merge. -/
def iff : TruthTable N → TruthTable N → TruthTable N := binop "↔" TruthValues.iff
/-- `¬` with the fixed merge. -/
def not (p : TruthTable N) : TruthTable N :=
  combine p #[] p.value.not #["¬(" ++ (p.current.names.back?.getD "") ++ ")"]

end Clean

/-! ## Evaluating formulas as tables -/

/-- Evaluate a formula with the Julia table connectives, the variables being the
projection tables `vars` (Julia evaluates the same expression tree, DM:148-159).
`⊥`/`⊤` (not supported by Julia's `TruthTable`) become one-class tables. -/
def ofFormula (vars : Fin N → TruthTable N) : Formula N → TruthTable N
  | .var m => vars m
  | .bot => ofColumn TruthValues.bot "⊥"
  | .top => ofColumn TruthValues.top "⊤"
  | .not φ => (ofFormula vars φ).not
  | .and φ ψ => (ofFormula vars φ).and (ofFormula vars ψ)
  | .or φ ψ => (ofFormula vars φ).or (ofFormula vars ψ)
  | .imp φ ψ => (ofFormula vars φ).imp (ofFormula vars ψ)
  | .rimp φ ψ => (ofFormula vars φ).rimp (ofFormula vars ψ)
  | .iff φ ψ => (ofFormula vars φ).iff (ofFormula vars ψ)

/-- `ofFormula` with the fixed merge. -/
def ofFormulaClean (vars : Fin N → TruthTable N) : Formula N → TruthTable N
  | .var m => vars m
  | .bot => ofColumn TruthValues.bot "⊥"
  | .top => ofColumn TruthValues.top "⊤"
  | .not φ => Clean.not (ofFormulaClean vars φ)
  | .and φ ψ => Clean.and (ofFormulaClean vars φ) (ofFormulaClean vars ψ)
  | .or φ ψ => Clean.or (ofFormulaClean vars φ) (ofFormulaClean vars ψ)
  | .imp φ ψ => Clean.imp (ofFormulaClean vars φ) (ofFormulaClean vars ψ)
  | .rimp φ ψ => Clean.rimp (ofFormulaClean vars φ) (ofFormulaClean vars ψ)
  | .iff φ ψ => Clean.iff (ofFormulaClean vars φ) (ofFormulaClean vars ψ)

/-! ## Rendering (PrettyTables v2 unicode format, port-notes §5.3) -/

/-- Julia `pretty_table(::TruthTable)` (DM:163-169) with PrettyTables v2 defaults: one
column per class, `max` alias-count header rows (missing aliases blank), the `2^N` rows
(`rows N`) `digits(p[c], base=2, pad=2^N)`, cells right-aligned and padded by one space,
unicode box drawing. The result ends with a newline, like `pretty_table`. -/
def render (t : TruthTable N) : String := Id.run do
  let cols := t.classes
  let h := cols.foldl (fun acc c => max acc c.names.size) 0
  let header : Array (Array String) :=
    (Array.range h).map fun r => cols.map fun c => c.names[r]?.getD ""
  let body : Array (Array String) :=
    (Array.range (rows N)).map fun k => cols.map fun c => if c.col.eval k then "1" else "0"
  let widths : Array Nat := (Array.range cols.size).map fun c =>
    (header ++ body).foldl (fun acc row => max acc (row[c]?.getD "").length) 0
  let rule (l m r : String) : String :=
    l ++ String.intercalate m (widths.toList.map fun w => String.ofList (List.replicate (w + 2) '─')) ++ r
  let line (row : Array String) : String :=
    "│" ++ String.intercalate "│" ((List.range cols.size).map fun c =>
      let s := row[c]?.getD ""
      " " ++ String.ofList (List.replicate (widths[c]! - s.length) ' ') ++ s ++ " ") ++ "│"
  let mut out := rule "┌" "┬" "┐" ++ "\n"
  for r in header do out := out ++ line r ++ "\n"
  out := out ++ rule "├" "┼" "┤" ++ "\n"
  for r in body do out := out ++ line r ++ "\n"
  out := out ++ rule "└" "┴" "┘" ++ "\n"
  return out

instance : Repr (TruthTable N) := ⟨fun t _ => render t⟩

end TruthTable

/-! ## `@truthtable` -/

/-- `truthtable p q r in e`: Julia `@truthtable p q r` (DM:87-91) scoped over `e`. Binds
each name to its projection table over `N = #names` variables (the first name varies
slowest; row 0 is all-true), named by its identifier. -/
scoped syntax (name := truthtableIn) "truthtable " ident+ " in " term : term

macro_rules
  | `(truthtable $xs* in $body) => do
    let n := xs.size
    let nLit := Lean.Syntax.mkNumLit (toString n)
    let mut acc := body
    for idx in (List.range n).reverse do
      let x := xs[idx]!
      let iLit := Lean.Syntax.mkNumLit (toString idx)
      let nameLit := Lean.Syntax.mkStrLit x.getId.toString
      acc ← `(let $x : DeMorgan.TruthTable $nLit :=
          DeMorgan.TruthTable.proj $nLit ⟨$iLit, by decide⟩ $nameLit
        $acc)
    return acc

end DeMorgan
