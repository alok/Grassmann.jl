import DeMorgan
import Tests.AbstractLattices.Harness

/-!
DeMorgan tests: goldens from `oracle/demorgan/gen.jl` (`oracle/golden/demorgan/*.json`),
the README tables (port-notes §6.3, verbatim), compile-time `decide` checks of the
tautology checker, and properties of the fixed merge.
-/

open DeMorgan Tests.Small

namespace Tests.DeMorgan

/-! ## Compile-time checks -/

-- projection columns (port-notes §4.3.1)
example : select 1 2 = 0b0101 := by decide
example : select 2 2 = 0b0011 := by decide
example : select 3 3 = 0x0f := by decide
example : select 1 6 = 0x5555555555555555 := by decide
example : select 6 6 = 0x00000000FFFFFFFF := by decide
-- `TruthValues(false,true,true,false) → TruthValues{4}(6)`; `¬` of it is 65529
example : (TruthValues.ofBools [false, true, true, false]).toNat = 6 := by decide
example : (TruthValues.ofBools [false, true, true, false]).not.toNat = 65529 := by decide
example : (TruthValues.not (TruthValues.ofNat 2 0b0011)).toNat = 12 := by decide
example : (TruthValues.imp (TruthValues.ofNat 2 0b0011) (TruthValues.ofNat 2 0b0101)).toNat = 13 := by
  decide
example : (TruthValues.not (TruthValues.bot : TruthValues 6)).toNat = 0xFFFFFFFFFFFFFFFF := by decide
-- the tautology checker, decided by the kernel (contraposition, hypothetical syllogism)
example : (Formula.iff (.imp (.var (0 : Fin 2)) (.var 1))
    (.imp (.not (.var 1)) (.not (.var 0)))).isTautology = true := by decide
example : (Formula.imp (.and (.imp (.var (0 : Fin 3)) (.var 1)) (.imp (.var 1) (.var 2)))
    (.imp (.var 0) (.var 2))).isTautology = true := by decide
example : (Formula.imp (.var (0 : Fin 2)) (.var 1)).isTautology = false := by decide
-- … and by the theorem, a statement about all assignments
example : ∀ ρ : Fin 2 → Bool, (Formula.or (.var 0) (.not (.var 0))).eval ρ = true :=
  (Formula.isTautology_iff _).mp (by decide)

/-! README tables (DeMorgan.jl README.md:9-41, PrettyTables v2), verbatim. -/

def readme1 : String :=
"┌───┬───┬───────────┬──────┬──────┬───────────────────┐
│ p │ q │       p→q │ ¬(q) │ ¬(p) │                 ⊤ │
│   │   │ ¬(q)→¬(p) │      │      │ (p→q)↔(¬(q)→¬(p)) │
├───┼───┼───────────┼──────┼──────┼───────────────────┤
│ 1 │ 1 │         1 │    0 │    0 │                 1 │
│ 1 │ 0 │         0 │    1 │    0 │                 1 │
│ 0 │ 1 │         1 │    0 │    1 │                 1 │
│ 0 │ 0 │         1 │    1 │    1 │                 1 │
└───┴───┴───────────┴──────┴──────┴───────────────────┘
"

def readme2 : String :=
"┌───┬───┬───┬─────┬─────┬─────────────┬─────┬─────────────────────┐
│ p │ q │ r │ p→q │ q→r │ (p→q)∧(q→r) │ p→r │                   ⊤ │
│   │   │   │     │     │             │     │ ((p→q)∧(q→r))→(p→r) │
├───┼───┼───┼─────┼─────┼─────────────┼─────┼─────────────────────┤
│ 1 │ 1 │ 1 │   1 │   1 │           1 │   1 │                   1 │
│ 1 │ 1 │ 0 │   1 │   0 │           0 │   0 │                   1 │
│ 1 │ 0 │ 1 │   0 │   1 │           0 │   1 │                   1 │
│ 1 │ 0 │ 0 │   0 │   1 │           0 │   0 │                   1 │
│ 0 │ 1 │ 1 │   1 │   1 │           1 │   1 │                   1 │
│ 0 │ 1 │ 0 │   1 │   0 │           0 │   1 │                   1 │
│ 0 │ 0 │ 1 │   1 │   1 │           1 │   1 │                   1 │
│ 0 │ 0 │ 0 │   1 │   1 │           1 │   1 │                   1 │
└───┴───┴───┴─────┴─────┴─────────────┴─────┴─────────────────────┘
"

#guard TruthTable.render (truthtable p q in (p ⇒ q) ⇔ (¬q ⇒ ¬p)) == readme1
#guard TruthTable.render (truthtable p q r in ((p ⇒ q) &&& (q ⇒ r)) ⇒ (p ⇒ r)) == readme2
#guard toString (truthtable p q in (p ⇒ q) ⇔ (¬q ⇒ ¬p)) == "⊤"
-- the duplicate-class quirk: `p ∧ (p ∧ q)` has four classes, `(p ∧ q) ∧ p` three
#guard (truthtable p q in p &&& (p &&& q)).classes.size == 4
#guard (truthtable p q in (p &&& q) &&& p).classes.size == 3
#guard (truthtable p q in TruthTable.Clean.and p (TruthTable.Clean.and p q)).classes.size == 3

/-! ## Oracle goldens -/

/-- Parse the JSON expression encoding `["op", args...]` of `gen.jl`. -/
partial def parseExpr (N : Nat) (j : Lean.Json) : TestM (Formula N) := do
  let a ← jArr j
  let op ← jStr a[0]!
  match op with
  | "var" =>
    let m ← jNat a[1]!
    if h : m < N then return .var ⟨m, h⟩ else throw <| IO.userError "var out of range"
  | "not" => return .not (← parseExpr N a[1]!)
  | _ =>
    let x ← parseExpr N a[1]!
    let y ← parseExpr N a[2]!
    match op with
    | "and" => return .and x y
    | "or" => return .or x y
    | "imp" => return .imp x y
    | "rimp" => return .rimp x y
    | "iff" => return .iff x y
    | _ => throw <| IO.userError s!"unknown op {op}"

def names : Array String := #["p", "q", "r", "s", "t", "u"]

def truthvalues : TestM Unit := do
  let j ← readJson "oracle/golden/demorgan/truthvalues.json"
  for c in ← gArr j "tv" do
    let N ← gNat c "N"
    let p := TruthValues.ofNat N (← gNat c "p")
    let q := TruthValues.ofNat N (← gNat c "q")
    let lbl := s!"N={N} p={p.toNat} q={q.toNat}"
    checkEq s!"{lbl} ¬" p.not.toNat (← gNat c "not")
    checkEq s!"{lbl} ∧" (AbstractLattices.wedge p q).toNat (← gNat c "and")
    checkEq s!"{lbl} ∨" (AbstractLattices.vee p q).toNat (← gNat c "or")
    checkEq s!"{lbl} &" (p &&& q).toNat (← gNat c "amp")
    checkEq s!"{lbl} |" (p ||| q).toNat (← gNat c "bar")
    checkEq s!"{lbl} →" (p ⇒ q).toNat (← gNat c "imp")
    checkEq s!"{lbl} ←" (p ⇐ q).toNat (← gNat c "rimp")
    checkEq s!"{lbl} ↔" (p ⇔ q).toNat (← gNat c "iff")
    checkEq s!"{lbl} ⊥∨p" (TruthValues.bot ||| p).toNat (← gNat c "bot_or")
    checkEq s!"{lbl} p∧⊤" (p &&& TruthValues.top).toNat (← gNat c "and_top")
    checkEq s!"{lbl} ⊤→p" (TruthValues.top ⇒ p).toNat (← gNat c "top_imp")
    checkEq s!"{lbl} p←⊥" (p ⇐ TruthValues.bot).toNat (← gNat c "rimp_bot")
    checkEq s!"{lbl} p↔⊤" (p ⇔ TruthValues.top).toNat (← gNat c "iff_top")
    checkEq s!"{lbl} show" (toString p) (← gStr c "show")
  for c in ← gArr j "select" do
    let n ← gNat c "n"
    let N ← gNat c "N"
    checkEq s!"select {n} {N}" (select n N).toNat (← gNat c "value")
  for c in ← gArr j "bools" do
    let bits := (← jBools (← jField c "bits")).toList
    checkEq s!"TruthValues{bits}" (TruthValues.ofBools bits).toNat (← gNat c "value")
    checkEq s!"¬TruthValues{bits}" (TruthValues.ofBools bits).not.toNat (← gNat c "not")
  let misc ← jField j "misc"
  checkEq "!⊥" (toString (TruthValues.bot : TruthValues 0).not) (← gStr misc "not_bot")
  checkEq "!⊤" (toString (TruthValues.top : TruthValues 0).not) (← gStr misc "not_top")
  checkEq "⊥" (toString (TruthValues.bot : TruthValues 0)) (← gStr misc "bot")
  checkEq "⊤" (toString (TruthValues.top : TruthValues 0)) (← gStr misc "top")

def truthtables : TestM Unit := do
  let j ← readJson "oracle/golden/demorgan/truthtable.json"
  for c in ← gArr j "tables" do
    let N ← gNat c "N"
    let φ ← parseExpr N (← jField c "expr")
    let vars : Fin N → TruthTable N := fun m => TruthTable.proj N m (names[m.val]!)
    let t := TruthTable.ofFormula vars φ
    let lbl := s!"N={N} {(← gStr c "str")}"
    checkEq s!"{lbl} cols" (t.classes.map (·.col.toNat)) (← gNats c "cols")
    checkEq s!"{lbl} names" (t.classes.map (·.names))
      (← (← gArr c "names").mapM jStrs)
    checkEq s!"{lbl} i" (t.i + 1) (← gNat c "i")
    checkEq s!"{lbl} j" (t.j + 1) (← gNat c "j")
    checkEq s!"{lbl} str" (toString t) (← gStr c "str")
    match (← jField c "render").getStr? with
    | .ok r => checkEq s!"{lbl} render" (TruthTable.render t) r
    | .error _ => pure ()
    -- semantics: the fixed merge always points at the formula's column
    let tc := TruthTable.ofFormulaClean vars φ
    checkEq s!"{lbl} clean value" tc.value.toNat φ.tv.toNat
    -- the fixed merge never duplicates a column
    let cols := tc.classes.map (·.col.toNat)
    check s!"{lbl} clean nodup" (cols.toList.eraseDups.length == cols.size)

def parstrings : TestM Unit := do
  let j ← readJson "oracle/golden/demorgan/parstring.json"
  for c in ← gArr j "cases" do
    let s ← gStr c "s"
    checkEq s!"parstring {s}" (TruthTable.parstring s) (← gStr c "out")

/-- Suite entry point for the `lake test` driver. -/
def run : IO (Nat × Nat) := runSuite "DeMorgan" (do truthvalues; truthtables; parstrings)

end Tests.DeMorgan
