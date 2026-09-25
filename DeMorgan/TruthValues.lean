import AbstractLattices

/-!
# Truth values: bit-parallel truth-table columns

Julia source: `DeMorgan.jl src/DeMorgan.jl` (DM). `TruthValues{N}` (DM:31-33) is one
column of a truth table over `N` propositional variables: row `k ∈ [0, 2^N)` is bit `k`
of a `UInt`. The connectives are bitwise (DM:48-58).

Lean design:
* `TruthValues N` wraps a `BitVec (2 ^ N)`. The row count is in the type, so columns of
  different `N` cannot be mixed (Julia enforces this by dispatch, DM:48-54) and the
  column is always masked. Julia stores a 64-bit `UInt` and is limited to `N ≤ 6`; here
  any `N` works, and `N ≤ 6` agrees with Julia bit for bit.
* Julia's N-polymorphic contradiction `⊥ = TruthValues{0}(0)` and singleton tautology `⊤`
  (DM:39-46), with their lifting rules (DM:148-153), become the implicit-`N` constants
  `TruthValues.bot`/`TruthValues.top`: the lifting is done by elaboration.
* `∧`/`∨` are instances of the AbstractLattices classes (as in Julia, where DeMorgan
  extends `AbstractLattices.wedge`/`vee`, DM:26), plus `&&&`/`|||` (Julia `&`/`|`,
  DM:50-51). Negation and the arrows get scoped notation `¬`, `⇒`, `⇐`, `⇔` (Julia `¬`,
  `-->`, `<--`, `<-->`; `-->` cannot be a Lean token since `--` starts a comment).

The semantic bridge (`Formula`, `row`, `Formula.isTautology_iff`) proves that this
bit-parallel evaluation is a sound and complete tautology checker.
-/

namespace DeMorgan

open AbstractLattices

/-- The truth-table column with bit `k` equal to `f k`, for the `2^N` rows. -/
def column (N : Nat) (f : Nat → Bool) : BitVec (2 ^ N) :=
  (BitVec.ofBoolListLE ((List.range (2 ^ N)).map f)).cast (by simp)

@[simp] theorem getLsbD_column (N : Nat) (f : Nat → Bool) (k : Nat) :
    (column N f).getLsbD k = (decide (k < 2 ^ N) && f k) := by
  simp only [column, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD]
  by_cases h : k < 2 ^ N <;> simp [h]

/-- Julia `TruthValues{N}` (DM:31-33): a column of `2^N` truth values, row `k` = bit `k`. -/
structure TruthValues (N : Nat) where
  /-- The column; bit `k` is the value on row `k`. -/
  bits : BitVec (2 ^ N)
  deriving DecidableEq

namespace TruthValues

variable {N : Nat}

/-- Julia `tautology(N) = UInt(1)<<(1<<N)-UInt(1)` (DM:100): all rows set. Julia's
`<<` by ≥ 64 gives 0, so `N = 6` still yields all ones; here the width is exact. -/
def mask (N : Nat) : BitVec (2 ^ N) := BitVec.allOnes _

/-- The contradiction `⊥` (Julia `⊥ = TruthValues{0}(0)`, DM:39), at any `N`
(Julia's lifting rule `op(TV{0}, TV{N})`, DM:150-151). -/
def bot : TruthValues N := ⟨0⟩

/-- The tautology `⊤` (Julia `⊤ = Tautology()`, DM:43-44), lifted to `N` rows
(DM:152-153). -/
def top : TruthValues N := ⟨mask N⟩

/-- The value on row `k` (`false` outside `[0, 2^N)`). -/
@[inline] def eval (p : TruthValues N) (k : Nat) : Bool := p.bits.getLsbD k

/-- Julia `TruthValues(p::Bool...)` (DM:37): packs the arguments as bits, argument 1
at bit 0. **Julia's `N` is the number of arguments** (not log₂ of the row count), which
this signature reproduces: `ofBools [false, true, true, false] = TruthValues{4}(6)`. -/
def ofBools (ps : List Bool) : TruthValues ps.length :=
  ⟨column ps.length fun k => ps.getD k false⟩

/-- Build a column from its natural-number encoding (bits beyond `2^N` are dropped). -/
def ofNat (N : Nat) (n : Nat) : TruthValues N := ⟨BitVec.ofNat _ n⟩

/-- The column as a natural number (Julia `p.p`). -/
@[inline] def toNat (p : TruthValues N) : Nat := p.bits.toNat

/-- Julia `wedge(p, q) = TruthValues{N}(p.p & q.p)` (DM:48). -/
@[inline] def and (p q : TruthValues N) : TruthValues N := ⟨p.bits &&& q.bits⟩
/-- Julia `vee(p, q) = TruthValues{N}(p.p | q.p)` (DM:49). -/
@[inline] def or (p q : TruthValues N) : TruthValues N := ⟨p.bits ||| q.bits⟩
/-- Julia `!(p) = TruthValues{N}(p.p ⊻ tautology(N))` (DM:55); `!⊥ = ⊤`, `!⊤ = ⊥`
(DM:56-57). -/
@[inline] def not (p : TruthValues N) : TruthValues N := ⟨p.bits ^^^ mask N⟩
/-- Julia `p --> q = ¬p ∨ q` (DM:52). -/
@[inline] def imp (p q : TruthValues N) : TruthValues N := p.not.or q
/-- Julia `p <-- q = p ∨ ¬q` (DM:53). -/
@[inline] def rimp (p q : TruthValues N) : TruthValues N := p.or q.not
/-- Julia `p <--> q = (p --> q) ∧ (q --> p)` (DM:54). -/
@[inline] def iff (p q : TruthValues N) : TruthValues N := (p.imp q).and (q.imp p)

instance : HWedge (TruthValues N) (TruthValues N) (TruthValues N) := ⟨and⟩
instance : HVee (TruthValues N) (TruthValues N) (TruthValues N) := ⟨or⟩
/-- Julia `&` (DM:50). -/
instance : AndOp (TruthValues N) := ⟨and⟩
/-- Julia `|` (DM:51). -/
instance : OrOp (TruthValues N) := ⟨or⟩
instance : Complement (TruthValues N) := ⟨not⟩

/-- Julia `show`: `TruthValues{0}` prints `⊥` (DM:41) and `Tautology` prints `⊤` (DM:46);
other columns use the default struct show `TruthValues{N}(0x…)` with a 64-bit hex
payload **[run]** (port-notes §5.3). -/
protected def toString (p : TruthValues N) : String :=
  if N = 0 then (if p.toNat = 0 then "⊥" else "⊤")
  else
    let digits := max 16 ((2 ^ N + 3) / 4)
    let h := String.ofList (Nat.toDigits 16 p.toNat)
    s!"TruthValues\{{N}}(0x{String.ofList (List.replicate (digits - h.length) '0')}{h})"

instance : ToString (TruthValues N) := ⟨TruthValues.toString⟩
instance : Repr (TruthValues N) := ⟨fun p _ => TruthValues.toString p⟩

/-! ### Laws -/

@[ext] theorem ext {p q : TruthValues N} (h : ∀ k, k < 2 ^ N → p.eval k = q.eval k) : p = q := by
  cases p; cases q; congr 1; exact BitVec.eq_of_getLsbD_eq h

@[simp] theorem eval_and (p q : TruthValues N) (k : Nat) :
    (p.and q).eval k = (p.eval k && q.eval k) := BitVec.getLsbD_and
@[simp] theorem eval_or (p q : TruthValues N) (k : Nat) :
    (p.or q).eval k = (p.eval k || q.eval k) := BitVec.getLsbD_or
@[simp] theorem eval_not (p : TruthValues N) (k : Nat) :
    p.not.eval k = (decide (k < 2 ^ N) && !p.eval k) := by
  simp only [not, eval, mask, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes]
  by_cases h : k < 2 ^ N
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt h)]
@[simp] theorem eval_bot (k : Nat) : (bot : TruthValues N).eval k = false := by
  simp [bot, eval]
@[simp] theorem eval_top (k : Nat) : (top : TruthValues N).eval k = decide (k < 2 ^ N) := by
  simp [top, eval, mask]

theorem eval_of_ge (p : TruthValues N) {k : Nat} (h : 2 ^ N ≤ k) : p.eval k = false :=
  BitVec.getLsbD_of_ge _ _ h

/-- Involution of negation (Julia `¬¬p == p` for masked columns; always true here). -/
@[simp] theorem not_not (p : TruthValues N) : p.not.not = p := by
  ext k hk; simp [hk]

/-- De Morgan's law `¬(p ∧ q) = ¬p ∨ ¬q`. -/
theorem not_and (p q : TruthValues N) : (p.and q).not = p.not.or q.not := by
  ext k hk; simp [hk, Bool.not_and]

/-- De Morgan's law `¬(p ∨ q) = ¬p ∧ ¬q`. -/
theorem not_or (p q : TruthValues N) : (p.or q).not = p.not.and q.not := by
  ext k hk; simp [hk, Bool.not_or]

/-- `p ↔ q` is the rowwise equality of columns. -/
theorem eval_iff (p q : TruthValues N) (k : Nat) (hk : k < 2 ^ N) :
    (p.iff q).eval k = (p.eval k == q.eval k) := by
  simp only [iff, imp, eval_and, eval_or, eval_not, hk, decide_true, Bool.true_and]
  cases p.eval k <;> cases q.eval k <;> rfl

/-- The truth values form a distributive lattice under the AbstractLattices classes
(in fact a Boolean algebra, by `not_and`/`not_or`/`not_not`). -/
instance : LawfulDistribLattice (TruthValues N) where
  wedge_comm p q := by ext k; simp [wedge, Bool.and_comm]
  vee_comm p q := by ext k; simp [vee, Bool.or_comm]
  wedge_assoc p q r := by ext k; simp [wedge, Bool.and_assoc]
  vee_assoc p q r := by ext k; simp [vee, Bool.or_assoc]
  wedge_vee_self p q := by
    ext k; simp only [wedge, vee, eval_and, eval_or]; cases p.eval k <;> cases q.eval k <;> rfl
  vee_wedge_self p q := by
    ext k; simp only [wedge, vee, eval_and, eval_or]; cases p.eval k <;> cases q.eval k <;> rfl
  wedge_vee_distrib p q r := by ext k; simp [wedge, vee, Bool.and_or_distrib_left]

end TruthValues

/-! ## Projections (DM:80-91) -/

/-- Julia `select(n, N)` (DM:80-83): the column that is true on the rows whose bit
`n-1` is zero, `n` being 1-based. Examples **[run]**: `select 1 2 = 0b0101`,
`select 2 2 = 0b0011`. -/
def select (n N : Nat) : BitVec (2 ^ N) := column N fun k => !k.testBit (n - 1)

/-- The row assignment of the Julia truth table: variable `m` (0-based, declared
`m+1`-th in `@truthtable`) is true on row `k` iff bit `N-1-m` of `k` is zero. Row 0 is
all-true and the first variable varies slowest (port-notes §3.3). -/
def row (N : Nat) (k : Nat) (m : Fin N) : Bool := !k.testBit (N - 1 - m)

/-- The projection column of variable `m`: Julia's `@truthtable` binds variable `m+1`
of `N` to `select(N - m, N)` (DM:89). -/
def TruthValues.proj {N : Nat} (m : Fin N) : TruthValues N := ⟨select (N - m) N⟩

@[simp] theorem TruthValues.eval_proj {N : Nat} (m : Fin N) (k : Nat) :
    (TruthValues.proj m).eval k = (decide (k < 2 ^ N) && row N k m) := by
  simp only [TruthValues.proj, TruthValues.eval, select, getLsbD_column, row]
  congr 3
  omega

/-! ## Formulas: the semantics behind the bit-parallel columns -/

/-- Propositional formulas over `N` variables (the expressions DeMorgan evaluates). -/
inductive Formula (N : Nat) where
  /-- variable `m` (0-based declaration order) -/
  | var (m : Fin N)
  /-- `⊥` -/
  | bot
  /-- `⊤` -/
  | top
  /-- `¬φ` -/
  | not (φ : Formula N)
  /-- `φ ∧ ψ` -/
  | and (φ ψ : Formula N)
  /-- `φ ∨ ψ` -/
  | or (φ ψ : Formula N)
  /-- `φ → ψ` (Julia `-->`) -/
  | imp (φ ψ : Formula N)
  /-- `φ ← ψ` (Julia `<--`) -/
  | rimp (φ ψ : Formula N)
  /-- `φ ↔ ψ` (Julia `<-->`) -/
  | iff (φ ψ : Formula N)
  deriving DecidableEq, Repr

namespace Formula

variable {N : Nat}

/-- Evaluate a formula under an assignment. -/
def eval (ρ : Fin N → Bool) : Formula N → Bool
  | var m => ρ m
  | bot => false
  | top => true
  | not φ => !φ.eval ρ
  | and φ ψ => φ.eval ρ && ψ.eval ρ
  | or φ ψ => φ.eval ρ || ψ.eval ρ
  | imp φ ψ => !φ.eval ρ || ψ.eval ρ
  | rimp φ ψ => φ.eval ρ || !ψ.eval ρ
  | iff φ ψ => φ.eval ρ == ψ.eval ρ

/-- Bit-parallel evaluation: the whole truth-table column at once, with the Julia
connectives (DM:48-58). -/
def tv : Formula N → TruthValues N
  | var m => TruthValues.proj m
  | bot => TruthValues.bot
  | top => TruthValues.top
  | not φ => φ.tv.not
  | and φ ψ => φ.tv.and ψ.tv
  | or φ ψ => φ.tv.or ψ.tv
  | imp φ ψ => φ.tv.imp ψ.tv
  | rimp φ ψ => φ.tv.rimp ψ.tv
  | iff φ ψ => φ.tv.iff ψ.tv

/-- **Soundness of the columns**: row `k` of the bit-parallel column is the formula's
value under the row-`k` assignment. -/
theorem eval_tv (φ : Formula N) (k : Nat) (hk : k < 2 ^ N) :
    φ.tv.eval k = φ.eval (row N k) := by
  induction φ with
  | var m => simp [tv, eval, hk]
  | bot => simp [tv, eval]
  | top => simp [tv, eval, hk]
  | not φ ih => simp [tv, eval, hk, ih]
  | and φ ψ ih₁ ih₂ => simp [tv, eval, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ => simp [tv, eval, ih₁, ih₂]
  | imp φ ψ ih₁ ih₂ => simp [tv, eval, TruthValues.imp, hk, ih₁, ih₂]
  | rimp φ ψ ih₁ ih₂ => simp [tv, eval, TruthValues.rimp, hk, ih₁, ih₂]
  | iff φ ψ ih₁ ih₂ => rw [tv, TruthValues.eval_iff _ _ _ hk, ih₁, ih₂]; rfl

/-- The row index of an assignment (inverse of `row`). -/
def rowIndex : {N : Nat} → (Fin N → Bool) → Nat
  | 0, _ => 0
  | N + 1, ρ => (if ρ 0 then 0 else 2 ^ N) + rowIndex fun m => ρ m.succ

theorem rowIndex_lt : ∀ {N : Nat} (ρ : Fin N → Bool), rowIndex ρ < 2 ^ N
  | 0, _ => by simp [rowIndex]
  | N + 1, ρ => by
    have := rowIndex_lt fun m : Fin N => ρ m.succ
    simp only [rowIndex, Nat.pow_succ]
    split <;> omega

/-- Every assignment is some row of the truth table. -/
theorem row_rowIndex : ∀ {N : Nat} (ρ : Fin N → Bool), row N (rowIndex ρ) = ρ
  | 0, ρ => funext fun m => m.elim0
  | N + 1, ρ => by
    funext m
    have hlt := rowIndex_lt fun m : Fin N => ρ m.succ
    have ih := congrFun (row_rowIndex fun m : Fin N => ρ m.succ)
    simp only [row, rowIndex] at ih ⊢
    cases m using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
      split
      · next h => simp [Nat.testBit_lt_two_pow hlt, h]
      · next h => simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, h]
    | succ m =>
      have hm : N + 1 - 1 - (m.succ : Fin (N + 1)).val = N - 1 - m.val := by simp; omega
      rw [hm, ← ih m]
      split
      · simp
      · rw [Nat.testBit_two_pow_add_gt (by omega)]

/-- **DeMorgan decides tautologies**: a formula's bit-parallel column is `⊤` exactly
when the formula is true under every assignment. -/
theorem tv_eq_top_iff (φ : Formula N) : φ.tv = TruthValues.top ↔ ∀ ρ, φ.eval ρ = true := by
  constructor
  · intro h ρ
    have := eval_tv φ (rowIndex ρ) (rowIndex_lt ρ)
    rw [row_rowIndex, h, TruthValues.eval_top] at this
    simpa [rowIndex_lt ρ] using this.symm
  · intro h
    ext k hk
    rw [eval_tv φ k hk, h, TruthValues.eval_top]
    simp [hk]

/-- Decidable tautology test via one bit-parallel evaluation. -/
def isTautology (φ : Formula N) : Bool := φ.tv == TruthValues.top

theorem isTautology_iff (φ : Formula N) : φ.isTautology = true ↔ ∀ ρ, φ.eval ρ = true := by
  simp [isTautology, tv_eq_top_iff]

end Formula

end DeMorgan
