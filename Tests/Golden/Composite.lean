import Tests.Golden.Registry
import Grassmann.Composite

/-!
# The composite-suite evaluator (`oracle/golden/composite/*.json`)

Evaluates the composite suite (docs/port-notes/oracle-schema.md §8.5) with
`Grassmann.Composite`: every operand is decoded from its dense `Float64` vector into the
typed container of its kind (`Single`, `Chain`, `Spinor`, `CoSpinor`, `Multivector`,
`Couple`, `PseudoCouple`) over the shard's space, the typed function of the op runs,
and the result's dense vector is returned. The runner compares it with Julia's under
the op's tolerance (`‖Δ‖₂ ≤ atol + rtol·max(‖out‖₂, ‖expect‖₂)`); result kinds and
strings are informational in this suite (§11 rule 2).

| op | computed by |
|---|---|
| `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`, `sinh`, `cosh` | the typed functions of the operand's kind (`Single.exp`, `Chain.log?`, `Half.cos`, …) |
| `inv` | `Single.inv`, `Chain.inv`, `Couple.inv`, `Half.inv?`, `Multivector.inv?` |
| `div` | `a ⟑ inv(b)`; two couples on one blade divide as couples (Julia's robust division) |
| `pow` | `Single.pow`, `Chain.pow`, `Couple.pow`, `Half.pow`, `Multivector.pow` |

Where Julia throws (`inv(m) is undefined`), the `?` functions return `none` and the
evaluator reports a rejection (schema §11 rule 5).

Known issues (expected failures, see `compositeKnownIssues`):

* `exp-nilpotent-couple`: Julia's `exp` of a couple whose blade squares to zero returns
  `eᵃ(1 + t)` instead of `eᵃ(1 + bB)` (port-notes/grassmann-composite.md §8.3 item 1;
  `exp(1.0 + 0.25v∞)` in `CGA3` is `5.44 + 0.68v∞` in Julia, `2.72 + 0.68v∞` here). The
  port fixes it; the golden is not yet tagged (integrator request: a `skip` defect in
  `oracle/defects.toml`).
* `norm2-infinite`: the composite comparator takes `‖out − expect‖₂` of equal infinite
  coefficients as `NaN` (`inv(0.7v∞) = Inf·v∞` in `CGA3` agrees exactly); integrator
  request for `Tests/Golden/Scalar.lean`.
-/

namespace Tests.ElementOracle.CompositeEval

open Tests.ElementOracle Grassmann DirectSum DirectSum.Bits StaticVectors AbstractTensors Composite

/-- A decoded composite operand in the typed layer. -/
inductive Operand (V : TensorBundle) where
  /-- A scaled blade of grade `g` (Julia `Single`, `Submanifold`, `One`). -/
  | single (g : Nat) (s : Single V g Float)
  /-- A chain of grade `g`. -/
  | chain (g : Nat) (c : Chain V g Float)
  /-- A spinor. -/
  | spinor (s : Half V false Float)
  /-- A co-spinor. -/
  | cospinor (s : Half V true Float)
  /-- A multivector. -/
  | multi (m : Multivector V Float)
  /-- A couple. -/
  | couple (z : Couple V Float)
  /-- A pseudo-couple. -/
  | pseudo (z : PseudoCouple V Float)

variable {V : TensorBundle}

/-- The dense `Float64` coefficients of an element. -/
def floats? (e : GoldenElem) : Option FloatArray :=
  match e.dense with
  | some (.float v) => some v
  | _ => none

/-- Decode a composite input (every input of the suite is a `Float64` element). -/
def decode (V : TensorBundle) (e : GoldenElem) : Option (Operand V) := do
  let d ← floats? e
  if d.size != 2 ^ V.n then none
  let at_ := fun (b : UInt64) => d[Leibniz.basisRank V.n b]!
  let mv : Multivector V Float := ⟨Values.ofFn fun i => d[i.1]!⟩
  match e.kind with
  | .single | .submanifold | .one =>
    let b := e.bits.getD 0
    some (.single (popcount b) ⟨b, at_ b⟩)
  | .chain => do
    let g ← e.grade
    some (.chain g ⟨convertLayout V.n .full (.chain g) mv.v⟩)
  | .spinor => some (.spinor (mv.half false))
  | .cospinor => some (.cospinor (mv.half true))
  | .multivector => some (.multi mv)
  | .couple => do
    let b ← e.bits
    some (.couple ⟨b, d[0]!, if b == 0 then 0 else at_ b⟩)
  | .pseudoCouple => do
    let b ← e.bits
    let top := lowMask V.n
    some (.pseudo ⟨b, at_ b, if b == top then 0 else at_ top⟩)
  | _ => none

/-- The operand as a multivector. -/
def Operand.mv : Operand V → Multivector V Float
  | .single _ s => toMultivector s
  | .chain _ c => toMultivector c
  | .spinor s => toMultivector s
  | .cospinor s => toMultivector s
  | .multi m => m
  | .couple z => z.toMultivector
  | .pseudo z => z.toMultivector

/-- A typed result as a golden element (dense `Float64` values only). -/
def result (m : Multivector V Float) : GoldenElem :=
  { kind := .multivector, T := some .float64, dense := some (.float m.v.data) }

/-- A rejection (Julia throws for these operands). -/
def rejected : GoldenElem := GoldenElem.rejected "ErrorException" "inv(m) is undefined"

/-- An optional result (`none` is a rejection). -/
def resultOpt : Option (Multivector V Float) → GoldenElem
  | some m => result m
  | none => rejected

variable [Kernels V]

/-- Julia `inv(a)` of an operand, or `none` where Julia throws. -/
def inv? : Operand V → Option (Multivector V Float)
  | .single _ s => some (toMultivector s.inv)
  | .chain _ c => some (toMultivector c.inv)
  | .spinor s => s.inv?.map toMultivector
  | .cospinor s => s.inv?.map toMultivector
  | .multi m => m.inv?
  | .couple z => some z.inv.toMultivector
  | .pseudo z => (toMultivector z).inv?

/-- The typed unary op of a key. -/
def unary (op : String) (a : Operand V) : Option GoldenElem :=
  match op, a with
  | "exp", .single _ s => some (result s.exp.toMultivector)
  | "exp", .chain _ c => some (result c.exp)
  | "exp", .spinor s => some (result (toMultivector s.exp))
  | "exp", .cospinor s => some (result (CoSpinor.exp s))
  | "exp", .multi m => some (result m.exp)
  | "exp", .couple z => some (result z.exp.toMultivector)
  | "exp", .pseudo z => some (result z.exp)
  | "log", .single _ s => some (result s.log.toMultivector)
  | "log", .chain _ c => some (resultOpt c.log?)
  | "log", .spinor s => some (resultOpt (s.log?.map toMultivector))
  | "log", .cospinor s => some (resultOpt (Multivector.log? (toMultivector s)))
  | "log", .multi m => some (resultOpt m.log?)
  | "log", .couple z => some (result z.log.toMultivector)
  | "log", .pseudo z => some (result z.log)
  | "sqrt", .single _ s => some (result s.sqrt.toMultivector)
  | "sqrt", .chain _ c => some (resultOpt c.sqrt?)
  | "sqrt", .spinor s => some (resultOpt (s.sqrt?.map toMultivector))
  | "sqrt", .cospinor s => some (result (CoSpinor.sqrt s))
  | "sqrt", .multi m => some (resultOpt m.sqrt?)
  | "sqrt", .couple z => some (result z.sqrt.toMultivector)
  | "cosh", .single _ s => some (result (toMultivector s.cosh))
  | "cosh", .chain _ c => some (result (toMultivector c.cosh))
  | "cosh", .spinor s => some (result (toMultivector s.cosh))
  | "cosh", .cospinor s => some (result (CoSpinor.cosh s))
  | "cosh", .multi m => some (result m.cosh)
  | "cosh", .couple z => some (result z.cosh.toMultivector)
  | "cosh", .pseudo z => some (result z.cosh)
  | "sinh", .single _ s => some (result (toMultivector s.sinh))
  | "sinh", .chain _ c => some (result (toMultivector c.sinh))
  | "sinh", .spinor s => some (result (toMultivector s.sinh))
  | "sinh", .cospinor s => some (result (CoSpinor.sinh s))
  | "sinh", .multi m => some (result m.sinh)
  | "sinh", .couple z => some (result z.sinh.toMultivector)
  | "sinh", .pseudo z => some (result z.sinh)
  | "cos", .single _ s => some (result (toMultivector s.cos))
  | "cos", .chain _ c => some (result (toMultivector c.cos))
  | "cos", .spinor s => some (result (toMultivector s.cos))
  | "cos", .cospinor s => some (result (CoSpinor.cos s))
  | "cos", .multi m => some (result m.cos)
  | "cos", .couple z => some (result z.cos)
  | "cos", .pseudo z => some (result z.cos)
  | "sin", .single _ s => some (result (toMultivector s.sin))
  | "sin", .chain _ c => some (result (toMultivector c.sin))
  | "sin", .spinor s => some (result (toMultivector s.sin))
  | "sin", .cospinor s => some (result (CoSpinor.sin s))
  | "sin", .multi m => some (result m.sin)
  | "sin", .couple z => some (result z.sin)
  | "sin", .pseudo z => some (result z.sin)
  | "tan", .single _ s => some (result (toMultivector s.tan))
  | "tan", .chain _ c =>
    some (if (Half.inv? c.cos).isSome then result (toMultivector c.tan) else rejected)
  | "tan", .spinor s => some (if (Half.inv? s.cos).isSome then result (toMultivector s.tan) else rejected)
  | "tan", .cospinor s => some (result (CoSpinor.tan s))
  | "tan", .multi m => some (result m.tan)
  | "tan", .couple z => some (result z.tan)
  | "tan", .pseudo z => some (result z.tan)
  | "inv", a => some (resultOpt (inv? a))
  | _, _ => none

/-- Julia `a / b = a ⟑ inv(b)` (two couples on one blade: the couple division). -/
def div (a b : Operand V) : GoldenElem :=
  match a, b with
  | .couple x, .couple y =>
    if x.bits == y.bits then result (Couple.divSame x y).toMultivector
    else resultOpt ((inv? b).map (x.toMultivector * ·))
  | _, _ => resultOpt ((inv? b).map (a.mv * ·))

/-- Julia `a ^ k`. -/
def pow (a : Operand V) (k : Int) : Option GoldenElem :=
  match a with
  | .single _ s => some (result (s.pow k).toMultivector)
  | .chain _ c => some (result (c.pow k))
  | .spinor s => some (result (toMultivector (s.pow k)))
  | .multi m => some (result (m.pow k))
  | .couple z => some (result (z.pow k).toMultivector)
  | _ => none

end CompositeEval

open CompositeEval in
/-- The composite evaluator: decode the operands over the shard's space, run the typed
function. -/
def compositeEval : Evaluator := fun ctx args => do
  let V ← ctx.bundle?
  let a ← args[0]? >>= decode V
  match ctx.op with
  | "div" => do
    let b ← args[1]? >>= decode V
    some (div a b)
  | "pow" => pow a (← ctx.k)
  | op => unary op a

/-- The documented expected failures of the composite evaluator (module docstring). -/
def compositeKnownIssues : Array KnownIssue := #[
  { id := "exp-nilpotent-couple"
    note := "Julia's exp(a + bB) with B² = 0 returns eᵃ(1 + t) instead of eᵃ(1 + bB) \
      (composite.jl:104, port-notes/grassmann-composite.md §8.3 item 1); fixed in \
      Grassmann.Couple.exp; the golden needs a skip defect in oracle/defects.toml"
    tables := #[{ suite := some (Glob.compile "composite"), op := some (Glob.compile "exp"),
                  kinds := some #[KindPat.compile "Couple"], when := some "null_blade" }] },
  { id := "norm2-infinite"
    note := "the composite comparator's ‖out − expect‖₂ is NaN for equal infinite \
      coefficients (inv(0.7v∞) = Inf·v∞ agrees); Tests/Golden/Scalar.lean compareCoeffs \
      should skip components that are equal"
    tables := #[{ suite := some (Glob.compile "composite"), op := some (Glob.compile "inv"),
                  kinds := some #[KindPat.compile "Single:1"], when := some "null_blade" }] }
]

/-- The composite-suite registration. -/
def compositeRegistration : Registration :=
  { name := "grassmann/composite", suite := "composite", op := "*", eval := compositeEval
    aspects := { kind := false, str := false, compact := false }
    knownIssues := compositeKnownIssues }

initialize register compositeRegistration

end Tests.ElementOracle
