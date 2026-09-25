import Tests.Golden.Shard

/-!
# The evaluation registry

The oracle harness is library-agnostic: it knows how to load, validate and compare goldens,
but not how to compute anything. Computation is plugged in through **evaluators**: pure
functions from the decoded operands of a case to a decoded result,

```
Evaluator := EvalCtx → Array GoldenElem → Option GoldenElem
```

registered for a (suite glob, op glob) pair. `none` means "not implemented for these
operands" and counts as skipped (schema §11 rule 1); a result of kind `Error`
(`GoldenElem.rejected`) means the port rejects the operation.

The arguments are, per suite (see `GoldenCase.args`): the input elements `a`(, `b`) for
arith/products/unary/composite (`ctx.k` holds `pow`'s exponent), the output stripped to its
constructor data for construct, the bare number for floats, nothing for docs (the statement
is `ctx.case.input`).

An evaluator fills only what it computes: `dense`/`value` are compared when present, `str`
and `compact_str` when present, the kind (with `grade`/`bits`) when `Aspects.kind` is set.
Comparison rules are those of schema §11 (`Tests.Golden.Compare`).

**Registering from another module** (e.g. the Grassmann dynamic layer):

```
import Tests.Golden.Registry
open Tests.ElementOracle in
initialize register
  { name := "grassmann/arith", suite := "arith", op := "add|sub|neg",
    eval := fun ctx args => … }
```

An evaluator that needs per-space tables (kernel plans, label tables) sets `prepare`
instead: it is called once per (shard, op) with the shard's space and returns the evaluator
for that shard's cases, wrapped in `Prepared`:

```
prepare := fun p =>
  let table := buildTable p.space   -- computed once per (shard, op)
  ⟨fun ctx args => … table …⟩
```

The wrapper is load-bearing: a definition whose result type is a bare function type is
eta-expanded by the compiler, which moves `let table := …` under the lambda and rebuilds the
table on every call (measured 40× slower on the products suite).

The module must be imported by the test driver (`Tests.lean`) so that its initializer
runs; `Tests.Golden.run` then picks the registration up. Later registrations take
precedence over earlier ones (and over the built-in evaluators); the first registration whose
evaluator returns `some` decides the case. `runWith` takes an explicit list instead.
-/

namespace Tests.ElementOracle

open Lean

/-- What an evaluator sees besides its arguments. -/
structure EvalCtx where
  /-- Suite name. -/
  suite : String
  /-- Shard name. -/
  shard : String
  /-- The op key (`construct`, `docs`, `show` for floats). -/
  op : String
  /-- The shard's space descriptor (per-space suites). -/
  space : Option SpaceDesc := none
  /-- `pow`'s exponent (composite). -/
  k : Option Int := none
  /-- The raw case record (labels, sources, docs statements). -/
  case : GoldenCase := default
  deriving Inhabited

/-- The shard space as a `DirectSum.TensorBundle`. -/
def EvalCtx.bundle? (c : EvalCtx) : Option DirectSum.TensorBundle := c.space.map (·.bundle)

/-- An evaluator: operands ↦ result, `none` when not implemented for them. -/
abbrev Evaluator := EvalCtx → Array GoldenElem → Option GoldenElem

/-- A prepared evaluator. Returning this structure (rather than a bare `Evaluator`) from a
factory keeps the factory's precomputation outside the evaluator closure (see the module
docstring). -/
structure Prepared where
  /-- The evaluator for one (shard, op). -/
  eval : Evaluator

instance : Inhabited Prepared := ⟨⟨fun _ _ => none⟩⟩

/-- What an evaluator factory sees: one (shard, op) pair. -/
structure PrepCtx where
  /-- Suite name. -/
  suite : String
  /-- Shard name. -/
  shard : String
  /-- The shard's space descriptor (per-space suites). -/
  space : Option SpaceDesc := none
  /-- The op key. -/
  op : String
  deriving Inhabited

/-- Which parts of a result are compared (each only when the result provides it). -/
structure Aspects where
  /-- The kind tag, `T`, `grade` and `bits` (schema §11 rule 2). -/
  kind : Bool := true
  /-- `dense` (or a Number's `value`) (rule 3). -/
  values : Bool := true
  /-- `str` (rule 4). -/
  str : Bool := true
  /-- `compact_str` (rule 4). -/
  compact : Bool := true
  deriving Inhabited, Repr

/-- A documented disagreement of an evaluator with the goldens: cases it matches that fail
are counted as expected failures (`xfail`) instead of failures, and cases that pass as
`xpass`. For discrepancies that belong to the library under test (not to Julia: those are
defects); each needs an owner and an integrator request. -/
structure KnownIssue where
  /-- Short id. -/
  id : String
  /-- What is wrong and where it should be fixed. -/
  note : String
  /-- The affected cases, in the defect match language (schema §10). -/
  tables : Array MatchTable
  deriving Inhabited

/-- A registered evaluator. -/
structure Registration where
  /-- Name used in reports. -/
  name : String
  /-- Suite glob (`|` alternatives, `*`). -/
  suite : String := "*"
  /-- Op glob. -/
  op : String := "*"
  /-- The evaluator. -/
  eval : Evaluator := fun _ _ => none
  /-- Per-(shard, op) preparation, called once before the shard's cases of that op are
  evaluated: an evaluator factory that can precompute tables for the space (products plans,
  label tables). Defaults to `eval`. -/
  prepare : PrepCtx → Prepared := fun _ => ⟨eval⟩
  /-- The aspects compared. -/
  aspects : Aspects := {}
  /-- A documented Float tolerance `(rtol, atol)` for kernels that sum in a different order
  than Julia (schema §11 rule 3; default bitwise). The composite suite always uses the
  shard's `tolerance` table. -/
  floatTol : Option (Float × Float) := none
  /-- Documented expected failures of this evaluator. -/
  knownIssues : Array KnownIssue := #[]
  deriving Inhabited

/-- The global registry that other modules extend at initialization. -/
initialize registryRef : IO.Ref (Array Registration) ← IO.mkRef #[]

/-- Register an evaluator (call from an `initialize` block). -/
def register (r : Registration) : IO Unit := registryRef.modify (·.push r)

/-- Every registration made so far, in registration order. -/
def registered : IO (Array Registration) := registryRef.get

/-- The registrations applicable to a suite and op, highest precedence first. -/
def applicable (regs : Array Registration) (suite op : String) : Array Registration :=
  (regs.filter fun r => (Glob.compile r.suite).test suite && (Glob.compile r.op).test op).reverse

/-- The applicable registrations with their evaluators prepared for a shard's space and an op. -/
def prepared (regs : Array Registration) (p : PrepCtx) : Array (Registration × Evaluator) :=
  (applicable regs p.suite p.op).map fun r => (r, (r.prepare p).eval)

/-- Evaluate a case with the first prepared registration that returns a result. -/
def evaluate (regs : Array (Registration × Evaluator)) (ctx : EvalCtx) (args : Array GoldenElem) :
    Option (Registration × GoldenElem) :=
  regs.findSome? fun (r, ev) => (ev ctx args).map (r, ·)

end Tests.ElementOracle
