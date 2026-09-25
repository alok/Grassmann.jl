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
open Tests.Golden in
initialize register
  { name := "grassmann/arith", suite := "arith", op := "add|sub|neg",
    eval := fun ctx args => … }
```

The module must be imported by the test driver (`Tests.lean`) so that its initializer
runs; `Tests.Golden.run` then picks the registration up. Later registrations take
precedence over earlier ones (and over the built-in evaluators); the first registration whose
evaluator returns `some` decides the case. `runWith` takes an explicit list instead.
-/

namespace Tests.Golden

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

/-- A registered evaluator. -/
structure Registration where
  /-- Name used in reports. -/
  name : String
  /-- Suite glob (`|` alternatives, `*`). -/
  suite : String := "*"
  /-- Op glob. -/
  op : String := "*"
  /-- The evaluator. -/
  eval : Evaluator
  /-- The aspects compared. -/
  aspects : Aspects := {}
  /-- A documented Float tolerance `(rtol, atol)` for kernels that sum in a different order
  than Julia (schema §11 rule 3; default bitwise). The composite suite always uses the
  shard's `tolerance` table. -/
  floatTol : Option (Float × Float) := none
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

/-- Evaluate a case with the first applicable registration that returns a result. -/
def evaluate (regs : Array Registration) (ctx : EvalCtx) (args : Array GoldenElem) :
    Option (Registration × GoldenElem) :=
  regs.findSome? fun r => (r.eval ctx args).map (r, ·)

end Tests.Golden
