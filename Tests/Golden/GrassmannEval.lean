import Tests.Golden.GrassmannDynamic

/-!
# Golden evaluators of the dynamic layer

Registrations of `Grassmann.TA` with the element-oracle harness (`Tests.Golden.Registry`):

| name | suite / ops | computes | compares |
|---|---|---|---|
| `grassmann/construct` | construct | the element from `(kind, grade, bits, T, native)` | kind, `T`, dense, `str`, `compact_str` |
| `grassmann/arith` | arith: `add sub neg mul div rdiv` | Julia's `+ - *` lattice and scalar actions (`TA.add`, `TA.addNum`, `TA.smul`, …) | kind, `T`, `grade`/`bits`, dense, `str` |

Everything is compared exactly (floats bitwise). Importing this module registers the
evaluators (the test driver must import it); `grassmannRegistrations` lists them for
`Tests.ElementOracle.runWith`.
-/

namespace Tests.ElementOracle.Dyn

open Grassmann DirectSum AbstractTensors JuliaBase

variable {V : TensorBundle}

/-! ## construct -/

/-- `grassmann/construct`: build the element and print it. -/
def constructEval : Evaluator := fun ctx args => do
  let V ← ctx.bundle?
  let x ← AnyTA.decode V (← args[0]?)
  pure x.encode

/-! ## arith -/

/-- A number converted to coefficient type `T`, applied to an element of that type. -/
def AnyTA.withNum (T : CoeffType) (x : AnyTA V) (n : AnyNum)
    (f : {α : Type} → [Coeff α] → [JuliaShow α] → [OracleScalar α] → TA V α → α → TA V α) :
    Option (AnyTA V) := do
  match ← x.promoteTo T, ← (n.toTA V).promoteTo T with
  | .int x, .int (.single _ k) => pure (.int (f x k))
  | .rat x, .rat (.single _ k) => pure (.rat (f x k))
  | .float x, .float (.single _ k) => pure (.float (f x k))
  | _, _ => none

/-- Negate an operand in its own coefficient type. -/
def DynOperand.neg : DynOperand V → DynOperand V
  | .elem x => .elem (x.un TA.neg)
  | .num (.int k) => .num (.int (-k))
  | .num (.float f) => .num (.float (-f))
  | .num (.rat q) => .num (.rat (-q))

/-- A term (`Zero`, `One`, a blade or a `Single`). -/
def AnyTA.isTerm (x : AnyTA V) : Bool :=
  match x.encode.kind with
  | .zero | .one | .submanifold | .single => true
  | _ => false

/-- A dense container result (`Chain`, `Spinor`, `CoSpinor`, `Multivector`). -/
def AnyTA.isContainer (x : AnyTA V) : Bool :=
  match x.encode.kind with
  | .chain | .spinor | .cospinor | .multivector => true
  | _ => false

/-- Promote an operand's coefficients to `T`. -/
def DynOperand.promoteTo (T : CoeffType) : DynOperand V → Option (DynOperand V)
  | .elem x => .elem <$> x.promoteTo T
  | .num (.int k) => match T with
    | .float64 => some (.num (.float (Float.ofInt k)))
    | .rational => some (.num (.rat k))
    | _ => some (.num (.int k))
  | .num n => some (.num n)

/-- Julia's `x / n` result type: integer division promotes to `Float64`. -/
def divType (T : CoeffType) : CoeffType :=
  match T with
  | .int64 | .bool => .float64
  | t => t

/-- `grassmann/arith`: `a + b`, `a - b` (with numbers: `x ± n`, `n ± x`), `-a`, `n * x`,
`x * n`, `x / n`, `x // n`. -/
def arithEval : Evaluator := fun ctx args => do
  let V ← ctx.bundle?
  let a ← DynOperand.decode V (← args[0]?)
  match ctx.op, args[1]? with
  | "neg", none => match a with
    | .elem x => pure (x.un TA.neg).encode
    | .num _ => none
  | op, some be =>
    let b ← DynOperand.decode V be
    let T ← CoeffType.promote a.T b.T
    -- Julia's `a - b` mostly negates `b` in its own coefficient type (`-value(b)`, then
    -- the container converts: `0.5 - 0v₁ = 0.5 + 0.0v₁`); the term-term container
    -- branches (`src/algebra.jl:760-779`, `$bop(value(b,$t))`) convert first.
    let isTerm := fun (o : DynOperand V) => match o with
      | .num _ => true
      | .elem x => x.isTerm
    let sum := fun (b : DynOperand V) => match a, b with
      | .elem x, .elem y => x.bin T TA.add y
      | .elem x, .num n => x.withNum T n TA.addNum
      | .num n, .elem y => y.withNum T n fun y k => TA.numAdd k y
      | _, _ => none
    let r ← match op, a, b with
      | "add", _, _ => sum b
      | "sub", _, _ => do
        let pre ← sum b.neg
        if isTerm a && isTerm b && pre.isContainer then (b.promoteTo T).bind (sum ·.neg) else pure pre
      | "mul", .num n, .elem y => y.withNum T n fun y k => TA.smul k y
      | "mul", .elem x, .num n => x.withNum T n TA.mulScalar
      | "div", .elem x, .num n => do
        match ← x.withNum (divType T) n fun x _ => x, ← (n.toTA V).promoteTo (divType T) with
        | .float x, .float (.single _ k) => pure (.float (TA.divScalar x k))
        | .rat x, .rat (.single _ k) => pure (.rat (TA.divScalar x k))
        | _, _ => none
      | "rdiv", .elem x, .num n => do
        match ← x.promoteTo .rational, ← (n.toTA V).promoteTo .rational with
        | .rat x, .rat (.single _ k) => pure (.rat (TA.divScalar x k))
        | _, _ => none
      | _, _, _ => none
    pure r.encode
  | _, _ => none

/-! ## Registrations -/

/-- The dynamic layer's registrations. -/
def grassmannRegistrations : Array Registration := #[
  { name := "grassmann/construct", suite := "construct", op := "construct", eval := constructEval },
  { name := "grassmann/arith", suite := "arith", op := "*", eval := arithEval }
]

initialize
  for r in grassmannRegistrations do register r

end Tests.ElementOracle.Dyn
