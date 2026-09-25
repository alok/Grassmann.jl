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

/-! ## unary -/

/-- The dynamic unary map of an oracle op key (schema §12), `none` if not a map
evaluated here. -/
def unaryOf? (op : String) : Option (UnTA V) :=
  match op with
  | "neg" => some fun x => TA.neg x
  | "reverse" => some fun x => TA.reverse x
  | "involute" => some fun x => TA.involute x
  | "clifford" => some fun x => TA.clifford x
  | "antireverse" => some fun x => TA.antireverse x
  | "complementright" => some fun x => TA.complementright x
  | "complementleft" => some fun x => TA.complementleft x
  | "hodge" => some fun x => TA.hodge x
  | "complementlefthodge" => some fun x => TA.complementlefthodge x
  | "metric" => some fun x => TA.metric x
  | "antimetric" => some fun x => TA.antimetric x
  | "even" => some fun x => TA.even x
  | "odd" => some fun x => TA.odd x
  | "real" => some fun x => TA.realPart x
  | "imag" => some fun x => TA.imagPart x
  | "scalar" => some fun x => TA.scalar x
  | "vector" => some fun x => TA.vector x
  | "bivector" => some fun x => TA.bivector x
  | "trivector" => some fun x => TA.trivector x
  | "volume" => some fun x => TA.volume x
  | "Multivector" => some fun x => TA.toMultiTA x
  | _ =>
    if op.startsWith "grade:" then
      (op.drop 6).toString.toNat?.map fun k => fun x => TA.gradeProj k x
    else none

/-- `x'` (Julia `adjoint`): the element in the dual space with real coefficients
unchanged (`src/products.jl:943-1070`); `Zero` and `∞` stay, and a `Couple` or
`PseudoCouple`, which have no `adjoint` method, fall back to Julia's
`adjoint(x::Number) = conj(x)`, i.e. the reverse in the same space. -/
def AnyTA.adjoint (x : AnyTA V) : Option GoldenElem := do
  let k := x.encode.kind
  if k == .zero || k == .infinity then return x.encode
  if k == .couple || k == .pseudoCouple then return (x.un fun y => TA.reverse y).encode
  let W ← V.adjoint.toOption
  let e ← match x with
    | .int x => encodeTA <$> x.retarget W id
    | .rat x => encodeTA <$> x.retarget W id
    | .float x => encodeTA <$> x.retarget W id
    | _ => none
  pure { e with V := some W.showHandle }

/-- `grassmann/unary`: the unary maps, the grade projections, `Multivector(a)` and `a'`. -/
def unaryEval : Evaluator := fun ctx args => do
  let V ← ctx.bundle?
  let x ← AnyTA.decode V (← args[0]?)
  if ctx.op == "adjoint" then x.adjoint
  else match unaryOf? (V := V) ctx.op with
    | some f => pure (x.un f).encode
    | none => none

/-- Julia defects that `defects.json` (and `Tests.Golden.Pending`) do not cover yet, on
cases the dynamic layer computes correctly: the evaluator's expected failures until the
oracle tags them (integrator requests). -/
def unaryKnownIssues : Array KnownIssue := #[
  { id := "grade0-couple-coefficient",
    note := "Julia defect (extends the pending grade-couple-coefficient): grade(z::Couple, 0) " ++
      "returns the bare number realvalue(z) (src/multivectors.jl:670) instead of the scalar part " ++
      "Single{V}(realvalue(z)); the port returns the Single. Request: add grade:0 to the op glob " ++
      "of grade-couple-coefficient (Tests/Golden/Pending.lean, then oracle/defects.toml)",
    tables := #[{ suite := some (Glob.compile "unary"), op := some (Glob.compile "grade:0"),
                  out := some (Glob.compile "Number"), kinds := some #[KindPat.compile "Couple"] }] }
]

/-! ## products -/

/-- The dynamic binary product of an oracle op key (schema §12). -/
def productOf? (op : String) : Option (BinTA V) :=
  match op with
  | "mul" => some fun a b => TA.mul a b
  | "wedge" => some fun a b => TA.wedge a b
  | "vee" => some fun a b => TA.vee a b
  | "contraction" => some fun a b => TA.contraction a b
  | "lcontraction" => some fun a b => TA.lcontraction a b
  | "lshift" => some fun a b => TA.lshift a b
  | "rshift" => some fun a b => TA.rshift a b
  | "revmul" => some fun a b => TA.revmul a b
  | "scalarprod" => some fun a b => TA.scalarprod a b
  | "cross" => some fun a b => TA.cross a b
  | "sandwich" => some fun a b => TA.sandwich a b
  | "tsandwich" => some fun a b => TA.tsandwich a b
  | "veedot" => some fun a b => TA.veedot a b
  | "antidot" => some fun a b => TA.antidot a b
  | _ => none

/-- `grassmann/products`: the 14 binary products over every ordered pair. -/
def productsEval : Evaluator := fun ctx args => do
  let V ← ctx.bundle?
  let a ← AnyTA.decode V (← args[0]?)
  let b ← AnyTA.decode V (← args[1]?)
  let T ← CoeffType.promote a.T b.T
  match productOf? (V := V) ctx.op with
  | some f => (← a.bin T f b).encode
  | none => none

/-! ## Registrations -/

/-- The dynamic layer's registrations. -/
def grassmannRegistrations : Array Registration := #[
  { name := "grassmann/construct", suite := "construct", op := "construct", eval := constructEval },
  { name := "grassmann/arith", suite := "arith", op := "*", eval := arithEval },
  { name := "grassmann/unary", suite := "unary", op := "*", eval := unaryEval,
    knownIssues := unaryKnownIssues },
  { name := "grassmann/products", suite := "products", op := "*", eval := productsEval }
]

initialize
  for r in grassmannRegistrations do register r

end Tests.ElementOracle.Dyn
