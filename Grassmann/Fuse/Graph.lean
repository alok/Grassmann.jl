/-
The symbolic scalar graph of expression fusion (`Grassmann.Fuse`).

An expression of the typed algebra (`R * v * ~R`, `2 * a + b ∧ c`, ...) is evaluated at
elaboration time on *symbolic* coefficients: every coefficient of every intermediate result is
a node of a hash-consed DAG over the coefficients of the expression's leaves (its operands) and
its opaque scalars. The DAG is then emitted as straight-line code (`Grassmann.Fuse.Emit`): one
`let` per node, every output written into one result buffer, so a whole expression costs one
allocation instead of one per operation (DESIGN.md §5.2; docs/PERF.md, "fusion").

## Exactness

The products are applied with the **same plans in the same summation order** as the generated
kernels (`Grassmann.Kernel.Codegen.rowSum`): the first entry of an output is its term (negated,
or scaled by its metric coefficient), each further entry is added or subtracted. Intermediate
results are nodes, not expanded polynomials, so a fused expression computes the very same
floating-point operations as the chain of typed operations it replaces. The graph only applies
rewrites that are exact in IEEE arithmetic (and in every commutative `Coeff`):

* `a + (-b) = a - b`, `a - (-b) = a + b`, `(-a) + b = b - a`, `-(-a) = a`, `-(a - b) = b - a`;
* `(-a)·b = a·(-b) = -(a·b)`, `1·a = a`, `(-1)·a = -a`;
* commutativity of `+` and `·` (operands ordered by node id, which merges `x₀y₁` and `y₁x₀`),
  only when the coefficient type is commutative (`Graph.commutative`);

and the structural-zero rules `a + 0 = a`, `0 - a = -a`, `a · 0 = 0`, which differ from the
unfused computation only in the sign of a zero result and, for `a · 0`, when `a` is infinite or
NaN (the unfused kernels never multiply by the zeros that the layouts of their operands leave
out, but `convertLayout` and the zero vector do write explicit zeros). So a fused result equals
the unfused one bit for bit up to the sign of zero for finite inputs (`Tests/Fuse`).
-/
import Grassmann.Kernel.Plan
import Std.Data.HashMap

namespace Grassmann.Fuse

open Grassmann.Kernel

/-- One node of the scalar graph. Children are node ids (always smaller than the node's own id,
so ids are a topological order). -/
inductive Node where
  /-- Coefficient `idx` of leaf vector `leaf`. -/
  | input (leaf idx : Nat)
  /-- Opaque scalar number `k` (a run-time value of the coefficient type). -/
  | scalar (k : Nat)
  /-- An exact constant (`Coeff.ofRat q`; `0` and `±1` are special-cased by the smart constructors). -/
  | const (q : Rat)
  /-- `a + b`. -/
  | add (a b : Nat)
  /-- `a - b`. -/
  | sub (a b : Nat)
  /-- `a * b`. -/
  | mul (a b : Nat)
  /-- `-a`. -/
  | neg (a : Nat)
  /-- Application of opaque scalar function number `f` (a closed lambda over the coefficient
  type) to nodes. -/
  | ext (f : Nat) (args : Array Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- A hash-consed scalar graph. Node `0` is the constant `0`, node `1` the constant `1`. -/
structure Graph where
  /-- The nodes, in creation (topological) order. -/
  nodes : Array Node := #[.const 0, .const 1]
  /-- Hash-consing table. -/
  index : Std.HashMap Node Nat := ({} : Std.HashMap Node Nat).insert (.const 0) 0 |>.insert (.const 1) 1
  /-- Whether `+` and `·` of the coefficient type commute (operands are then ordered). -/
  commutative : Bool := true
  deriving Inhabited

namespace Graph

/-- The node `0`. -/
def zero : Nat := 0
/-- The node `1`. -/
def one : Nat := 1

/-- The node with id `i`. -/
@[inline] def get (g : Graph) (i : Nat) : Node := g.nodes[i]?.getD (.const 0)

/-- Whether node `i` is the constant `q`. -/
@[inline] def isConst (g : Graph) (i : Nat) (q : Rat) : Bool :=
  match g.get i with
  | .const r => r == q
  | _ => false

/-- Intern a node (no simplification). -/
def intern (g : Graph) (n : Node) : Graph × Nat :=
  match g.index.get? n with
  | some i => (g, i)
  | none =>
    let i := g.nodes.size
    ({ g with nodes := g.nodes.push n, index := g.index.insert n i }, i)

/-- The constant `q`. -/
def const (g : Graph) (q : Rat) : Graph × Nat :=
  if q == 0 then (g, zero) else if q == 1 then (g, one) else g.intern (.const q)

/-- `-a`. -/
def neg (g : Graph) (a : Nat) : Graph × Nat :=
  match g.get a with
  | .const q => g.const (-q)
  | .neg b => (g, b)
  | .sub b c => g.intern (.sub c b)
  | _ => g.intern (.neg a)

/-- Order two operands of a commutative operation. -/
@[inline] def order (g : Graph) (a b : Nat) : Nat × Nat := if g.commutative && b < a then (b, a) else (a, b)

mutual

/-- `a + b`. -/
partial def add (g : Graph) (a b : Nat) : Graph × Nat :=
  if a == zero then (g, b) else if b == zero then (g, a) else
  match g.get a, g.get b with
  | _, .neg b' => sub g a b'
  | .neg a', _ => sub g b a'
  | _, _ => let (x, y) := g.order a b; g.intern (.add x y)

/-- `a - b`. -/
partial def sub (g : Graph) (a b : Nat) : Graph × Nat :=
  if b == zero then (g, a) else if a == zero then g.neg b else
  match g.get b with
  | .neg b' => add g a b'
  | _ => g.intern (.sub a b)

end

/-- `a * b`. -/
partial def mul (g : Graph) (a b : Nat) : Graph × Nat :=
  if a == zero || b == zero then (g, zero)
  else if a == one then (g, b) else if b == one then (g, a)
  else if g.isConst a (-1) then g.neg b else if g.isConst b (-1) then g.neg a
  else match g.get a, g.get b with
  | .neg a', _ => let (g, m) := g.mul a' b; g.neg m
  | _, .neg b' => let (g, m) := g.mul a b'; g.neg m
  | _, _ => let (x, y) := g.order a b; g.intern (.mul x y)

/-- `a / b` through opaque binary function `f` (the coefficient type's division). -/
def div' (g : Graph) (f a b : Nat) : Graph × Nat :=
  if b == one then (g, a) else g.intern (.ext f #[a, b])

/-- Opaque function `f` applied to `args`. -/
def ext (g : Graph) (f : Nat) (args : Array Nat) : Graph × Nat := g.intern (.ext f args)

/-- The sum of the entries of output `c` of plan `p` in the generated kernels' order
(`Grassmann.Kernel.Codegen.rowSum`): the first entry as its term (negated or scaled), the
others added or subtracted; `term t` builds the product of entry `t`'s operands. -/
def rowSum (g : Graph) (p : Plan) (c : Nat) (term : Graph → Nat → Graph × Nat) : Graph × Nat := Id.run do
  let s := (p.rowStart[c]?.getD 0).toNat
  let e := (p.rowStart[c + 1]?.getD 0).toNat
  let mut g := g
  let mut acc : Option Nat := none
  for t in [s:e] do
    let (g1, v) := term g t
    g := g1
    let code := p.code.get! t
    let (g2, r) : Graph × Nat := match acc, code with
      | none, 0 => (g, v)
      | none, 1 => g.neg v
      | none, _ =>
        let (g, q) := g.const (p.coef[t]?.getD 0)
        g.mul q v
      | some a, 0 => g.add a v
      | some a, 1 => g.sub a v
      | some a, _ =>
        let (g, q) := g.const (p.coef[t]?.getD 0)
        let (g, m) := g.mul q v
        g.add a m
    g := g2
    acc := some r
  return (g, acc.getD zero)

/-- A binary plan applied to the node vectors `x` and `y`: the node of every output. -/
def apply₂ (g : Graph) (p : Plan) (x y : Array Nat) : Graph × Array Nat := Id.run do
  let mut g := g
  let mut out := #[]
  for c in [0:p.outputs] do
    let (g1, o) := g.rowSum p c fun g t => g.mul (x[p.ia[t]!.toNat]?.getD zero) (y[p.ib[t]!.toNat]?.getD zero)
    g := g1
    out := out.push o
  return (g, out)

/-- A unary plan applied to the node vector `x`. -/
def apply₁ (g : Graph) (p : Plan) (x : Array Nat) : Graph × Array Nat := Id.run do
  let mut g := g
  let mut out := #[]
  for c in [0:p.outputs] do
    let (g1, o) := g.rowSum p c fun g t => (g, x[p.ia[t]!.toNat]?.getD zero)
    g := g1
    out := out.push o
  return (g, out)

/-- Map a unary node operation over a vector. -/
def mapV (g : Graph) (f : Graph → Nat → Graph × Nat) (x : Array Nat) : Graph × Array Nat :=
  x.foldl (init := (g, #[])) fun (g, out) a => let (g, r) := f g a; (g, out.push r)

/-- Combine two vectors of the same length elementwise. -/
def zipV (g : Graph) (f : Graph → Nat → Nat → Graph × Nat) (x y : Array Nat) : Graph × Array Nat :=
  (x.zip y).foldl (init := (g, #[])) fun (g, out) (a, b) => let (g, r) := f g a b; (g, out.push r)

/-- The nodes reachable from `roots`, in increasing (topological) order. -/
def reachable (g : Graph) (roots : Array Nat) : Array Nat := Id.run do
  let mut mark := Array.replicate g.nodes.size false
  let mut stack := roots
  while h : stack.size > 0 do
    let i := stack[stack.size - 1]
    stack := stack.pop
    if mark[i]?.getD true then continue
    mark := mark.set! i true
    match g.get i with
    | .add a b | .sub a b | .mul a b => stack := (stack.push a).push b
    | .neg a => stack := stack.push a
    | .ext _ args => stack := stack ++ args
    | _ => pure ()
  return (Array.range g.nodes.size).filter (mark[·]?.getD false)

/-- Number of arithmetic operations (`+ - · neg` and opaque functions) among the nodes reachable from `roots`. -/
def opCount (g : Graph) (roots : Array Nat) : Nat :=
  (g.reachable roots).foldl (init := 0) fun acc i => match g.get i with
    | .add .. | .sub .. | .mul .. | .neg .. | .ext .. => acc + 1
    | _ => acc

end Graph

end Grassmann.Fuse
