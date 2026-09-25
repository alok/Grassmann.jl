/-
The kernel emitter (DESIGN.md §5.2): Lean's counterpart of Julia's `@generated`
products (Grassmann.jl `src/algebra.jl:1152-1889`, grassmann-products.md §4.4).

For each planned `Spec` (`Grassmann.Kernel.Codegen.Plans`) the emitter builds, at
elaboration time, the core term of a straight-line kernel

```lean
def k {α : Type} [Coeff α] (x : Values α na) (y : Values α nb) : Values α nc :=
  let x₀ := x.get ⟨0, _⟩; …; let y₀ := y.get ⟨0, _⟩; …           -- each used input once
  let o₀ := x₀ * y₀ - x₁ * y₁ + …; …                             -- one sum per output
  ⟨push (… (push (mkEmpty nc) o₀) …) o_{nc-1}, _⟩                  -- packed storage
```

directly as an `Expr` (no elaboration of arithmetic syntax, so emission costs
little beyond the compiler's own work) and adds it with `addDecl`, marked
`@[specialize]`. Reads are unchecked (`Fin` literals with kernel-checked bounds
proofs), and the output size is proved by a chain of `size_push_succ`, so the
compiled kernel has no bounds checks, no branches and no loop: at `α = Float`
it specializes to unboxed loads, multiply-adds and `FloatArray.push`es.

Each output sums its entries **in the reference order** (`Plan.row₂`), so a
generated kernel agrees with the reference kernel bit for bit up to the sign of
zero (the reference starts every sum from `0`, the kernel from its first term).
Coefficients `±1` cost a single add or subtract; any other exact coefficient
(diagonal metrics) is `Coeff.ofRat r * term`.

The dispatch functions and the `Kernels V` instance are emitted as syntax (they
are small `match`es whose dependent motives the elaborator handles): per field,
one `@[inline]` function per operation matching the layout triple, and one
matching the operation; every unmatched case falls through to the reference
kernel (`refBin`/`refBinProj`/`refUn`). At a call site whose operation and
layouts are literals (every typed instance of the algebra layer), the
projection of the instance, the dispatchers and the `match`es fold away and
the call is a direct call of the kernel specialized at the coefficient type.
-/
import Grassmann.Kernel.Codegen.Plans
import Grassmann.Kernel.Class
import Lean.Elab.Command
import Lean.Compiler.Specialize

namespace Grassmann.Kernel.Codegen

open Lean Meta Elab Command
open DirectSum StaticVectors AbstractTensors

/-- One step of the output-size proof of a generated kernel: pushing onto an
array of size `k` gives size `k + 1`. -/
theorem size_push_succ {α : Type} [Packed α] {a : Packed.Arr α} {k : Nat} (x : α)
    (h : Packed.size a = k) : Packed.size (Packed.push a x) = k + 1 := by
  rw [Packed.size_push, h]

/-! ## Names -/

/-- The short name of a layout in kernel names: `c2`, `e`, `o`, `f`. -/
def layoutTag : Layout → String
  | .chain g => s!"c{g}"
  | .even => "e"
  | .odd => "o"
  | .full => "f"

/-- The constructor name of an operation (`mul`, `complementright`, ...). -/
def opTag : KOp → String
  | .bin op => ((reprStr op).splitOn ".").getLast!
  | .un op => ((reprStr op).splitOn ".").getLast!

/-- The name of a field (`bin`, `proj`, `un`). -/
def fieldTag : Field → String
  | .bin => "bin"
  | .binProj => "proj"
  | .un => "un"

/-- The declaration name of a kernel under the space prefix `pre`. -/
def kernelName (pre : Name) (s : Spec) : Name :=
  let k := s.key
  let ls := if s.field == .un then [k.la, k.lc] else [k.la, k.lb, k.lc]
  pre ++ Name.mkSimple ("_".intercalate (("k" :: fieldTag s.field :: opTag k.op :: ls.map layoutTag)))

/-! ## Kernel terms -/

/-- Arithmetic of the coefficient type `α` with instance `inst : Coeff α`, as core terms. -/
structure Arith where
  /-- The coefficient type. -/
  α : Expr
  /-- The `Coeff α` instance. -/
  inst : Expr
  /-- The `Packed α` instance (`Coeff.packed`). -/
  P : Expr
  /-- `HAdd α α α`. -/
  addI : Expr
  /-- `HSub α α α`. -/
  subI : Expr
  /-- `HMul α α α`. -/
  mulI : Expr
  /-- `Neg α`. -/
  negI : Expr

namespace Arith

/-- The arithmetic of `α` from its `Coeff` instance. -/
def new (α inst : Expr) : Arith where
  α := α
  inst := inst
  P := mkApp2 (mkConst ``Coeff.packed) α inst
  addI := mkApp2 (mkConst ``instHAdd [0]) α (mkApp2 (mkConst ``Coeff.toAdd) α inst)
  subI := mkApp2 (mkConst ``instHSub [0]) α (mkApp2 (mkConst ``Coeff.toSub) α inst)
  mulI := mkApp2 (mkConst ``instHMul [0]) α (mkApp2 (mkConst ``Coeff.toMul) α inst)
  negI := mkApp2 (mkConst ``Coeff.toNeg) α inst

/-- `a + b`. -/
def add (r : Arith) (a b : Expr) : Expr := mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) r.α r.α r.α r.addI a b
/-- `a - b`. -/
def sub (r : Arith) (a b : Expr) : Expr := mkApp6 (mkConst ``HSub.hSub [0, 0, 0]) r.α r.α r.α r.subI a b
/-- `a * b`. -/
def mul (r : Arith) (a b : Expr) : Expr := mkApp6 (mkConst ``HMul.hMul [0, 0, 0]) r.α r.α r.α r.mulI a b
/-- `-a`. -/
def neg (r : Arith) (a : Expr) : Expr := mkApp3 (mkConst ``Neg.neg [0]) r.α r.negI a
/-- `Coeff.zero`. -/
def zero (r : Arith) : Expr := mkApp2 (mkConst ``Coeff.zero) r.α r.inst
/-- `Coeff.ofRat q`. -/
def ofRat (r : Arith) (q : Rat) : Expr :=
  mkApp3 (mkConst ``Coeff.ofRat) r.α r.inst (mkApp2 (mkConst ``mkRat) (toExpr q.num) (toExpr q.den))
/-- `Values α n`. -/
def values (r : Arith) (n : Nat) : Expr := mkApp3 (mkConst ``Values [0]) r.α r.P (mkRawNatLit n)

/-- A proof of `i < n` for literals (`Nat.ble (i+1) n` evaluates to `true`). -/
def ltProof (i n : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkRawNatLit (i + 1)) (mkRawNatLit n)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- The unchecked read `v.get ⟨i, _⟩` of `v : Values α n`. -/
def get (r : Arith) (n : Nat) (v : Expr) (i : Nat) : Expr :=
  mkApp5 (mkConst ``Values.get [0]) r.α r.P (mkRawNatLit n) v
    (mkApp3 (mkConst ``Fin.mk) (mkRawNatLit n) (mkRawNatLit i) (ltProof i n))

/-- `⟨push (… (push (mkEmpty n) o₀) …) oₙ₋₁, proof⟩ : Values α n`. -/
def pack (r : Arith) (os : Array Expr) : Expr := Id.run do
  let n := os.size
  let mut arr := mkApp3 (mkConst ``Packed.mkEmpty [0]) r.α r.P (mkRawNatLit n)
  let mut prf := mkApp3 (mkConst ``Packed.size_mkEmpty [0]) r.α r.P (mkRawNatLit n)
  for h : i in [0:n] do
    let o := os[i]
    prf := mkApp6 (mkConst ``size_push_succ) r.α r.P arr (mkRawNatLit i) o prf
    arr := mkApp4 (mkConst ``Packed.push [0]) r.α r.P arr o
  return mkApp5 (mkConst ``Values.mk [0]) r.α r.P (mkRawNatLit n) arr prf

end Arith

/-- Run `k` with let-bound local variables `names[i] : ty := vals[i]` in scope. -/
partial def withLets {β : Type} (names : Array Name) (ty : Expr) (vals : Array Expr)
    (k : Array Expr → MetaM β) (i : Nat := 0) (acc : Array Expr := #[]) : MetaM β :=
  if h : i < vals.size then
    withLetDecl (names[i]?.getD `v) ty vals[i] fun v => withLets names ty vals k (i + 1) (acc.push v)
  else k acc

/-- The sum of the entries of output `c` of plan `p`, in the reference order;
`term t` is the product of entry `t`'s operands. -/
def rowSum (r : Arith) (p : Plan) (c : Nat) (term : Nat → Expr) : Expr := Id.run do
  let s := (p.rowStart[c]?.getD 0).toNat
  let e := (p.rowStart[c + 1]?.getD 0).toNat
  let mut acc : Option Expr := none
  for t in [s:e] do
    let v := term t
    let code := p.code.get! t
    acc := some <| match acc, code with
      | none, 0 => v
      | none, 1 => r.neg v
      | none, _ => r.mul (r.ofRat (p.coef[t]?.getD 0)) v
      | some a, 0 => r.add a v
      | some a, 1 => r.sub a v
      | some a, _ => r.add a (r.mul (r.ofRat (p.coef[t]?.getD 0)) v)
  return acc.getD r.zero

/-- The type and value of the kernel of plan `p` from `Values α na (× Values α nb)` to
`Values α nc` (`unary`: one operand). -/
def kernelTerm (unary : Bool) (na nb nc : Nat) (p : Plan) : MetaM (Expr × Expr) := do
  withLocalDecl `α .implicit (mkSort Level.one) fun α => do
  withLocalDecl `inst .instImplicit (mkApp (mkConst ``Coeff) α) fun inst => do
    let r := Arith.new α inst
    withLocalDeclD `x (r.values na) fun x => do
      let body (y? : Option Expr) : MetaM (Expr × Expr) := do
        let args := #[α, inst, x] ++ y?.toArray
        -- the inputs each output reads, each read once
        let mut usedX := Array.replicate na false
        let mut usedY := Array.replicate nb false
        for t in [0:p.size] do
          usedX := usedX.set! (p.ia[t]!.toNat) true
          if !unary then usedY := usedY.set! (p.ib[t]!.toNat) true
        let mut rn : Array Name := #[]
        let mut rv : Array Expr := #[]
        let mut slotX : Array Nat := Array.replicate na 0
        let mut slotY : Array Nat := Array.replicate nb 0
        for i in [0:na] do
          if usedX[i]! then
            slotX := slotX.set! i rv.size
            rn := rn.push (.mkSimple s!"x{i}")
            rv := rv.push (r.get na x i)
        if let some y := y? then
          for j in [0:nb] do
            if usedY[j]! then
              slotY := slotY.set! j rv.size
              rn := rn.push (.mkSimple s!"y{j}")
              rv := rv.push (r.get nb y j)
        withLets rn α rv fun reads => do
          let term (t : Nat) : Expr :=
            let a := reads[slotX[p.ia[t]!.toNat]!]!
            if unary then a else r.mul a reads[slotY[p.ib[t]!.toNat]!]!
          let outs := (Array.range nc).map fun c => rowSum r p c term
          withLets ((Array.range nc).map fun c => .mkSimple s!"o{c}") α outs fun os => do
            let e ← mkLetFVars (reads ++ os) (r.pack os)
            return (← mkForallFVars args (r.values nc), ← mkLambdaFVars args e)
      if unary then body none
      else withLocalDeclD `y (r.values nb) fun y => body (some y)

/-- Add the kernel `name` of plan `p` (not yet compiled), marked `@[specialize]`, with a
docstring. -/
def addKernel (name : Name) (doc : String) (unary : Bool) (na nb nc : Nat) (p : Plan) : MetaM Unit := do
  let (type, value) ← kernelTerm unary na nb nc p
  addDecl <| .defnDecl {
    name, levelParams := [], type, value
    hints := .regular (getMaxHeight (← getEnv) value + 1)
    safety := .safe }
  modifyEnv fun env => (Compiler.specializeAttr.setParam env name #[]).toOption.getD env
  addDocStringCore name doc

/-! ## Fallbacks

The dispatch falls through to these out-of-line copies of the reference kernels:
one call per unmatched case keeps the dispatch code small, and each is still
specialized at the coefficient type of its call site (instance arguments always
are), so an uncovered shape costs what the reference kernel costs. -/

/-- `Grassmann.Kernel.refBin`, out of line. -/
@[noinline, specialize] def refBinOut {α : Type} [Coeff α] (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  refBin V op la lb lc x y

/-- `Grassmann.Kernel.refBinProj`, out of line. -/
@[noinline, specialize] def refBinProjOut {α : Type} [Coeff α] (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  refBinProj V op la lb lc x y

/-- `Grassmann.Kernel.refUn`, out of line. -/
@[noinline, specialize] def refUnOut {α : Type} [Coeff α] (V : TensorBundle) (op : UnOp) (la lc : Layout)
    (x : Values α (la.size V.n)) : Values α (lc.size V.n) :=
  refUn V op la lc x

/-! ## Dispatch syntax -/

/-- A layout as a pattern/term. -/
def layoutStx (l : Layout) : CommandElabM Term :=
  match l with
  | .chain g => `(DirectSum.Layout.chain $(quote g))
  | .even => `(DirectSum.Layout.even)
  | .odd => `(DirectSum.Layout.odd)
  | .full => `(DirectSum.Layout.full)

/-- An operation constructor as a pattern/term. -/
def opStx : KOp → Term
  | .bin op => mkCIdent (Name.str ``DirectSum.BinOp (opTag (.bin op)))
  | .un op => mkCIdent (Name.str ``DirectSum.UnOp (opTag (.un op)))

/-- A human-readable description of a layout. -/
def layoutDoc : Layout → String
  | .chain g => s!"Chain {g}"
  | .even => "Spinor"
  | .odd => "CoSpinor"
  | .full => "Multivector"

/-- The emitted declarations of one space. -/
structure Emitted where
  /-- Kernels by field and operation: `(field, op, [(spec, kernel name)])`. -/
  groups : Array (Field × KOp × Array (Spec × Name)) := #[]
  /-- Number of kernels. -/
  kernels : Nat := 0
  /-- Total multiply-accumulate entries. -/
  entries : Nat := 0

/-- The out-of-line reference kernel of a field. -/
def fallbackOf : Field → Ident
  | .bin => mkCIdent ``refBinOut
  | .binProj => mkCIdent ``refBinProjOut
  | .un => mkCIdent ``refUnOut

/-- Emit the dispatcher of one operation of one field: a `match` on the layouts,
each emitted kernel an alternative, the reference kernel the fallback. -/
def emitOpDispatch (V : Term) (nLit : Term) (name : Ident) (field : Field) (op : KOp)
    (ks : Array (Spec × Name)) : CommandElabM Unit := do
  let (la, lb, lc, x, y) := (mkIdent `la, mkIdent `lb, mkIdent `lc, mkIdent `x, mkIdent `y)
  let o := opStx op
  let fb := fallbackOf field
  match field with
  | .un =>
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for (s, k) in ks do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $(← layoutStx s.key.la), $(← layoutStx s.key.lc), $x => $(mkCIdent k) $x))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $la, $lc, $x => $fb $V $o $la $lc $x))
    elabCommand (← `(command|
      @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($la $lc : DirectSum.Layout)
          ($x : StaticVectors.Values α (DirectSum.Layout.size $nLit $la)) :
          StaticVectors.Values α (DirectSum.Layout.size $nLit $lc) :=
        match $la:ident, $lc:ident, $x:ident with $alts:matchAlt*))
  | .bin | .binProj =>
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for (s, k) in ks do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $(← layoutStx s.key.la), $(← layoutStx s.key.lb), $(← layoutStx s.key.lc), $x, $y =>
          $(mkCIdent k) $x $y))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | $la, $lb, $lc, $x, $y => $fb $V $o $la $lb $lc $x $y))
    elabCommand (← `(command|
      @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($la $lb $lc : DirectSum.Layout)
          ($x : StaticVectors.Values α (DirectSum.Layout.size $nLit $la))
          ($y : StaticVectors.Values α (DirectSum.Layout.size $nLit $lb)) :
          StaticVectors.Values α (DirectSum.Layout.size $nLit $lc) :=
        match $la:ident, $lb:ident, $lc:ident, $x:ident, $y:ident with $alts:matchAlt*))

/-- The value of one field of the instance: a `match` on the operation, each operation
with kernels calling its dispatcher (`ops`), the others the reference kernel. -/
def fieldValue (V : Term) (field : Field) (ops : Array (KOp × Ident)) : CommandElabM Term := do
  let (op, la, lb, lc, x, y) := (mkIdent `op, mkIdent `la, mkIdent `lb, mkIdent `lc, mkIdent `x, mkIdent `y)
  let fb := fallbackOf field
  let allOps := if field == .un then UnOp.all.length else BinOp.all.length
  match field with
  | .un =>
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for (k, f) in ops do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(opStx k) => $f $la $lc $x))
    if ops.size < allOps then
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $op => $fb $V $op $la $lc $x))
    `(fun $op $la $lc $x => match $op:ident with $alts:matchAlt*)
  | .bin | .binProj =>
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for (k, f) in ops do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(opStx k) => $f $la $lb $lc $x $y))
    if ops.size < allOps then
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $op => $fb $V $op $la $lb $lc $x $y))
    `(fun $op $la $lb $lc $x $y => match $op:ident with $alts:matchAlt*)

/-! ## Emitting a space -/

/-- Emit and compile every kernel of `planned` under the prefix `pre`, then the dispatchers
and the `Kernels` instance for the space `V` (a term denoting `space`, e.g. an `abbrev`). -/
def emitSpace (space : TensorBundle) (V : Term) (pre : Name) (planned : Array Planned) :
    CommandElabM Emitted := do
  let n := space.n
  let mut em : Emitted := {}
  let mut names : Array Name := #[]
  -- kernels, deduplicated: a projecting key whose strict plan exists reuses the strict kernel
  let mut byKey : Std.HashMap (KOp × Layout × Layout × Layout) (Plan × Name) := {}
  let mut assigned : Array (Spec × Name) := #[]
  for pl in planned do
    let s := pl.spec
    let k := s.key
    let key := (k.op, k.la, k.lb, k.lc)
    if s.field == .binProj then
      if let some (q, nm) := byKey.get? key then
        if q.entries == pl.plan.entries then
          assigned := assigned.push (s, nm)
          continue
    let nm := kernelName pre s
    let unary := s.field == .un
    let doc := s!"Generated kernel (DESIGN.md §5.2): `{opTag k.op}` of \
      {layoutDoc k.la}{if unary then "" else s!" × {layoutDoc k.lb}"} → {layoutDoc k.lc}\
      {if k.project then " (projected)" else ""} in `{space}`, {pl.plan.size} entries."
    liftTermElabM <| addKernel nm doc unary (k.la.size n) (k.lb.size n) (k.lc.size n) pl.plan
    names := names.push nm
    if s.field == .bin then byKey := byKey.insert key (pl.plan, nm)
    assigned := assigned.push (s, nm)
    em := { em with kernels := em.kernels + 1, entries := em.entries + pl.plan.size }
  liftCoreM <| compileDecls names
  -- group by field and operation, in first-appearance order
  let mut groups : Array (Field × KOp × Array (Spec × Name)) := #[]
  for (s, nm) in assigned do
    match groups.findIdx? fun (f, o, _) => f == s.field && o == s.key.op with
    | some i => groups := groups.modify i fun (f, o, ks) => (f, o, ks.push (s, nm))
    | none => groups := groups.push (s.field, s.key.op, #[(s, nm)])
  em := { em with groups }
  -- per-operation dispatchers
  let nLit : Term := quote n
  let mut values : Array Term := #[]
  for field in [Field.bin, .binProj, .un] do
    let mut ops : Array (KOp × Ident) := #[]
    for (_, op, ks) in groups.filter (·.1 == field) do
      let nm := pre ++ Name.mkSimple s!"{fieldTag field}_{opTag op}"
      emitOpDispatch V nLit (mkIdent (`_root_ ++ nm)) field op ks
      addDocStringCore nm s!"Generated dispatch of `{opTag op}` ({fieldTag field}) in `{space}` over \
        {ks.size} layout triples; other triples use the reference kernel."
      ops := ops.push (op, mkCIdent nm)
    values := values.push (← fieldValue V field ops)
  -- the instance
  let instId := mkIdent (`_root_ ++ pre ++ `instKernels)
  elabCommand (← `(command|
    /-- The generated kernels of this space (DESIGN.md §5.2, §5.4). -/
    instance $instId:ident : Grassmann.Kernels $V where
      bin := $(values[0]!)
      binProj := $(values[1]!)
      un := $(values[2]!)))
  return em

end Grassmann.Kernel.Codegen
