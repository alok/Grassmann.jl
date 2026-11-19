/-
The kernel emitter (DESIGN.md §5.2): Lean's counterpart of Julia's `@generated`
products (Grassmann.jl `src/algebra.jl:1152-1889`, grassmann-products.md §4.4).

For each planned `Spec` (`Grassmann.Kernel.Codegen.Plans`) the emitter builds, at
elaboration time, the core term of a straight-line kernel

```lean
def k {α : Type} [Coeff α] (x : Values α na) (y : Values α nb) : Values α nc :=
  let x₀ := x.get ⟨0, _⟩; …; let y₀ := y.get ⟨0, _⟩; …           -- each used input once
  let o₀ := x₀ * y₀ - x₁ * y₁ + …; …                             -- one sum per output
  (base.set ⟨0, _⟩ o₀).set ⟨1, _⟩ o₁ …                           -- packed storage
```

directly as an `Expr` (no elaboration of arithmetic syntax, so emission costs
little beyond the compiler's own work) and adds it with `addDecl`, marked
`@[specialize]`. Reads and writes are unchecked (`Fin` literals with
kernel-checked bounds proofs), so the compiled kernel has no bounds checks, no
branches and no loop: at `α = Float` it specializes to unboxed loads,
multiply-adds and stores.

## The output buffer

A kernel writes its outputs into one buffer, `base` (`Base`):

* an operand of the output's size (`Base.arg`), so `m := ~m` on an exclusive `m` allocates
  nothing; the writes of outputs the operand already holds are skipped (`Out.read` of the same
  position: the identity entries of the sign maps, a copy in a conversion), so a map that
  fixes every entry (`~v` of a vector) returns its operand untouched, shared or not;
* when *both* operands of a binary kernel have the output's size, whichever of them is
  exclusive at run time (`Base.pick`, `pickBase`): `a * m` with an exclusive `m` and a shared
  `a` writes into `m` (every output is written, so which buffer is chosen is invisible);
* otherwise a copy of the zero vector (`Base.zeros`, a closed constant at each coefficient
  type), whose zero outputs are not written again.

Measured at `Float` (ℝ3 `Multivector*Multivector`, docs/PERF.md): 21 ns with a
`FloatArray.push` chain (one runtime call per output), 14 ns with the writes.

## Exactness

Each output sums its entries **in the reference order** (`Plan.row₂`), so a
generated kernel agrees with the reference kernel bit for bit up to the sign of
zero (the reference starts every sum from `0`, the kernel from its first term).
Coefficients `±1` cost a single add or subtract; any other exact coefficient
(diagonal metrics) is `Coeff.ofRat r * term`. The linear kernels (`add` … `convSub`,
`Grassmann.Kernels`) perform exactly the reference's operations, explicit `+ 0` of the promoted
sums included.

## Dispatch

The dispatch functions and the `Kernels V` instance are emitted as syntax (they
are small `match`es whose dependent motives the elaborator handles): per field,
one `@[inline]` function per operation matching the layout triple, and one
matching the operation; every unmatched case falls through to the reference
kernel (`refBin`/`refBinProj`/`refUn`, `convertLayout`, `Values` arithmetic). At a call site
whose operation and layouts are literals (every typed instance of the algebra layer), the
projection of the instance, the dispatchers and the `match`es fold away and
the call is a direct call of the kernel specialized at the coefficient type.
Two caveats of the compiler (Lean v4.35): the grade patterns (`.chain 2`) compile
to `instDecidableEqNat` tests, which LCNF folds only after its specialization
pass, so a call site also specializes the (dead) kernels of the other grades of
its operation (compile time only; the final code is the direct call); and the
typed layer's parity layouts (`halfLayout ((G + H) % 2 == 1)`) do not fold at all
(no `Nat.mod`/`Nat.beq` folding), leaving one branch on a closed `Bool`.
-/
import Grassmann.Kernel.Codegen.Plans
import Lean.Elab.Command
import Lean.Compiler.Specialize

namespace Grassmann.Kernel.Codegen

open Lean Meta Elab Command
open DirectSum StaticVectors AbstractTensors

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
  /-- Generated constants `c : {α : Type} → [Coeff α] → α` for the non-unit coefficients. -/
  coefs : Array (Rat × Name) := #[]

namespace Arith

/-- The arithmetic of `α` from its `Coeff` instance (`coefs`: the space's coefficient constants). -/
def new (α inst : Expr) (coefs : Array (Rat × Name) := #[]) : Arith where
  α := α
  inst := inst
  coefs := coefs
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
/-- `Coeff.ofRat q`, through the space's coefficient constant for `q` when there is one (a
closed constant at each coefficient type, where an inline `Coeff.ofRat` is recomputed on
every call: at `Float`, `Float.ofInt num / Float.ofNat den`). -/
def ofRat (r : Arith) (q : Rat) : Expr :=
  match r.coefs.find? (·.1 == q) with
  | some (_, c) => mkApp2 (mkConst c) r.α r.inst
  | none => mkApp3 (mkConst ``Coeff.ofRat) r.α r.inst (mkApp2 (mkConst ``mkRat) (toExpr q.num) (toExpr q.den))
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

/-- The unchecked write `v.set ⟨i, _⟩ o` of `v : Values α n`. -/
def set (r : Arith) (n : Nat) (v : Expr) (i : Nat) (o : Expr) : Expr :=
  mkApp6 (mkConst ``Values.set [0]) r.α r.P (mkRawNatLit n) v
    (mkApp3 (mkConst ``Fin.mk) (mkRawNatLit n) (mkRawNatLit i) (ltProof i n)) o

/-- `base.set ⟨0, _⟩ o₀ |>.set ⟨1, _⟩ o₁ …` for `base : Values α n`, `n = os.size`: the
outputs written into `base` (in place when `base` is exclusive; otherwise its first write
copies it once). -/
def packSet (r : Arith) (base : Expr) (os : Array Expr) : Expr := Id.run do
  let n := os.size
  let mut v := base
  for h : i in [0:n] do
    v := r.set n v i os[i]
  return v

/-- The zero vector `zeroValues n : Values α n`. -/
def zeros (r : Arith) (n : Nat) : Expr := mkApp3 (mkConst ``Grassmann.zeroValues) r.α r.inst (mkRawNatLit n)

/-- `pickBase x y : Values α n`. -/
def pick (r : Arith) (n : Nat) (x y : Expr) : Expr :=
  mkApp5 (mkConst ``Grassmann.Kernel.pickBase) r.α r.inst (mkRawNatLit n) x y

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

/-! ## The general kernel builder -/

/-- A parameter of a generated kernel (after `{α : Type} [Coeff α]`). -/
inductive Param where
  /-- A coefficient vector `Values α n`. -/
  | vec (n : Nat)
  /-- A coefficient `α`. -/
  | scalar
  deriving Inhabited, BEq

/-- Where a kernel writes its outputs (see the module docstring). -/
inductive Base where
  /-- Into parameter `k` (a vector of the output's size). -/
  | arg (k : Nat)
  /-- Into whichever of parameters `k₁`, `k₂` (both of the output's size) is exclusive. -/
  | pick (k₁ k₂ : Nat)
  /-- Into a copy of the zero vector. -/
  | zeros
  deriving Inhabited, BEq

/-- One output of a kernel. -/
inductive Out where
  /-- The constant `0`. -/
  | zero
  /-- Exactly entry `i` of vector parameter `k`. -/
  | read (k i : Nat)
  /-- A term over the reads. -/
  | val (e : Expr)
  deriving Inhabited

/-- Whether the output buffer `base` already holds output `c` (the write is skipped). -/
def Out.held (o : Out) (base : Base) (c : Nat) : Bool :=
  match o, base with
  | .zero, .zeros => true
  | .read k i, .arg k' => k == k' && i == c
  | _, _ => false

/-- The type and value of a straight-line kernel `{α} [Coeff α] (params…) : Values α nc`. The
outputs are computed by `outs ar read param zero` from the reads `read k i` (entry `i` of vector
parameter `k`, each let-bound once and only if used), the parameters and a let-bound zero; they
are written into `base`, skipping the ones it already holds. -/
def kernelCore (params : Array Param) (nc : Nat) (base : Base) (coefs : Array (Rat × Name))
    (outs : Arith → (Nat → Nat → Expr) → (Nat → Expr) → Expr → MetaM (Array Out)) :
    MetaM (Expr × Expr) := do
  withLocalDecl `α .implicit (mkSort Level.one) fun α => do
  withLocalDecl `inst .instImplicit (mkApp (mkConst ``Coeff) α) fun inst => do
    let r := Arith.new α inst coefs
    let names := (Array.range params.size).map fun k => Name.mkSimple s!"p{k}"
    let tys := params.map fun | .vec n => r.values n | .scalar => α
    let rec go (k : Nat) (acc : Array Expr) : MetaM (Expr × Expr) := do
      if h : k < params.size then
        withLocalDeclD names[k]! tys[k]! fun p => go (k + 1) (acc.push p)
      else
        -- every read of every vector parameter (unused ones are dropped by `mkLetFVars`)
        let mut rn : Array Name := #[]
        let mut rv : Array Expr := #[]
        let mut off : Array Nat := #[]
        for h : j in [0:params.size] do
          off := off.push rv.size
          if let .vec n := params[j] then
            for i in [0:n] do
              rn := rn.push (.mkSimple s!"x{j}_{i}")
              rv := rv.push (r.get n acc[j]! i)
        withLets rn α rv fun reads => do
        withLetDecl `z α r.zero fun z => do
          let read (j i : Nat) : Expr := reads[off[j]! + i]!
          let param (j : Nat) : Expr := acc[j]!
          let os ← outs r read param z
          -- the outputs to write, let-bound
          let mut wn : Array Name := #[]
          let mut wv : Array Expr := #[]
          let mut wix : Array Nat := #[]
          for h : c in [0:os.size] do
            let o := os[c]
            unless o.held base c do
              match o with
              | .zero => wix := wix.push c; wv := wv.push z; wn := wn.push (.mkSimple s!"o{c}")
              | .read j i => wix := wix.push c; wv := wv.push (read j i); wn := wn.push (.mkSimple s!"o{c}")
              | .val e => wix := wix.push c; wv := wv.push e; wn := wn.push (.mkSimple s!"o{c}")
          withLets wn α wv fun ws => do
            let b := match base with
              | .arg j => param j
              | .pick j₁ j₂ => r.pick nc (param j₁) (param j₂)
              | .zeros => r.zeros nc
            let mut v := b
            for h : t in [0:ws.size] do
              v := r.set nc v wix[t]! ws[t]
            let e ← mkLetFVars (reads ++ #[z] ++ ws) v
            let args := #[α, inst] ++ acc
            return (← mkForallFVars args (r.values nc), ← mkLambdaFVars args e)
    go 0 #[]

/-- The output buffer of a kernel with vector parameters of sizes `ns` and output size `nc`:
the pair of operands when both have the output's size (binary kernels), else the first operand
of the output's size, else the zero vector. -/
def chooseBase (ns : Array (Option Nat)) (nc : Nat) : Base :=
  let fits := (Array.range ns.size).filter fun k => ns[k]! == some nc
  match fits.toList with
  | [k₁, k₂] => .pick k₁ k₂
  | k :: _ => .arg k
  | [] => .zeros

/-- The output `c` of plan `p` (reading vector parameter `0`, and `1` for a binary plan) as an
`Out`: `Out.read` when it is exactly one operand entry (a unary entry of coefficient `1`),
`Out.zero` for an empty row. -/
def planOut (r : Arith) (unary : Bool) (p : Plan) (c : Nat) (read : Nat → Nat → Expr) : Out :=
  let s := (p.rowStart[c]?.getD 0).toNat
  let e := (p.rowStart[c + 1]?.getD 0).toNat
  if s == e then .zero
  else if unary && e == s + 1 && p.code.get! s == 0 then .read 0 (p.ia[s]!.toNat)
  else .val (rowSum r p c fun t =>
    let a := read 0 (p.ia[t]!.toNat)
    if unary then a else r.mul a (read 1 (p.ib[t]!.toNat)))

/-- The type and value of the kernel of plan `p` from `Values α na (× Values α nb)` to
`Values α nc` (`unary`: one operand). -/
def kernelTerm (unary : Bool) (na nb nc : Nat) (p : Plan) (coefs : Array (Rat × Name) := #[]) :
    MetaM (Expr × Expr) := do
  let params := if unary then #[Param.vec na] else #[.vec na, .vec nb]
  let base := chooseBase (if unary then #[some na] else #[some na, some nb]) nc
  kernelCore params nc base coefs fun r read _ _ =>
    return (Array.range nc).map fun c => planOut r unary p c read

/-- Compile generated kernels in batches of 32, without a heartbeat limit and with a
recursion depth for their long `let` chains (a whole space in one batch exceeds the default
heartbeat budget of the compiler's checks; an `n = 6` kernel nests hundreds of `let`s). -/
def compileKernels (names : Array Name) : CommandElabM Unit := do
  for i in [0:(names.size + 31) / 32] do
    liftCoreM <| withOptions (fun o => maxRecDepth.set o (max (maxRecDepth.get o) 65536)) <|
      withTheReader Core.Context
        (fun ctx => { ctx with
          maxHeartbeats := 0
          maxRecDepth := max ctx.maxRecDepth 65536 }) <|
      compileDecls (names.extract (i * 32) ((i + 1) * 32))

/-- Add the declaration `name : type := value` (not yet compiled), marked `@[specialize]`,
with a docstring. -/
def addKernelDecl (name : Name) (doc : String) (type value : Expr) : MetaM Unit := do
  addDecl <| .defnDecl {
    name, levelParams := [], type, value
    hints := .regular (getMaxHeight (← getEnv) value + 1)
    safety := .safe }
  modifyEnv fun env => (Compiler.specializeAttr.setParam env name #[]).toOption.getD env
  addDocStringCore name doc

/-- Add the kernel `name` of plan `p` (not yet compiled), marked `@[specialize]`, with a
docstring. -/
def addKernel (name : Name) (doc : String) (unary : Bool) (na nb nc : Nat) (p : Plan)
    (coefs : Array (Rat × Name) := #[]) : MetaM Unit := do
  let (type, value) ← kernelTerm unary na nb nc p coefs
  addKernelDecl name doc type value

/-- The coefficients other than `±1` of some plans (diagonal metrics), without repetitions. -/
def nonUnitCoefs (ps : Array Plan) : Array Rat := Id.run do
  let mut out : Array Rat := #[]
  for p in ps do
    for h : t in [0:p.coef.size] do
      let q := p.coef[t]
      if q != 1 && q != -1 && !out.contains q then out := out.push q
  return out

/-- Declare one coefficient constant `<pre>.coef<i> {α} [Coeff α] : α := Coeff.ofRat q` per
rational `q` (`@[noinline]`, so each coefficient type evaluates it once, as a closed constant
of the specialized kernels). -/
def emitCoefs (pre : Name) (qs : Array Rat) : CommandElabM (Array (Rat × Name)) := do
  let mut out := #[]
  for h : i in [0:qs.size] do
    let q := qs[i]
    let nm := pre ++ Name.mkSimple s!"coef{i}"
    let num : Term := if q.num < 0 then Syntax.mkApp (mkCIdent ``Int.neg) #[quote q.num.natAbs] else quote q.num.natAbs
    elabCommand (← `(command|
      @[noinline, specialize] def $(mkIdent (`_root_ ++ nm)) {α : Type} [AbstractTensors.Coeff α] : α :=
        AbstractTensors.Coeff.ofRat (mkRat $num $(quote q.den))))
    addDocStringCore nm s!"The metric coefficient `{q}` of the generated kernels, as a constant of every \
      coefficient type."
    out := out.push (q, nm)
  return out

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
  /-- The linear kernels: `(spec, kernel name)`. -/
  linear : Array (LinSpec × Name) := #[]
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
  -- `V` is the space's run-time value (an opaque constant, see `emitSpace`)
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

/-! ## Linear kernels (`add` … `convSub`) -/

/-- The name of a linear kernel under the space prefix `pre`. -/
def linName (pre : Name) (s : LinSpec) : Name :=
  let ls := match s.op with
    | .add | .sub | .neg | .smul | .muls => [s.la]
    | .conv => [s.la, s.lc]
    | .convAdd | .convSub => [s.la, s.lb, s.lc]
  pre ++ Name.mkSimple ("_".intercalate ("k" :: s.op.tag :: ls.map layoutTag))

/-- The type and value of a linear kernel of an `n`-generator space (the reference's operations
exactly: `Grassmann.Kernels`' defaults). -/
def linTerm (n : Nat) (s : LinSpec) : MetaM (Expr × Expr) := do
  let (na, nb, nc) := (s.la.size n, s.lb.size n, s.lc.size n)
  -- the position in `l` of the blade at position `c` of `s.lc`, if `l` stores it
  let src (l : Layout) (c : Nat) : Option Nat :=
    let b := (s.lc.blades n)[c]!
    if l.contains n b then some (l.rank n b) else none
  match s.op with
  | .add | .sub =>
    kernelCore #[.vec na, .vec na] na (.pick 0 1) #[] fun r read _ _ =>
      return (Array.range na).map fun i =>
        .val (if s.op == .add then r.add (read 0 i) (read 1 i) else r.sub (read 0 i) (read 1 i))
  | .neg =>
    kernelCore #[.vec na] na (.arg 0) #[] fun r read _ _ =>
      return (Array.range na).map fun i => .val (r.neg (read 0 i))
  | .smul =>
    kernelCore #[.scalar, .vec na] na (.arg 1) #[] fun r read param _ =>
      return (Array.range na).map fun i => .val (r.mul (param 0) (read 1 i))
  | .muls =>
    kernelCore #[.vec na, .scalar] na (.arg 0) #[] fun r read param _ =>
      return (Array.range na).map fun i => .val (r.mul (read 0 i) (param 1))
  | .conv =>
    kernelCore #[.vec na] nc (chooseBase #[some na] nc) #[] fun _ _ _ _ =>
      return (Array.range nc).map fun c => match src s.la c with
        | some i => .read 0 i
        | none => .zero
  | .convAdd | .convSub =>
    let add := s.op == .convAdd
    kernelCore #[.vec na, .vec nb] nc (chooseBase #[some na, some nb] nc) #[] fun r read _ z =>
      return (Array.range nc).map fun c =>
        let op := if add then r.add else r.sub
        match src s.la c, src s.lb c with
        | some i, some j => .val (op (read 0 i) (read 1 j))
        | some i, none => .val (op (read 0 i) z)
        | none, some j => .val (op z (read 1 j))
        | none, none => .zero

/-- Emit the dispatcher of one linear operation: a `match` on its layouts, the reference the
fallback (`Values` arithmetic, `convertLayout`); a conversion into its own layout is the
identity. -/
def emitLinDispatch (nLit : Term) (name : Ident) (op : LinOp) (ks : Array (LinSpec × Name))
    (allLs : List Layout) : CommandElabM Unit := do
  let (l, la, lb, lc, x, y, s) :=
    (mkIdent `l, mkIdent `la, mkIdent `lb, mkIdent `lc, mkIdent `x, mkIdent `y, mkIdent `s)
  let vals (l : Ident) : CommandElabM Term := `(StaticVectors.Values α (DirectSum.Layout.size $nLit $l))
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  match op with
  | .neg =>
    for (sp, k) in ks do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(← layoutStx sp.la), $x => $(mkCIdent k) $x))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _, $x => -$x))
    elabCommand (← `(command|
      @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($l : DirectSum.Layout) ($x : $(← vals l)) :
          $(← vals l) :=
        match $l:ident, $x:ident with $alts:matchAlt*))
  | .add | .sub =>
    for (sp, k) in ks do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(← layoutStx sp.la), $x, $y => $(mkCIdent k) $x $y))
    alts := alts.push <| ← if op == .add then `(Lean.Parser.Term.matchAltExpr| | _, $x, $y => $x + $y)
      else `(Lean.Parser.Term.matchAltExpr| | _, $x, $y => $x - $y)
    elabCommand (← `(command|
      @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($l : DirectSum.Layout) ($x $y : $(← vals l)) :
          $(← vals l) :=
        match $l:ident, $x:ident, $y:ident with $alts:matchAlt*))
  | .smul | .muls =>
    for (sp, k) in ks do
      alts := alts.push <| ← if op == .smul then
          `(Lean.Parser.Term.matchAltExpr| | $(← layoutStx sp.la), $s, $x => $(mkCIdent k) $s $x)
        else `(Lean.Parser.Term.matchAltExpr| | $(← layoutStx sp.la), $s, $x => $(mkCIdent k) $x $s)
    alts := alts.push <| ← if op == .smul then
        `(Lean.Parser.Term.matchAltExpr| | _, $s, $x => StaticVectors.Values.map ($s * ·) $x)
      else `(Lean.Parser.Term.matchAltExpr| | _, $s, $x => StaticVectors.Values.map (· * $s) $x)
    let sig ← if op == .smul then
        `(command| @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($l : DirectSum.Layout) ($s : α)
            ($x : $(← vals l)) : $(← vals l) := match $l:ident, $s:ident, $x:ident with $alts:matchAlt*)
      else
        `(command| @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($l : DirectSum.Layout)
            ($x : $(← vals l)) ($s : α) : $(← vals l) := match $l:ident, $s:ident, $x:ident with $alts:matchAlt*)
    elabCommand sig
  | .conv =>
    for (sp, k) in ks do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $(← layoutStx sp.la), $(← layoutStx sp.lc), $x => $(mkCIdent k) $x))
    for l' in allLs do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(← layoutStx l'), $(← layoutStx l'), $x => $x))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | $la, $lc, $x => Grassmann.Kernel.Codegen.refConvOut $nLit $la $lc $x))
    elabCommand (← `(command|
      @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($la $lc : DirectSum.Layout) ($x : $(← vals la)) :
          $(← vals lc) :=
        match $la:ident, $lc:ident, $x:ident with $alts:matchAlt*))
  | .convAdd | .convSub =>
    for (sp, k) in ks do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $(← layoutStx sp.la), $(← layoutStx sp.lb), $(← layoutStx sp.lc), $x, $y => $(mkCIdent k) $x $y))
    let fb := mkCIdent (if op == .convAdd then ``refConvAddOut else ``refConvSubOut)
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $la, $lb, $lc, $x, $y => $fb $nLit $la $lb $lc $x $y))
    elabCommand (← `(command|
      @[inline] def $name {α : Type} [AbstractTensors.Coeff α] ($la $lb $lc : DirectSum.Layout)
          ($x : $(← vals la)) ($y : $(← vals lb)) : $(← vals lc) :=
        match $la:ident, $lb:ident, $lc:ident, $x:ident, $y:ident with $alts:matchAlt*))

/-! ## Emitting a space -/

/-- The kernel of every planned specification: its declaration name under `pre`, and
whether it is emitted for it (`true`) or shared with the strict kernel of the same
key, whose plan it equals (a projection that drops nothing). -/
def assignKernels (pre : Name) (planned : Array Planned) : Array (Planned × Name × Bool) := Id.run do
  let mut byKey : Std.HashMap (KOp × Layout × Layout × Layout) (Plan × Name) := {}
  let mut out := #[]
  for pl in planned do
    let s := pl.spec
    let k := s.key
    let key := (k.op, k.la, k.lb, k.lc)
    if s.field == .binProj then
      if let some (q, nm) := byKey.get? key then
        if q.entries == pl.plan.entries then
          out := out.push (pl, nm, false)
          continue
    let nm := kernelName pre s
    if s.field == .bin then byKey := byKey.insert key (pl.plan, nm)
    out := out.push (pl, nm, true)
  return out

/-- Emit and compile every kernel of `planned` and every linear kernel of `linear` under the
prefix `pre`, then the dispatchers and the `Kernels` instance for the space `V` (a term
denoting `space`, e.g. an `abbrev`). The fallbacks receive the space as `Vrt`, a
`@[noinline]` constant: an `abbrev` of a structure literal is inlined by the compiler, and
where a dispatch does not fold at a call site the literal was rebuilt (allocated) on every
call before the branch. -/
def emitSpace (space : TensorBundle) (V : Term) (Vrt : Term) (pre : Name) (planned : Array Planned)
    (linear : Array LinSpec) (coefs : Array (Rat × Name) := #[]) : CommandElabM Emitted := do
  let n := space.n
  let mut em : Emitted := {}
  let mut names : Array Name := #[]
  let mut assigned : Array (Spec × Name) := #[]
  for (pl, nm, fresh) in assignKernels pre planned do
    let s := pl.spec
    let k := s.key
    assigned := assigned.push (s, nm)
    if !fresh then continue
    let unary := s.field == .un
    let doc := s!"Generated kernel (DESIGN.md §5.2): `{opTag k.op}` of \
      {layoutDoc k.la}{if unary then "" else s!" × {layoutDoc k.lb}"} → {layoutDoc k.lc}\
      {if k.project then " (projected)" else ""} in `{space}`, {pl.plan.size} entries."
    liftTermElabM <| addKernel nm doc unary (k.la.size n) (k.lb.size n) (k.lc.size n) pl.plan coefs
    names := names.push nm
    em := { em with kernels := em.kernels + 1, entries := em.entries + pl.plan.size }
  for s in linear do
    let nm := linName pre s
    let (type, value) ← liftTermElabM <| linTerm n s
    liftTermElabM <| addKernelDecl nm s!"Generated linear kernel (DESIGN.md §5.2): {s.describe} in `{space}`."
      type value
    names := names.push nm
    em := { em with kernels := em.kernels + 1, linear := em.linear.push (s, nm) }
  compileKernels names
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
      emitOpDispatch Vrt nLit (mkIdent (`_root_ ++ nm)) field op ks
      addDocStringCore nm s!"Generated dispatch of `{opTag op}` ({fieldTag field}) in `{space}` over \
        {ks.size} layout triples; other triples use the reference kernel."
      ops := ops.push (op, mkCIdent nm)
    values := values.push (← fieldValue Vrt field ops)
  -- the linear dispatchers
  for op in LinOp.all do
    let nm := pre ++ Name.mkSimple s!"lin_{op.tag}"
    emitLinDispatch nLit (mkIdent (`_root_ ++ nm)) op (em.linear.filter (·.1.op == op)) (allLayouts n)
    addDocStringCore nm s!"Generated dispatch of the linear kernels `{op.tag}` in `{space}`; other layouts \
      use the reference."
  let lin (op : LinOp) : Ident := mkCIdent (pre ++ Name.mkSimple s!"lin_{op.tag}")
  -- the instance
  let instId := mkIdent (`_root_ ++ pre ++ `instKernels)
  let (l, la, lb, lc, x, y, s) :=
    (mkIdent `l, mkIdent `la, mkIdent `lb, mkIdent `lc, mkIdent `x, mkIdent `y, mkIdent `s)
  elabCommand (← `(command|
    /-- The generated kernels of this space (DESIGN.md §5.2, §5.4). -/
    instance $instId:ident : Grassmann.Kernels $V where
      bin := $(values[0]!)
      binProj := $(values[1]!)
      un := $(values[2]!)
      add := fun $l $x $y => $(lin .add) $l $x $y
      sub := fun $l $x $y => $(lin .sub) $l $x $y
      neg := fun $l $x => $(lin .neg) $l $x
      smul := fun $l $s $x => $(lin .smul) $l $s $x
      muls := fun $l $x $s => $(lin .muls) $l $x $s
      conv := fun $la $lc $x => $(lin .conv) $la $lc $x
      convAdd := fun $la $lb $lc $x $y => $(lin .convAdd) $la $lb $lc $x $y
      convSub := fun $la $lb $lc $x $y => $(lin .convSub) $la $lb $lc $x $y))
  return em

end Grassmann.Kernel.Codegen
