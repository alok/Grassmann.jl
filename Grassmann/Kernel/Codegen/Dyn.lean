/-
Emission of the dynamic layer's kernels (`Grassmann.DynKernels`, `Grassmann.Kernel.Dyn`): run by
`grassmann_kernels`/`basis!` for spaces with at most five generators and no tangent generators.

For every key of `dynKeys` the emitter builds Julia's loop plan (`Grassmann.Loops.build`, the
first operand outermost; Julia's expression form, which its generators take below their
`cache_limit` for every such key when `n ≤ 5`) and compares it with the plan of the typed
layer's generated kernel of the same layouts. Equal plans share the kernel (the generated kernel
sums the same entries in the same order from the first term, so it computes Julia's loop);
otherwise a kernel `k_loop_<op>_<la>_<lb>_<lc>` is emitted from the loop plan itself (its zero
metric factors `0·(x·y)` and conformal coefficients included). The unary flags compare Julia's
entry-wise maps (`out[β] = c·x[src(β)]`, DirectSum's container-level coefficient `c`, zero
coefficients kept) with the generated unary plans in the same way.
-/
import Grassmann.Kernel.Codegen.Emit
import Grassmann.Kernel.Dyn

namespace Grassmann.Kernel.Codegen

open Lean Meta Elab Command
open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- One loop of the dynamic layer: its key, Julia's plan, and the typed kernel that computes it
(when the plans agree). -/
structure DynLoop where
  /-- The operation. -/
  op : BinOp
  /-- The first operand's layout. -/
  la : Layout
  /-- The second operand's layout. -/
  lb : Layout
  /-- The result layout. -/
  lc : Layout
  /-- Julia's loop plan. -/
  plan : Plan
  /-- The typed kernel with the same plan, if any. -/
  alias : Option Name
  deriving Inhabited

/-- Whether two plans have the same entries in the same rows (the same computation). -/
def samePlan (p q : Plan) : Bool :=
  p.rowStart == q.rowStart && p.ia == q.ia && p.ib == q.ib && p.coef == q.coef

/-- Julia's entry-wise image of a container under a sign map or complement (`op`, from layout
`la` into `lc`): output blade `β` is `c·x[src]` with `src = β` (sign maps, metrics) or its
complement, and `c` the container-level coefficient (`Kernel.unTermsC`, zero kept; Grassmann
`src/products.jl:1324-1487`, the dynamic layer's `monoCoeff`). -/
def juliaUnaryPlan (V : TensorBundle) (op : UnOp) (la lc : Layout) (complement : Bool) : Plan := Id.run do
  let n := V.n
  let mut rows : Array (Array (Nat × Nat × Rat)) := #[]
  for β in lc.blades n do
    let src := if complement then lowMask n ^^^ β else β
    let c : Rat := match Kernel.unTermsC V op src with
      | .ok ts => (ts.find? fun t => t.bits == β && t.z == 0).map (·.coef) |>.getD 0
      | .error _ => 0
    rows := rows.push (if la.contains n src then #[(la.rank n src, 0, c)] else #[])
  return Loops.ofRowsKeep rows

/-- Whether the generated unary kernels of `ops` compute Julia's entry-wise maps on every
container layout (`planned`: the space's planned kernels). -/
def unaryExact (V : TensorBundle) (planned : Array Planned) (ops : List UnOp) (complement : Bool) : Bool :=
  let n := V.n
  ops.all fun op => (allLayouts n).all fun la =>
    let lc := unaryResult n op la
    match planned.find? fun pl => pl.spec.field == .un && pl.spec.key.op == .un op &&
        pl.spec.key.la == la && pl.spec.key.lc == lc with
    | some pl => samePlan pl.plan (juliaUnaryPlan V op la lc complement)
    | none => false

/-- The dynamic layer's loops of `V` against the planned typed kernels (`pre`: their prefix);
empty when `V` does not qualify (more than five generators, tangent or dyadic generators). A
loop that needs a dedicated kernel of more than `maxEntries` entries is left to the interpreted
plans (the dispatch's fallback). -/
def planDynLoops (V : TensorBundle) (pre : Name) (planned : Array Planned) (maxEntries : Nat := 4096) :
    Array DynLoop := Id.run do
  if V.n > 5 || V.istangent || V.diffvars != 0 || V.dyadmode != 0 then return #[]
  let mut out := #[]
  for (op, la, lb, lc) in dynKeys V do
    let plan := Loops.build { V, op, a := .dense la, b := .dense lb, lc, outerFirst := true }
    let alias := planned.find? fun pl => pl.spec.field == .bin && pl.spec.key.op == .bin op &&
        pl.spec.key.la == la && pl.spec.key.lb == lb && pl.spec.key.lc == lc
    let alias := alias.bind fun pl => if samePlan pl.plan plan then some (kernelName pre pl.spec) else none
    if alias.isSome || plan.size ≤ maxEntries then out := out.push { op, la, lb, lc, plan, alias }
  return out

/-- The declaration name of an emitted loop kernel. -/
def dynLoopName (pre : Name) (d : DynLoop) : Name :=
  pre ++ Name.mkSimple s!"k_loop_{opTag (.bin d.op)}_{layoutTag d.la}_{layoutTag d.lb}_{layoutTag d.lc}"

/-- Julia's loop through the interpreted plans, out of line (the fallback of the generated
dispatch). -/
@[noinline, specialize] def dynLoopOut {α : Type} [Coeff α] (V : TensorBundle) (op : BinOp) (la lb lc : Layout)
    (x : Values α (la.size V.n)) (y : Values α (lb.size V.n)) : Values α (lc.size V.n) :=
  Loops.run true { V, op, a := .dense la, b := .dense lb, lc, outerFirst := true } x.data y.data

/-- Emit the loop kernels of `loops` that no typed kernel computes, the dispatcher `pre.dynLoop`
and the `DynKernels` instance of the space `V` (`Vrt`: its run-time value). Returns the number
of kernels emitted. -/
def emitDyn (space : TensorBundle) (V Vrt : Term) (pre : Name) (planned : Array Planned)
    (loops : Array DynLoop) (coefs : Array (Rat × Name)) : CommandElabM Nat := do
  if loops.isEmpty then return 0
  let n := space.n
  let mut names := #[]
  for d in loops do
    if d.alias.isNone then
      let nm := dynLoopName pre d
      liftTermElabM <| addKernel nm s!"Generated Julia loop (`Grassmann.DynKernels`): `{opTag (.bin d.op)}` of \
        {layoutDoc d.la} × {layoutDoc d.lb} → {layoutDoc d.lc} in `{space}` in Julia's order, \
        {d.plan.size} entries." false (d.la.size n) (d.lb.size n) (d.lc.size n) d.plan coefs
      names := names.push nm
  compileKernels names
  let nLit : Term := quote n
  let (op, la, lb, lc, x, y) := (mkIdent `op, mkIdent `la, mkIdent `lb, mkIdent `lc, mkIdent `x, mkIdent `y)
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for d in loops do
    let k := d.alias.getD (dynLoopName pre d)
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(opStx (.bin d.op)), $(← layoutStx d.la), $(← layoutStx d.lb), $(← layoutStx d.lc), $x, $y =>
        $(mkCIdent k) $x $y))
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
    | $op, $la, $lb, $lc, $x, $y => Grassmann.Kernel.Codegen.dynLoopOut $Vrt $op $la $lb $lc $x $y))
  let dnm := pre ++ `dynLoop
  elabCommand (← `(command|
    @[inline] def $(mkIdent (`_root_ ++ dnm)) {α : Type} [AbstractTensors.Coeff α] ($op : DirectSum.BinOp)
        ($la $lb $lc : DirectSum.Layout)
        ($x : StaticVectors.Values α (DirectSum.Layout.size $nLit $la))
        ($y : StaticVectors.Values α (DirectSum.Layout.size $nLit $lb)) :
        StaticVectors.Values α (DirectSum.Layout.size $nLit $lc) :=
      match $op:ident, $la:ident, $lb:ident, $lc:ident, $x:ident, $y:ident with $alts:matchAlt*))
  addDocStringCore dnm s!"Generated dispatch of Julia's loops in `{space}` (`Grassmann.DynKernels`): \
    {loops.size} keys, {names.size} dedicated kernels."
  let signs := unaryExact space planned [.reverse, .involute, .clifford, .antireverse] false &&
    unaryExact space planned [.complementright, .complementleft] true
  let hodges := space.isdiag && unaryExact space planned [.complementrighthodge, .complementlefthodge] true
  let fast := space.dynFastShape && signs && hodges && loops.all (·.alias.isSome)
  let instId := mkIdent (`_root_ ++ pre ++ `instDynKernels)
  let lit (b : Bool) : Term := if b then mkCIdent ``true else mkCIdent ``false
  elabCommand (← `(command|
    /-- The generated Julia loops of this space (`Grassmann.DynKernels`). -/
    instance $instId:ident : Grassmann.DynKernels $V where
      fast := $(lit fast)
      signs := $(lit signs)
      hodges := $(lit hodges)
      loops := true
      loop := fun $op $la $lb $lc $x $y => $(mkCIdent dnm) $op $la $lb $lc $x $y))
  return names.size

end Grassmann.Kernel.Codegen
