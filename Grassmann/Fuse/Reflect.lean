/-
Reflection of typed-algebra expressions into the symbolic scalar graph (`Grassmann.Fuse`).

`reflectVals e` evaluates, at elaboration time, a term `e : Values α n` built by the typed
operations into one graph node per coefficient. It does not interpret operator *names*: it
unfolds the typed layer's own definitions (operator classes through their instances,
`@[inline]` helpers, `let`s, `match`es and `if`s on closed data) until it reaches the
primitives the whole layer is built from, and gives each primitive its exact meaning:

| primitive | meaning |
|---|---|
| `Kernels.bin/binProj/un/unProj` (standard instances) | the reference plan of the key, in the generated kernels' order |
| `SandwichKernels.sandwich/tsandwich` (standard instances) | the two plans of `sandwichTwo`/`tsandwichTwo` |
| `Values.zipWith f`, `Values.map f`, `Values.replicate`, `Values.ofFn` | `f` applied to the coefficient nodes |
| `convertLayout n la lc`, `zeroValues n`, `Values.cast` | re-indexing, zeros, identity |
| `+ - * neg` of the coefficient type, `Coeff.zero/one/ofRat/ofInt`, integer literals | graph nodes |
| `Values.get v i` (closed `i`) | coefficient `i` of `v` |

A `Kernels`/`SandwichKernels` instance is *standard* when it is the reference instance or one
emitted by `grassmann_kernels`/`basis!` (`Grassmann.Kernel.Codegen.kernelRegistry`): those
compute exactly the plans. Everything else (a user instance, a coefficient function such as
`Float.sqrt`, a runtime branch, a loop) becomes an opaque **leaf**: evaluated at run time as
written and read coefficient by coefficient (vectors), or an opaque scalar or opaque scalar
function of graph nodes (coefficients). Reflection therefore never fails and never changes
the meaning of an expression; it only decides how much of it runs as one straight-line block.
-/
import Grassmann.Fuse.Graph
import Grassmann.Kernel.Codegen
import Lean.Meta.Eval
import Lean.Compiler.InlineAttrs

namespace Grassmann.Fuse

open Lean Meta Elab
open DirectSum StaticVectors AbstractTensors Grassmann.Kernel

initialize registerTraceClass `grassmann.fuse

/-- A run-time vector the fused code reads: `expr : Values α size`. -/
structure Leaf where
  /-- The vector expression (evaluated once, at the top of the fused code). -/
  expr : Expr
  /-- Its length. -/
  size : Nat
  deriving Inhabited

/-- Fixed data of one reflection: the coefficient type and its `Coeff` instance. -/
structure Ctx where
  /-- The coefficient type `α`. -/
  α : Expr
  /-- The `Coeff α` instance. -/
  instC : Expr
  /-- Maximum number of unfolding steps (a guard against runaway unfolding). -/
  fuel : Nat := 100000

/-- Mutable state of one reflection. -/
structure State where
  /-- The scalar graph. -/
  g : Graph := {}
  /-- The run-time vectors read. -/
  leaves : Array Leaf := #[]
  /-- Opaque scalars (closed terms of type `α` in the caller's context). -/
  scalars : Array Expr := #[]
  /-- Opaque scalar functions (closed lambdas `α → … → α`). -/
  fns : Array Expr := #[]
  /-- Scalar free variables bound by reflected lambdas, and their nodes. -/
  locals : Std.HashMap FVarId Nat := {}
  /-- Plans built so far. -/
  plans : Array (PlanKey × Plan) := #[]
  /-- Spaces evaluated so far. -/
  spaces : Array (Expr × TensorBundle) := #[]
  /-- Accepted (`true`) or rejected scalar instances. -/
  instOk : Std.HashMap Expr Bool := {}
  /-- Kernel calls reflected (a statistic for the trace). -/
  kernels : Nat := 0
  /-- Unfolding steps taken. -/
  steps : Nat := 0

/-- The reflection monad. -/
abbrev M := ReaderT Ctx (StateRefT State MetaM)

/-! ## Evaluating closed data -/

private unsafe def evalAtUnsafe (β : Type) (ty : Expr) (e : Expr) : MetaM β := do
  evalExpr β ty (← instantiateMVars e)

@[implemented_by evalAtUnsafe]
private opaque evalAtRaw (β : Type) (ty : Expr) (e : Expr) : MetaM β

/-- Evaluate a closed term with the compiler (`Meta.evalExpr`). Refuses open terms, and keeps
the message log unchanged (a failed evaluation reports through the log, not only by throwing). -/
def evalAt (β : Type) (ty : Expr) (e : Expr) : MetaM β := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then throwError "fused%: cannot evaluate an open term{indentExpr e}"
  let msgs := (← getThe Core.State).messages
  try
    let r ← evalAtRaw β ty e
    modifyThe Core.State fun s => { s with messages := msgs }
    return r
  catch ex =>
    modifyThe Core.State fun s => { s with messages := msgs }
    throw ex

/-- A closed natural number (literal, or reduced, or evaluated). -/
partial def natOf (e : Expr) : MetaM Nat := do
  let e ← instantiateMVars e
  if let some n := e.rawNatLit? then return n
  if let some n := e.nat? then return n
  let w ← whnfD e
  if let some n := w.rawNatLit? then return n
  if let some n := w.nat? then return n
  if w.isAppOfArity ``Nat.succ 1 then return (← natOf w.appArg!) + 1
  evalAt Nat (mkConst ``Nat) e

/-- A closed Boolean. -/
def boolOf (e : Expr) : MetaM Bool := do
  let w ← whnfD (← instantiateMVars e)
  if w.isConstOf ``Bool.true then return true
  if w.isConstOf ``Bool.false then return false
  evalAt Bool (mkConst ``Bool) e

/-- A closed layout (decoded from its constructor). -/
def layoutOf (e : Expr) : MetaM Layout := do
  let w ← whnfD (← instantiateMVars e)
  match w.getAppFn.constName?, w.getAppArgs with
  | some ``DirectSum.Layout.chain, #[g] => return .chain (← natOf g)
  | some ``DirectSum.Layout.even, #[] => return .even
  | some ``DirectSum.Layout.odd, #[] => return .odd
  | some ``DirectSum.Layout.full, #[] => return .full
  | _, _ => evalAt Layout (mkConst ``DirectSum.Layout) e

/-- The short constructor name of an operation (`mul`, `complementright`, ...). -/
def opName {β : Type} [Repr β] (o : β) : String := ((reprStr o).splitOn ".").getLast!

/-- A closed binary operation (decoded from its constructor). -/
def binOpOf (e : Expr) : MetaM BinOp := do
  let w ← whnfD (← instantiateMVars e)
  if let .const n _ := w then
    if let some o := BinOp.all.find? (opName · == n.getString!) then return o
  evalAt BinOp (mkConst ``DirectSum.BinOp) e

/-- A closed unary operation (decoded from its constructor). -/
def unOpOf (e : Expr) : MetaM UnOp := do
  let w ← whnfD (← instantiateMVars e)
  if let .const n _ := w then
    if let some o := UnOp.all.find? (opName · == n.getString!) then return o
  evalAt UnOp (mkConst ``DirectSum.UnOp) e

/-- A closed rational. -/
def ratOf (e : Expr) : MetaM Rat := evalAt Rat (mkConst ``Rat) e

/-- A closed integer. -/
def intOf (e : Expr) : MetaM Int := evalAt Int (mkConst ``Int) e

/-- The space denoted by a closed term (cached). -/
def spaceOf (e : Expr) : M TensorBundle := do
  let e ← instantiateMVars e
  if let some (_, V) := (← get).spaces.find? (·.1 == e) then return V
  let V ← evalAt TensorBundle (mkConst ``DirectSum.TensorBundle) e
  modify fun s => { s with spaces := s.spaces.push (e, V) }
  return V

/-- The plan of a key (cached). -/
def planOf (k : PlanKey) : M Plan := do
  if let some (_, p) := (← get).plans.find? (·.1 == k) then return p
  match build k with
  | .ok p =>
    modify fun s => { s with plans := s.plans.push (k, p) }
    return p
  | .error msg => throwError "fused%: plan of {repr k.op} failed: {msg}"

/-- The length `n` of a term of type `Values α n`. -/
def valuesSize (e : Expr) : MetaM Nat := do
  let ty ← whnfR (← inferType e)
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``StaticVectors.Values, #[_, _, n] => natOf n
  | _, _ => throwError "fused%: expected a `Values` term, got{indentExpr e}\nof type{indentExpr ty}"

/-! ## Standard instances -/

/-- Whether a `Kernels V` instance computes exactly the reference plans: the reference
instance, or one emitted by `grassmann_kernels`/`basis!` for `V`. -/
def standardKernels (inst : Expr) : MetaM Bool := do
  let inst ← instantiateMVars inst
  match inst.getAppFn with
  | .const n _ =>
    if n == ``Grassmann.Kernels.reference then return true
    if n.getString! == "instKernels" then
      let env ← getEnv
      return (Codegen.kernelRegistry.getState env).fold (init := false) fun ok _ pre =>
        ok || pre ++ `instKernels == n
    return false
  | _ => return false

/-- Whether a `SandwichKernels V` instance computes the two-kernel sandwiches (the reference
instance over a standard `Kernels V`, or a generated one), and the `Kernels V` instance its
semantics reads. -/
def standardSandwich (V inst : Expr) : MetaM (Option Expr) := do
  let inst ← instantiateMVars inst
  match inst.getAppFn with
  | .const n _ =>
    if n == ``Grassmann.SandwichKernels.reference then
      let k := inst.getAppArgs[1]!
      return if ← standardKernels k then some k else none
    if n.getString! == "instSandwichKernels" then
      let env ← getEnv
      let ok := (Codegen.kernelRegistry.getState env).fold (init := false) fun ok _ pre =>
        ok || pre ++ `instSandwichKernels == n
      if !ok then return none
      let k ← synthInstance (mkApp (mkConst ``Grassmann.Kernels) V)
      return if ← standardKernels k then some k else none
    return none
  | _ => return none

/-! ## Graph helpers -/

/-- Run a graph operation. -/
@[inline] def gop {β : Type} (f : Graph → Graph × β) : M β := do
  let (g, r) := f (← get).g
  modify fun s => { s with g }
  return r

/-- A vector of zeros. -/
def zerosV (n : Nat) : Array Nat := Array.replicate n Graph.zero

/-- The node vector of leaf `e` (registering it). -/
def leafV (e : Expr) : M (Array Nat) := do
  let e ← instantiateMVars e
  let n ← valuesSize e
  let st ← get
  let i ← match st.leaves.findIdx? (·.expr == e) with
    | some i => pure i
    | none =>
      modify fun s => { s with leaves := s.leaves.push { expr := e, size := n } }
      pure st.leaves.size
  let mut out := #[]
  for j in [0:n] do out := out.push (← gop (·.intern (.input i j)))
  return out

/-- The node of an opaque scalar `e : α` that mentions reflected locals only through `deps`. -/
def opaqueScalar (e : Expr) : M Nat := do
  let e ← instantiateMVars e
  let st ← get
  let deps := st.locals.toArray.filter fun (fv, _) => e.containsFVar fv
  if deps.isEmpty then
    let k ← match st.scalars.findIdx? (· == e) with
      | some k => pure k
      | none =>
        modify fun s => { s with scalars := s.scalars.push e }
        pure st.scalars.size
    gop (·.intern (.scalar k))
  else
    let fn ← mkLambdaFVars (deps.map (mkFVar ·.1)) e
    let f ← match st.fns.findIdx? (· == fn) with
      | some f => pure f
      | none =>
        modify fun s => { s with fns := s.fns.push fn }
        pure st.fns.size
    gop (·.ext f (deps.map (·.2)))

/-! ## Unfolding -/

/-- Constants that are never unfolded (they are primitives, or opaque by design). -/
def primitiveNames : List Name :=
  [``Grassmann.Kernels.bin, ``Grassmann.Kernels.binProj, ``Grassmann.Kernels.un,
   ``Grassmann.Kernels.unProj, ``Grassmann.SandwichKernels.sandwich,
   ``Grassmann.SandwichKernels.tsandwich, ``StaticVectors.Values.zipWith, ``StaticVectors.Values.map,
   ``StaticVectors.Values.cast, ``StaticVectors.Values.replicate, ``StaticVectors.Values.ofFn,
   ``StaticVectors.Values.get, ``Grassmann.convertLayout, ``Grassmann.zeroValues,
   ``AbstractTensors.Coeff.zero, ``AbstractTensors.Coeff.one, ``AbstractTensors.Coeff.ofRat,
   ``AbstractTensors.Coeff.ofInt]

/-- Whether constant `n` may be unfolded: `@[inline]`/`@[macro_inline]`/reducible definitions
and instances (the typed layer's operators and helpers), never loops or opaque definitions. -/
def unfoldable (n : Name) : MetaM Bool := do
  let env ← getEnv
  if primitiveNames.contains n then return false
  let some info := env.find? n | return false
  unless info.hasValue do return false
  if Compiler.hasInlineAttribute env n || Compiler.hasMacroInlineAttribute env n then return true
  if (← getReducibilityStatus n) matches .reducible then return true
  return isInstanceCore env n

/-- Whether `e` is (after unfolding) a constructor application. -/
def ctorApp? (e : Expr) : MetaM (Option (ConstructorVal × Array Expr)) := do
  match e.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.ctorInfo c) => return some (c, e.getAppArgs)
    | _ => return none
  | _ => return none

mutual

/-- One unfolding step of `e`, or `none` when `e` is stuck (a primitive, a free variable, an
opaque function, a branch on run-time data). -/
partial def step? (e : Expr) : M (Option Expr) := do
  modify fun s => { s with steps := s.steps + 1 }
  if (← get).steps > (← read).fuel then throwError "fused%: unfolding fuel exhausted"
  match e with
  | .mdata _ b => return some b
  | .letE _ _ v b _ => return some (b.instantiate1 v)
  | .proj sn i x =>
    let x' ← reduceFull x
    match ← ctorApp? x' with
    | some (c, args) => return args[c.numParams + i]?
    | none => return if x' == x then none else some (.proj sn i x')
  | .app .. =>
    let f := e.getAppFn
    if f.isLambda then return some e.headBeta
    let .const n _ := f | return none
    if n == ``id && e.getAppNumArgs ≥ 2 then
      return some (mkAppN e.getAppArgs[1]! (e.getAppArgs.extract 2))
    if primitiveNames.contains n then return none
    -- structure and class projections
    if let some info ← getProjectionFnInfo? n then
      if info.fromClass then
        return ← unfoldProjInst? e
      let args := e.getAppArgs
      let some x := args[info.numParams]? | return none
      let x' ← reduceFull x
      match ← ctorApp? x' with
      | some (c, cargs) =>
        let some fld := cargs[c.numParams + info.i]? | return none
        return some (mkAppN fld (args.extract (info.numParams + 1)))
      | none => return if x' == x then none else some (mkAppN f (args.set! info.numParams x'))
    -- `match`es and `if`s on closed data
    if ← isMatcher n then
      match ← reduceMatcher? e with
      | .reduced e' => return some e'
      | _ => return none
    if (n == ``ite || n == ``dite) && e.getAppNumArgs ≥ 5 then
      let args := e.getAppArgs
      let d ← whnfD args[2]!
      let mut branch := if d.isAppOfArity ``Decidable.isTrue 2 then some (true, d.appArg!)
        else if d.isAppOfArity ``Decidable.isFalse 2 then some (false, d.appArg!) else none
      if branch.isNone && !args[1]!.hasFVar && !args[1]!.hasMVar then
        -- a closed condition that `whnf` does not decide: evaluate it (the proof is by `decide`)
        let c := args[1]!
        let b ← evalAt Bool (mkConst ``Bool) (mkApp2 (mkConst ``Decidable.decide) c args[2]!)
        let refl (v : Name) := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst v)
        branch := some (b, if b then mkApp3 (mkConst ``of_decide_eq_true) c args[2]! (refl ``Bool.true)
          else mkApp3 (mkConst ``of_decide_eq_false) c args[2]! (refl ``Bool.false))
      let some (b, h) := branch | return none
      let br := if b then args[3]! else args[4]!
      let r := if n == ``dite then mkApp br h else br
      return some (mkAppN r (args.extract 5)).headBeta
    if n == ``cond && e.getAppNumArgs ≥ 4 then
      let args := e.getAppArgs
      let c ← whnfD args[1]!
      if c.isConstOf ``Bool.true then return some (mkAppN args[2]! (args.extract 4))
      if c.isConstOf ``Bool.false then return some (mkAppN args[3]! (args.extract 4))
      return none
    -- one-hot elements of a literal blade (`2.0 * v₁` as a chain): unfold, so that the blade's
    -- storage position folds at elaboration time; a run-time blade stays a leaf
    if n == ``Grassmann.Chain.ofBlade || n == ``Grassmann.Half.ofBlade ||
        n == ``Grassmann.Multivector.ofBlade then
      let args := e.getAppArgs
      -- the space, the grade and the blade argument of each constructor
      let pos := if n == ``Grassmann.Chain.ofBlade then (0, 1, 4)
        else if n == ``Grassmann.Half.ofBlade then (0, 4, 5) else (0, 3, 4)
      let (some V, some G, some b) := (args[pos.1]?, args[pos.2.1]?, args[pos.2.2]?) | return none
      let bits ← reduceFull (mkApp3 (mkConst ``DirectSum.Submanifold.bits) V G b)
      if bits.hasFVar || bits.hasMVar then return none
      -- the blade as a literal, then the definition
      let e' := mkAppN e.getAppFn (args.set! pos.2.2 (mkApp3 (mkConst ``DirectSum.Submanifold.mk) V G bits))
      return ← unfoldDefinition? e' (ignoreTransparency := true)
    if ← unfoldable n then
      return ← unfoldDefinition? e (ignoreTransparency := true)
    return none
  | _ => return none

/-- Unfold `e` until it is a constructor application or stuck. -/
partial def reduceFull (e : Expr) : M Expr := do
  if (← ctorApp? e).isSome then return e
  match ← step? e with
  | some e' => reduceFull e'
  | none => return e

end

/-! ## Reflection -/

/-- Accept a scalar arithmetic instance (`HAdd α α α` etc.) when it is the one the kernels use
(`Coeff`'s), up to instance reduction. -/
def scalarInstOk (canonical inst : Expr) : M Bool := do
  let inst ← instantiateMVars inst
  if let some b := (← get).instOk.get? inst then return b
  let ok ← withReducibleAndInstances <| isDefEq inst canonical
  modify fun s => { s with instOk := s.instOk.insert inst ok }
  return ok

/-- The canonical `HAdd α α α` (etc.) instance of the coefficient type. -/
def canonicalInst (cls : Name) : M Expr := do
  let { α, instC, .. } ← read
  return match cls with
  | ``HAdd.hAdd => mkApp2 (mkConst ``instHAdd [0]) α (mkApp2 (mkConst ``Coeff.toAdd) α instC)
  | ``HSub.hSub => mkApp2 (mkConst ``instHSub [0]) α (mkApp2 (mkConst ``Coeff.toSub) α instC)
  | ``HMul.hMul => mkApp2 (mkConst ``instHMul [0]) α (mkApp2 (mkConst ``Coeff.toMul) α instC)
  | _ => mkApp2 (mkConst ``Coeff.toNeg) α instC

/-- Whether `ty` is the coefficient type. -/
def isCoeffType (ty : Expr) : M Bool := do
  let ty ← instantiateMVars ty
  if ty == (← read).α then return true
  withReducible <| isDefEq ty (← read).α

mutual

/-- The node vector of a term `e : Values α n`; a term that cannot be reflected (open data,
a failing plan) is a leaf. -/
partial def reflectVals (e : Expr) : M (Array Nat) := do
  try reflectValsCore e
  catch ex => if ex.isRuntime then throw ex else leafV e

/-- The node of a term `e : α`; a term that cannot be reflected is an opaque scalar. -/
partial def reflectScalar (e : Expr) : M Nat := do
  try reflectScalarCore e
  catch ex => if ex.isRuntime then throw ex else opaqueScalar e

/-- `reflectVals` without the fallback. -/
partial def reflectValsCore (e : Expr) : M (Array Nat) := do
  let e ← instantiateMVars e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const n _ =>
    if (n == ``Grassmann.Kernels.bin || n == ``Grassmann.Kernels.binProj) && args.size == 10 then
      if ← standardKernels args[1]! then
        let V ← spaceOf args[0]!
        let op ← binOpOf args[4]!
        let (la, lb, lc) := (← layoutOf args[5]!, ← layoutOf args[6]!, ← layoutOf args[7]!)
        let p ← planOf { V, op := .bin op, la, lb, lc, project := n == ``Grassmann.Kernels.binProj }
        let x ← reflectVals args[8]!
        let y ← reflectVals args[9]!
        modify fun s => { s with kernels := s.kernels + 1 }
        return ← gop (·.apply₂ p x y)
      return ← leafV e
    if (n == ``Grassmann.Kernels.un || n == ``Grassmann.Kernels.unProj) && args.size == 8 then
      if ← standardKernels args[1]! then
        let V ← spaceOf args[0]!
        let op ← unOpOf args[4]!
        let (la, lc) := (← layoutOf args[5]!, ← layoutOf args[6]!)
        let p ← planOf { V, op := .un op, la, lb := la, lc, project := n == ``Grassmann.Kernels.unProj }
        let x ← reflectVals args[7]!
        modify fun s => { s with kernels := s.kernels + 1 }
        return ← gop (·.apply₁ p x)
      return ← leafV e
    if (n == ``Grassmann.SandwichKernels.sandwich || n == ``Grassmann.SandwichKernels.tsandwich)
        && args.size == 8 then
      if let some k ← standardSandwich args[0]! args[1]! then
        let Ve := args[0]!
        let V ← spaceOf Ve
        let (lr, lx) := (← layoutOf args[4]!, ← layoutOf args[5]!)
        let lt := Kernel.sandwichMid lr lx
        let r ← reflectVals args[6]!
        let x ← reflectVals args[7]!
        let second ← planOf { V, op := .bin .mul, la := lt, lb := lr, lc := lx, project := true }
        modify fun s => { s with kernels := s.kernels + 1 }
        let _ := k
        if n == ``Grassmann.SandwichKernels.sandwich then
          -- `sandwichCore lr lx lt lx (parityOf lr)`
          let first ← planOf { V, op := .bin .reverseMul, la := lr, lb := lx, lc := lt }
          let t ← gop (·.apply₂ first r x)
          match Codegen.parityOf lr with
          | some odd =>
            if V.diffvars == 0 then
              let res ← gop (·.apply₂ second t r)
              return ← if odd then gop (·.mapV Graph.neg res) else pure res
            let inv ← planOf { V, op := .un .involute, la := lr, lb := lr, lc := lr }
            let ri ← gop (·.apply₁ inv r)
            return ← gop (·.apply₂ second t ri)
          | none =>
            let inv ← planOf { V, op := .un .involute, la := lr, lb := lr, lc := lr }
            let ri ← gop (·.apply₁ inv r)
            return ← gop (·.apply₂ second t ri)
        else
          let first ← planOf { V, op := .bin .mul, la := lr, lb := lx, lc := lt }
          let cl ← planOf { V, op := .un .clifford, la := lr, lb := lr, lc := lr }
          let t ← gop (·.apply₂ first r x)
          let rc ← gop (·.apply₁ cl r)
          return ← gop (·.apply₂ second t rc)
      return ← leafV e
    if n == ``StaticVectors.Values.zipWith && args.size ≥ 3 then
      let x ← reflectVals args[args.size - 2]!
      let y ← reflectVals args[args.size - 1]!
      let f := args[args.size - 3]!
      let α := (← read).α
      return ← withLocalDeclD `a α fun a => withLocalDeclD `b α fun b => do
        let body := (mkApp2 f a b).headBeta
        let mut out := #[]
        for (xi, yi) in x.zip y do
          modify fun s => { s with locals := (s.locals.insert a.fvarId! xi).insert b.fvarId! yi }
          out := out.push (← reflectScalar body)
        modify fun s => { s with locals := (s.locals.erase a.fvarId!).erase b.fvarId! }
        return out
    if n == ``StaticVectors.Values.map && args.size ≥ 2 then
      let x ← reflectVals args[args.size - 1]!
      let f := args[args.size - 2]!
      let α := (← read).α
      return ← withLocalDeclD `a α fun a => do
        let body := (mkApp f a).headBeta
        let mut out := #[]
        for xi in x do
          modify fun s => { s with locals := s.locals.insert a.fvarId! xi }
          out := out.push (← reflectScalar body)
        modify fun s => { s with locals := s.locals.erase a.fvarId! }
        return out
    if n == ``StaticVectors.Values.cast && args.size ≥ 1 then
      return ← reflectVals args[args.size - 1]!
    if n == ``StaticVectors.Values.replicate && args.size ≥ 1 then
      let k ← valuesSize e
      let x ← reflectScalar args[args.size - 1]!
      return Array.replicate k x
    if n == ``StaticVectors.Values.ofFn && args.size ≥ 1 then
      let k ← valuesSize e
      if k > 256 then return ← leafV e
      let f := args[args.size - 1]!
      let mut out := #[]
      for i in [0:k] do
        let fi := mkApp3 (mkConst ``Fin.mk) (mkRawNatLit k) (mkRawNatLit i) (Codegen.Arith.ltProof i k)
        out := out.push (← reflectScalar (mkApp f fi).headBeta)
      return out
    if n == ``Grassmann.zeroValues && args.size == 3 then
      return zerosV (← natOf args[2]!)
    if n == ``Grassmann.convertLayout && args.size == 6 then
      let nn ← natOf args[2]!
      let (la, lc) := (← layoutOf args[3]!, ← layoutOf args[4]!)
      let x ← reflectVals args[5]!
      let bs := lc.blades nn
      return bs.map fun b => if la.contains nn b then x[la.rank nn b]?.getD Graph.zero else Graph.zero
    match ← step? e with
    | some e' => reflectVals e'
    | none => leafV e
  | _ =>
    match ← step? e with
    | some e' => reflectVals e'
    | none => leafV e

/-- `reflectScalar` without the fallback. -/
partial def reflectScalarCore (e : Expr) : M Nat := do
  let e ← instantiateMVars e
  if let .fvar fv := e then
    if let some i := (← get).locals.get? fv then return i
    return ← opaqueScalar e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const n _ =>
    if (n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul) && args.size == 6 then
      if (← isCoeffType args[0]!) && (← isCoeffType args[1]!) && (← isCoeffType args[2]!) &&
          (← scalarInstOk (← canonicalInst n) args[3]!) then
        let a ← reflectScalar args[4]!
        let b ← reflectScalar args[5]!
        return ← gop fun g =>
          if n == ``HAdd.hAdd then g.add a b else if n == ``HSub.hSub then g.sub a b else g.mul a b
      return ← opaqueScalar e
    if n == ``Neg.neg && args.size == 3 then
      if (← isCoeffType args[0]!) && (← scalarInstOk (← canonicalInst n) args[1]!) then
        let a ← reflectScalar args[2]!
        return ← gop (·.neg a)
      return ← opaqueScalar e
    if (n == ``AbstractTensors.Coeff.zero) && args.size == 2 then return Graph.zero
    if (n == ``AbstractTensors.Coeff.one) && args.size == 2 then return Graph.one
    if n == ``AbstractTensors.Coeff.ofRat && args.size == 3 then
      if !args[2]!.hasFVar then
        let q ← ratOf args[2]!
        return ← gop (·.const q)
      return ← opaqueScalar e
    if n == ``AbstractTensors.Coeff.ofInt && args.size == 3 then
      if !args[2]!.hasFVar then
        let z ← intOf args[2]!
        return ← gop (·.const z)
      return ← opaqueScalar e
    if n == ``OfNat.ofNat && args.size == 3 then
      -- an integer literal of the coefficient type: exact
      if (← isCoeffType args[0]!) then
        if let some k := args[1]!.rawNatLit? then
          if k < 2 ^ 53 then return ← gop (·.const k)
      return ← opaqueScalar e
    if n == ``StaticVectors.Values.get && args.size == 5 then
      let v ← reflectVals args[3]!
      let i ← (do
        let fi ← instantiateMVars args[4]!
        match fi.getAppFn.constName?, fi.getAppArgs with
        | some ``Fin.mk, #[_, iv, _] => natOf iv
        | _, _ => evalAt Nat (mkConst ``Nat) (mkApp2 (mkConst ``Fin.val) (← natOf args[2]! <&> mkRawNatLit) fi))
      return v[i]?.getD Graph.zero
    if n == ``HDiv.hDiv && args.size == 6 then
      if (← isCoeffType args[0]!) && (← isCoeffType args[1]!) && (← isCoeffType args[2]!) then
        -- the coefficient type's own division, as an opaque binary function of two nodes
        let α := (← read).α
        let fn ← withLocalDeclD `a α fun a => withLocalDeclD `b α fun b =>
          mkLambdaFVars #[a, b] (mkAppN e.getAppFn (args.extract 0 4 ++ #[a, b]))
        let x ← reflectScalar args[4]!
        let y ← reflectScalar args[5]!
        let st ← get
        let f ← match st.fns.findIdx? (· == fn) with
          | some f => pure f
          | none =>
            modify fun s => { s with fns := s.fns.push fn }
            pure st.fns.size
        return ← gop (·.div' f x y)
      return ← opaqueScalar e
    if primitiveNames.contains n || n == ``HAdd.hAdd || n == ``HSub.hSub || n == ``HMul.hMul ||
        n == ``HDiv.hDiv || n == ``Neg.neg then
      return ← opaqueScalar e
    match ← step? e with
    | some e' => reflectScalar e'
    | none => opaqueScalar e
  | _ =>
    match ← step? e with
    | some e' => reflectScalar e'
    | none => opaqueScalar e

end

end Grassmann.Fuse
