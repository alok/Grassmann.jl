import Grassmann.Fuse.Emit

/-!
# Expression fusion: `fused% e`

Every typed operation of the algebra returns a fresh `FloatArray`, so an expression such as
`R * v * ~R` allocates three times and passes its intermediates through memory: Lean does not
scalar-replace aggregates across calls (docs/PERF.md: an allocation costs ≈ 10 ns, the ℝ3
kernels themselves 1–5 ns). Julia's `isbits` results never leave registers.

`fused% e` elaborates `e` as usual and then compiles the **whole expression** into one
straight-line block at elaboration time: it evaluates the typed layer's definitions on
symbolic coefficients (`Grassmann.Fuse.Reflect`: the product plans of the space's kernels,
`+`, `-`, scalar multiples, reverses, complements, conversions, grade projections, ...) into a
hash-consed scalar graph with common subexpressions shared (`Grassmann.Fuse.Graph`) and emits
one `let` per node and one result buffer (`Grassmann.Fuse.Emit`).

* **Same type, same values.** The result has exactly the type of `e` (a `Chain`, `Half`,
  `Multivector`, or a coefficient). The products use the same plans in the same summation order
  as the generated kernels, so the result equals the unfused one bit for bit up to the sign of
  zero for finite inputs (`Tests/Fuse`).
* **One allocation** for a container result (none when it is written into an exclusive operand
  of the same length), **none** for a scalar result such as `fused% ((a * b).scalar ...)`.
* **Anything else stays as written**: operands that are not typed expressions (function calls,
  loops, run-time branches, user instances) are evaluated as usual and read coefficient by
  coefficient; `fused%` never changes the meaning of `e`.

The space must be a closed term (`ℝ3`, `STA`, a `basis!` space, ...): fusion happens at
elaboration time, like the generated kernels (DESIGN.md §5.2). In code generic over the space,
operations stay unfused.

```lean
open Grassmann in
def rotate (R : Spinor ℝ3 Float) (v : Chain ℝ3 1 Float) : CoSpinor ℝ3 Float :=
  fused% (R * v * ~R)      -- one kernel, one allocation (unfused: three of each)
```

`set_option trace.grassmann.fuse true` reports the kernel calls fused, the nodes and
operations emitted and the leaves read.
-/

namespace Grassmann.Fuse

open Lean Meta Elab Term
open DirectSum StaticVectors AbstractTensors Grassmann.Kernel Grassmann.Kernel.Codegen

/-- The coefficient type, its `Coeff` instance, and (for a container) the constructor and
parameters of the result type `T`. -/
structure Target where
  /-- Coefficient type. -/
  α : Expr
  /-- `Coeff α`. -/
  instC : Expr
  /-- `some (ctor, params)` for a container result, `none` for a scalar result. -/
  ctor? : Option (Expr × Array Expr)
  /-- The field projection of a container result. -/
  proj? : Option Name

/-- Classify the type of a fused expression. -/
def target? (T : Expr) : MetaM (Option Target) := do
  let T ← instantiateMVars T
  let Tw ← whnfR T
  if let .const sn us := Tw.getAppFn then
    if let some info := getStructureInfo? (← getEnv) sn then
      if info.fieldNames.size == 1 then
        let ctor := getStructureCtor (← getEnv) sn
        -- the single field must be a `Values α n`
        let fty ← withLocalDeclD `x Tw fun x => do
          whnfR (← inferType (← mkProjection x info.fieldNames[0]!))
        if fty.isAppOfArity ``StaticVectors.Values 3 then
          let α := fty.getArg! 0
          if let .some instC ← trySynthInstance (mkApp (mkConst ``AbstractTensors.Coeff) α) then
            return some { α, instC, ctor? := some (mkConst ctor.name us, Tw.getAppArgs.extract 0 ctor.numParams),
                          proj? := some info.fieldNames[0]! }
  if let .some instC ← trySynthInstance (mkApp (mkConst ``AbstractTensors.Coeff) T) then
    return some { α := T, instC, ctor? := none, proj? := none }
  return none

/-- Fuse the elaborated expression `e : T`. Returns `e` itself when nothing can be fused. -/
def fuseExpr (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasMVar then throwError "fused%: the expression has unassigned metavariables{indentExpr e}"
  let T ← inferType e
  let some tgt ← target? T
    | throwError "fused%: expected a `Chain`, `Half`, `Multivector` or coefficient-valued expression, got{indentExpr T}"
  let ctx : Ctx := { α := tgt.α, instC := tgt.instC }
  let t0 ← IO.monoMsNow
  let top ← match tgt.proj? with
    | some fld => mkProjection e fld
    | none => pure e
  let r ← try
      some <$> ((do
        match tgt.proj? with
        | some _ => reflectVals top
        | none => return #[← reflectScalar top] : M (Array Nat)).run ctx |>.run {})
    catch ex =>
      if ex.isRuntime then throw ex
      -- open data (a space or size that is not a closed term): nothing can be fused
      trace[grassmann.fuse] "not fused ({ex.toMessageData}):{indentExpr e}"
      pure none
  let some (outs, st) := r | return e
  -- nothing to fuse: the result is the expression itself, read back unchanged
  let identity := st.leaves.size == 1 && st.leaves[0]!.expr == top &&
    outs == (Array.range outs.size).map (fun j => st.g.index.getD (.input 0 j) outs.size)
  if identity || (tgt.proj?.isNone && st.scalars.size == 1 && st.scalars[0]! == top) then
    trace[grassmann.fuse] "nothing to fuse in{indentExpr e}"
    return e
  let res ← emitWith ctx st outs fun ar os leafVar => do
    match tgt.ctor? with
    | none => return os[0]!
    | some (ctor, params) =>
      let nc := os.size
      -- write into a leaf of the output's length (in place when it is exclusive), else a copy
      -- of the zero vector
      let base := (leafVar.zip st.leaves).findSome? (fun (v?, lf) => if lf.size == nc then v? else none)
        |>.getD (ar.zeros nc)
      return mkApp (mkAppN ctor params) (ar.packSet base os)
  let t1 ← IO.monoMsNow
  trace[grassmann.fuse] "fused {st.kernels} kernel calls: {(st.g.reachable outs).size} nodes, \
    {st.g.opCount outs} operations, {st.leaves.size} leaves, {st.scalars.size} scalars ({t1 - t0} ms)"
  for lf in st.leaves do trace[grassmann.fuse] "leaf: {lf.expr}"
  for sc in st.scalars do trace[grassmann.fuse] "opaque scalar: {sc}"
  return res

/-- `fused% e`: evaluate the typed-algebra expression `e` as one fused straight-line kernel with
a single result allocation (see the module documentation). -/
syntax (name := fusedStx) "fused% " term : term

@[term_elab fusedStx] def elabFused : TermElab := fun stx expected? => do
  match stx with
  | `(fused% $t) =>
    let e ← elabTerm t expected?
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let r ← fuseExpr e
    if r != e then
      -- the fused term must have the type of the unfused one
      check r
    return r
  | _ => throwUnsupportedSyntax

end Grassmann.Fuse
