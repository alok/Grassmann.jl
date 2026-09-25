/-
The batch elaborators `batch%` and `batchInto%` (`Grassmann.Batch`): a typed-algebra lambda
compiled into a loop over element-major batches, its body fused by `Grassmann.Fuse`.
-/
import Grassmann.Batch.Basic
import Grassmann.Fuse

namespace Grassmann.Fuse

open Lean Meta Elab
open DirectSum StaticVectors AbstractTensors Grassmann.Kernel Grassmann.Kernel.Codegen

/-- The target data and storage width of a container type (`Chain`/`Half`/`Multivector` with
`Float` coefficients). -/
def containerTarget (T : Expr) : MetaM (Target × Nat) := do
  let some tgt ← target? T | throwError "batch%: expected a Chain, Half or Multivector type, got{indentExpr T}"
  let some fld := tgt.proj? | throwError "batch%: expected a container type, got{indentExpr T}"
  unless ← isDefEq tgt.α (mkConst ``Float) do
    throwError "batch%: batches hold Float coefficients, got{indentExpr tgt.α}"
  let k ← withLocalDeclD `x T fun x => do valuesSize (← mkProjection x fld)
  return (tgt, k)

/-- A `USize` literal (compiled as an immediate). -/
def usizeLit (k : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [0]) (mkConst ``USize) (mkRawNatLit k)
    (mkApp (mkConst ``USize.instOfNat) (mkRawNatLit k))

/-- `USize` addition and multiplication heads (`HAdd.hAdd USize USize USize inst`, ...). -/
def usizeHeads : MetaM (Expr × Expr) := do
  let u := mkConst ``USize
  let hadd ← synthInstance (mkApp3 (mkConst ``HAdd [0, 0, 0]) u u u)
  let hmul ← synthInstance (mkApp3 (mkConst ``HMul [0, 0, 0]) u u u)
  return (mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) u u u hadd, mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) u u u hmul)

/-- Which binder a leaf reads (the leaf is `x.v` for the binder `x`), if any. -/
def binderOf (xs : Array Expr) (leaf : Expr) : Option Nat :=
  xs.findIdx? fun x => leaf.isApp && leaf.appArg! == x && leaf.getAppFn.isConst

/-- Compile the lambda `f` (binders of container types, a container-valued body) into a batch
kernel `Batch X₁ → … → Batch Xₘ → Batch Y`, or with `into`, `Batch Y → Batch X₁ → … → Batch Y`
(writing into the first argument's storage). -/
def batchKernel (f : Expr) (into : Bool) : MetaM Expr := do
  let f ← instantiateMVars f
  if f.hasMVar then throwError "batch%: the function has unassigned metavariables{indentExpr f}"
  lambdaTelescope f fun xs body => do
    if xs.isEmpty then throwError "batch%: expected a function of typed elements{indentExpr f}"
    let ins ← xs.mapM fun x => do containerTarget (← inferType x)
    let Y ← inferType body
    let (tgtY, kY) ← containerTarget Y
    let ctx : Ctx := { α := mkConst ``Float, instC := tgtY.instC }
    let top ← mkProjection body tgtY.proj?.get!
    let (outs, st) ← (reflectVals top : M (Array Nat)).run ctx |>.run {}
    -- every leaf is a binder's coefficient vector, or invariant (it mentions no binder)
    let mut leafBinder : Array (Option Nat) := #[]
    for lf in st.leaves do
      match binderOf xs lf.expr with
      | some b => leafBinder := leafBinder.push (some b)
      | none =>
        if xs.any (fun x => lf.expr.containsFVar x.fvarId!) then
          throwError "batch%: the element operand{indentExpr lf.expr}\ncannot be fused (a batch kernel \
            reads its operands' coefficients directly)"
        leafBinder := leafBinder.push none
    for sc in st.scalars do
      if xs.any (fun x => sc.containsFVar x.fvarId!) then
        throwError "batch%: the element scalar{indentExpr sc}\ncannot be fused"
    for fn in st.fns do
      if xs.any (fun x => fn.containsFVar x.fvarId!) then
        throwError "batch%: the element function{indentExpr fn}\ncannot be fused"
    let ar := Arith.new ctx.α ctx.instC
    let (addU, mulU) ← usizeHeads
    let usizeAdd (a b : Expr) := mkApp2 addU a b
    let usizeMul (a b : Expr) := mkApp2 mulU a b
    let batchTy (X : Expr) := mkApp (mkConst ``Grassmann.Batch) X
    let usize := mkConst ``USize
    let floatArr := mkConst ``FloatArray
    let inTys ← xs.mapM inferType
    let argTys := (if into then #[batchTy Y] else #[]) ++ inTys.map batchTy
    let names := (if into then #[`out] else #[]) ++ (xs.map fun _ => `xs)
    let rec binds (i : Nat) (acc : Array Expr) (k : Array Expr → MetaM Expr) : MetaM Expr :=
      if h : i < argTys.size then
        withLocalDeclD (names[i]?.getD `b) argTys[i] fun a => binds (i + 1) (acc.push a) k
      else k acc
    binds 0 #[] fun args => do
      let outArg? := if into then some args[0]! else none
      let bs := if into then args.extract 1 args.size else args
      -- `n`: the shortest input
      let lens := (bs.zip inTys).map fun (b, X) => mkApp2 (mkConst ``Grassmann.Batch.len) X b
      let n ← (lens.extract 1 lens.size).foldlM (init := lens[0]!) fun acc l => mkAppM ``Min.min #[acc, l]
      let datas := (bs.zip inTys).map fun (b, X) => mkApp2 (mkConst ``Grassmann.Batch.data) X b
      -- loop-invariant leaves and scalars, evaluated once
      let invIdx := (Array.range st.leaves.size).filter fun l => (leafBinder[l]!).isNone
      let vals := #[n] ++ datas ++ invIdx.map (st.leaves[·]!.expr) ++ st.scalars
      let tys := #[mkConst ``Nat] ++ datas.map (fun _ => floatArr) ++
        invIdx.map (ar.values st.leaves[·]!.size) ++ st.scalars.map fun _ => ctx.α
      let nms := #[`n] ++ (Array.range datas.size).map (fun j => Name.mkSimple s!"d{j}") ++
        invIdx.map (fun l => Name.mkSimple s!"l{l}") ++
        (Array.range st.scalars.size).map fun s => Name.mkSimple s!"s{s}"
      let e ← bindLets nms tys vals fun vars => do
        let nv := vars[0]!
        let dv := vars.extract 1 (1 + datas.size)
        let inv := vars.extract (1 + datas.size) (1 + datas.size + invIdx.size)
        let scalarVar := vars.extract (1 + datas.size + invIdx.size) vars.size
        let m ← mkAppM ``HMul.hMul #[nv, mkRawNatLit kY]
        let base := match outArg? with
          | some o => mkApp2 (mkConst ``Grassmann.Batch.data) Y o
          | none => mkApp (mkConst ``FloatArray.emptyWithCapacity) (mkRawNatLit 0)
        let out0 := mkApp2 (mkConst ``Grassmann.Batch.outputArray) base m
        -- the loop body `fun i out => …`: offsets, reads, the fused nodes, the writes
        let loopBody ← withLocalDeclD `i usize fun i => withLocalDeclD `out floatArr fun out => do
          let offs := (ins.map (·.2) |>.push kY).map fun k => usizeMul i (usizeLit k)
          let inner ← bindLets ((Array.range offs.size).map fun j => Name.mkSimple s!"o{j}")
              (offs.map fun _ => usize) offs fun ovs => do
            let read (l idx : Nat) : Option Expr :=
              match leafBinder[l]? with
              | some (some b) =>
                let off := ovs[b]!
                let pos := if idx == 0 then off else usizeAdd off (usizeLit idx)
                some (mkApp2 (mkConst ``Grassmann.Batch.rd) dv[b]! pos)
              | _ => (invIdx.findIdx? (· == l)).map fun t => ar.get (st.leaves[l]!.size) inv[t]! idx
            bindNodes ar (Heads.of ar) st (st.g.reachable outs) read scalarVar outs fun os => do
              let offY := ovs[ovs.size - 1]!
              let mut acc := out
              for h : j in [0:os.size] do
                let pos := if j == 0 then offY else usizeAdd offY (usizeLit j)
                acc := mkApp3 (mkConst ``Grassmann.Batch.wr) acc pos os[j]
              return acc
          mkLambdaFVars #[i, out] inner
        let res := mkApp4 (mkConst ``Grassmann.Batch.loop) loopBody nv (usizeLit 0) out0
        return mkApp3 (mkConst ``Grassmann.Batch.mk) Y nv res
      mkLambdaFVars args e

/-- `batch% fun (x₁ : X₁) … (xₘ : Xₘ) => e`: the batch kernel `Batch X₁ → … → Batch Xₘ → Batch Y`
of the typed-algebra expression `e` (module doc of `Grassmann.Batch`). -/
syntax (name := batchStx) "batch% " term : term

/-- `batchInto% fun (x₁ : X₁) … => e`: the batch kernel writing into its first argument's
storage, `Batch Y → Batch X₁ → … → Batch Y` (Julia `map!`). -/
syntax (name := batchIntoStx) "batchInto% " term : term

/-- Elaborate `batch%`/`batchInto%`. -/
def elabBatch (into : Bool) (t : Syntax) : Term.TermElabM Expr := do
  let f ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let r ← batchKernel (← instantiateMVars f) into
  check r
  return r

@[term_elab batchStx] def elabBatchStx : Term.TermElab := fun stx _ => match stx with
  | `(batch% $t) => elabBatch false t
  | _ => throwUnsupportedSyntax

@[term_elab batchIntoStx] def elabBatchIntoStx : Term.TermElab := fun stx _ => match stx with
  | `(batchInto% $t) => elabBatch true t
  | _ => throwUnsupportedSyntax

end Grassmann.Fuse
