/-
Emission of a reflected scalar graph as straight-line code (`Grassmann.Fuse`).

```lean
let l₀ : Values α n₀ := <leaf 0>; …            -- run-time vectors, each evaluated once
let s₀ : α := <opaque scalar 0>; …              -- run-time scalars
let t₃ := l₀.get ⟨i, _⟩; …                      -- the coefficients read (unchecked reads)
let t₇ := t₃ * t₅; let t₈ := t₇ - t₄ * t₆; …   -- one `let` per graph node, in topological order
Chain.mk ((base.set ⟨0, _⟩ o₀).set ⟨1, _⟩ o₁ …) -- the result: written into one buffer
```

`base` is a leaf of the output's length when there is one (the writes are then in place when
that leaf is exclusive; otherwise the first write copies it once), else the zero vector: one
allocation for the whole expression. A scalar-valued expression allocates nothing. The
arithmetic is the coefficient type's `Coeff` arithmetic (`Grassmann.Kernel.Codegen.Arith`), as
in the generated kernels; exact constants other than `0`, `1` go through `Fuse.coef`, a
`@[noinline]` function whose applications to literals are closed terms, evaluated once.
-/
import Grassmann.Fuse.Reflect

namespace Grassmann.Fuse

open Lean Meta
open DirectSum StaticVectors AbstractTensors Grassmann.Kernel Grassmann.Kernel.Codegen

/-- The exact constant `num / den` of the coefficient type (`@[noinline]`: applied to literals it
is a closed term of each specialized caller, computed once). -/
@[noinline, specialize] def coef {α : Type} [Coeff α] (num : Int) (den : Nat) : α := Coeff.ofRat (mkRat num den)

/-- The term of the exact constant `q`. -/
def constExpr (ar : Arith) (q : Rat) : Expr :=
  if q == 0 then ar.zero
  else if q == 1 then mkApp2 (mkConst ``AbstractTensors.Coeff.one) ar.α ar.inst
  else
    let num : Expr := if q.num < 0 then mkApp (mkConst ``Int.negSucc) (mkRawNatLit (q.num.natAbs - 1))
      else mkApp (mkConst ``Int.ofNat) (mkRawNatLit q.num.natAbs)
    mkApp4 (mkConst ``Grassmann.Fuse.coef) ar.α ar.inst num (mkRawNatLit q.den)

/-- The arithmetic heads `HAdd.hAdd α α α inst` etc., built once and shared by every node (the
emitted terms, and the `.olean`s that store them, are about half as large as with a fresh head
per node). -/
structure Heads where
  /-- `(· + ·)`. -/
  add : Expr
  /-- `(· - ·)`. -/
  sub : Expr
  /-- `(· * ·)`. -/
  mul : Expr
  /-- `(- ·)`. -/
  neg : Expr

/-- The shared heads of `ar`. -/
def Heads.of (ar : Arith) : Heads where
  add := mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) ar.α ar.α ar.α ar.addI
  sub := mkApp4 (mkConst ``HSub.hSub [0, 0, 0]) ar.α ar.α ar.α ar.subI
  mul := mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) ar.α ar.α ar.α ar.mulI
  neg := mkApp2 (mkConst ``Neg.neg [0]) ar.α ar.negI

/-- `let`-bind `vals[i] : tys[i]` in turn (as `names[i]`) and pass the variables to `k`; the
result is the `let` chain around `k`'s term. -/
partial def bindLets (names : Array Name) (tys vals : Array Expr) (k : Array Expr → MetaM Expr)
    (i : Nat := 0) (acc : Array Expr := #[]) : MetaM Expr :=
  if h : i < vals.size then
    withLetDecl (names[i]?.getD `v) (tys[i]?.getD (mkSort 0)) vals[i] fun x => do
      mkLetFVars #[x] (← bindLets names tys vals k (i + 1) (acc.push x))
  else k acc

/-- The term of every live node of `g` (in topological order), given the terms of the leaves
and scalars, as a `let` chain around `k (terms of outs)`. -/
partial def bindNodes (ar : Arith) (hd : Heads) (st : State) (live : Array Nat)
    (leafVar : Array (Option Expr)) (scalarVar : Array Expr) (outs : Array Nat) (k : Array Expr → MetaM Expr)
    (j : Nat := 0) (env : Std.HashMap Nat Expr := {}) : MetaM Expr := do
  let g := st.g
  let val (i : Nat) : Expr := env.getD i ar.zero
  if h : j < live.size then
    let i := live[j]
    let term? : Option Expr := match g.get i with
      | .input l idx => (leafVar[l]?.getD none).map fun lv => ar.get (st.leaves[l]!.size) lv idx
      | .scalar s => scalarVar[s]?
      | .const q => some (constExpr ar q)
      | .add a b => some (mkApp2 hd.add (val a) (val b))
      | .sub a b => some (mkApp2 hd.sub (val a) (val b))
      | .mul a b => some (mkApp2 hd.mul (val a) (val b))
      | .neg a => some (mkApp hd.neg (val a))
      | .ext f args => some (mkAppN st.fns[f]! (args.map val)).headBeta
    match term?, g.get i with
    | none, _ => bindNodes ar hd st live leafVar scalarVar outs k (j + 1) env
    | some t, .const _ => bindNodes ar hd st live leafVar scalarVar outs k (j + 1) (env.insert i t)
    | some t, .scalar _ => bindNodes ar hd st live leafVar scalarVar outs k (j + 1) (env.insert i t)
    | some t, _ =>
      withLetDecl (.mkSimple s!"t{i}") ar.α t fun x => do
        mkLetFVars #[x] (← bindNodes ar hd st live leafVar scalarVar outs k (j + 1) (env.insert i x))
  else k (outs.map val)

/-- Build the straight-line code computing the nodes `outs` of state `st` and hand the output
terms (and the leaf variables, by leaf index) to `k`, inside the `let`s. -/
def emitWith (ctx : Ctx) (st : State) (outs : Array Nat)
    (k : Arith → Array Expr → Array (Option Expr) → MetaM Expr) : MetaM Expr := do
  let ar := Arith.new ctx.α ctx.instC
  let g := st.g
  let live := g.reachable outs
  let mut usedLeaf := Array.replicate st.leaves.size false
  let mut usedScalar := Array.replicate st.scalars.size false
  for i in live do
    match g.get i with
    | .input l _ => usedLeaf := usedLeaf.set! l true
    | .scalar s => usedScalar := usedScalar.set! s true
    | _ => pure ()
  let lIdx := (Array.range st.leaves.size).filter (usedLeaf[·]!)
  let sIdx := (Array.range st.scalars.size).filter (usedScalar[·]!)
  let names := lIdx.map (fun l => Name.mkSimple s!"l{l}") ++ sIdx.map (fun s => Name.mkSimple s!"s{s}")
  let tys := lIdx.map (fun l => ar.values st.leaves[l]!.size) ++ sIdx.map fun _ => ctx.α
  let vals := lIdx.map (fun l => st.leaves[l]!.expr) ++ sIdx.map (st.scalars[·]!)
  bindLets names tys vals fun vars => do
    let mut leafVar : Array (Option Expr) := Array.replicate st.leaves.size none
    for h : t in [0:lIdx.size] do leafVar := leafVar.set! lIdx[t] (some vars[t]!)
    let mut scalarVar : Array Expr := Array.replicate st.scalars.size ar.zero
    for h : t in [0:sIdx.size] do scalarVar := scalarVar.set! sIdx[t] vars[lIdx.size + t]!
    bindNodes ar (Heads.of ar) st live leafVar scalarVar outs (k ar · leafVar)

end Grassmann.Fuse
