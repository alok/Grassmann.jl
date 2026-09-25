/-
Fused sandwich kernels (Julia's generated `product_sandwich`, Grassmann.jl
`src/algebra.jl:1560-1790`, grassmann-products.md §4.6).

The typed sandwiches of `Grassmann.Algebra.Products` evaluate `x ⊘ R` as two
kernel calls, `(~R) ⟑ x` and the projected product with `R` (and `R >>> x` as
three, `R ⟑ x`, `clifford(R)` and the projected product). Each call allocates
its result, and for the small spaces the allocations dominate (docs/PERF.md).
Julia generates one function per shape that keeps the intermediate in
registers. This module does the same:

* `class SandwichKernels V`: the sandwich `x ⊘ R` and `R >>> x` of a graded or
  half `x` by a graded or half `R`, projected onto the layout of `x`, generic in
  the coefficient type. The low-priority instance for every space is the
  two-kernel computation of the typed layer (`sandwichCore` and the `>>>`
  composition), so the values are those of `Grassmann.Algebra.Products` by
  construction.
* **High-priority typed instances** of `⊘` (`Sandwich`) and `>>>`
  (`HShiftRight`) for the graded/half shapes, evaluating through
  `SandwichKernels V`.
* The emitter (`emitSandwiches`, run by `grassmann_kernels` for spaces without
  tangent generators): per layout pair `(R, x)` a straight-line kernel computing
  the intermediate product `T` as local scalars, then the projected product (and
  for `>>>` the Clifford conjugate of `R` as signed scalars). Both stages sum in
  the reference order of their plans, so a fused kernel agrees bit for bit with
  the two-kernel computation (up to the sign of zero). One allocation per
  sandwich (none when `x` is exclusive: the result is written into it).

Integration note: the natural home of these two operations is `Kernels V`
itself (two more fields next to `bin`/`binProj`/`un`) with the typed instances
of `Grassmann.Algebra.Products` calling them; until then this module overrides
those instances for the graded/half shapes.
-/
import Grassmann.Algebra.Products
import Grassmann.Kernel.Codegen.Emit

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Kernel.Codegen

/-- The sandwich products of the space `V` on storage layouts (graded or half `R` and `x`),
projected onto the layout of `x`, generic in the coefficient type. -/
class SandwichKernels (V : TensorBundle) where
  /-- `x ⊘ R = (~R) ⟑ x ⟑ involute(R)`, projected onto `x`'s layout (`r` in layout `lr`). -/
  sandwich : {α : Type} → [Coeff α] → (lr lx : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lx.size V.n)
  /-- `R >>> x = R ⟑ x ⟑ clifford(R)`, projected onto `x`'s layout. -/
  tsandwich : {α : Type} → [Coeff α] → (lr lx : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lx.size V.n)

namespace Kernel

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V]

/-- The layout of the intermediate product of a sandwich: the half of parity
`parity(R) ⊕ parity(x)` (the full layout when either is not graded). -/
@[inline] def sandwichMid (lr lx : Layout) : Layout :=
  match parityOf lr, parityOf lx with
  | some p, some q => halfL (p ^^ q)
  | _, _ => .full

/-- `x ⊘ R` by the space's `Kernels`, exactly as the typed instances of
`Grassmann.Algebra.Products` compute it (`sandwichCore`). -/
@[inline] def sandwichTwo (lr lx : Layout) (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) :
    Values α (lx.size V.n) :=
  sandwichCore lr lx (sandwichMid lr lx) lx (parityOf lr) r x

/-- `R >>> x` by the space's `Kernels`, as the typed instances compute it. -/
@[inline] def tsandwichTwo (lr lx : Layout) (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) :
    Values α (lx.size V.n) :=
  let lt := sandwichMid lr lx
  Kernels.binProj .mul lt lr lx (Kernels.bin .mul lr lx lt r x) (Kernels.un .clifford lr lr r)

/-- `sandwichTwo`, out of line (the fallback of generated dispatch; specialized on the
space, a closed constant at every call site, so that it is not rebuilt at run time). -/
@[noinline, specialize V] def sandwichOut (V : TensorBundle) [Kernels V] (lr lx : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lx.size V.n) :=
  sandwichTwo lr lx r x

/-- `tsandwichTwo`, out of line. -/
@[noinline, specialize V] def tsandwichOut (V : TensorBundle) [Kernels V] (lr lx : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lx.size V.n) :=
  tsandwichTwo lr lx r x

end Kernel

/-- The two-kernel sandwiches for every space (low priority: generated instances win). -/
instance (priority := low) SandwichKernels.reference (V : TensorBundle) [Kernels V] : SandwichKernels V where
  sandwich lr lx r x := Kernel.sandwichTwo lr lx r x
  tsandwich lr lx r x := Kernel.tsandwichTwo lr lx r x

/-! ## Typed sandwiches through `SandwichKernels`

The graded/half shapes of `Grassmann.Algebra.Products` (same types, same values). -/

section Typed

variable {V : TensorBundle} {G H : Nat} {p q : Bool} {α : Type} [Coeff α] [SandwichKernels V] {X Y : Type}

instance (priority := high) [AsChain X V G α] [AsChain Y V H α] : Sandwich X Y (Chain V G α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (.chain H) (.chain G) (AsChain.toChain R).v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain X V G α] : Sandwich X (Half V q α) (Chain V G α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (halfLayout q) (.chain G) R.v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain Y V H α] : Sandwich (Half V p α) Y (Half V p α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (.chain H) (halfLayout p) (AsChain.toChain R).v x.v⟩⟩

instance (priority := high) : Sandwich (Half V p α) (Half V q α) (Half V p α) :=
  ⟨fun x R => ⟨SandwichKernels.sandwich (halfLayout q) (halfLayout p) R.v x.v⟩⟩

instance (priority := high) [AsChain X V G α] [AsChain Y V H α] : HShiftRight Y X (Chain V G α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (.chain H) (.chain G) (AsChain.toChain R).v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain X V G α] : HShiftRight (Half V q α) X (Chain V G α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (halfLayout q) (.chain G) R.v (AsChain.toChain x).v⟩⟩

instance (priority := high) [AsChain Y V H α] : HShiftRight Y (Half V p α) (Half V p α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (.chain H) (halfLayout p) (AsChain.toChain R).v x.v⟩⟩

instance (priority := high) : HShiftRight (Half V q α) (Half V p α) (Half V p α) :=
  ⟨fun R x => ⟨SandwichKernels.tsandwich (halfLayout q) (halfLayout p) R.v x.v⟩⟩

end Typed

namespace Kernel.Codegen

open Lean Meta Elab Command

/-- The plans of a fused sandwich of `R` (layout `lr`) on `x` (layout `lx`):
the intermediate product (`reverseMul` for `⊘`, `mul` for `>>>`), the Clifford
conjugate of `R` (`>>>` only) and the projected product. -/
structure SandwichPlan where
  /-- Layout of `R`. -/
  lr : Layout
  /-- Layout of `x` (and of the result). -/
  lx : Layout
  /-- Layout of the intermediate product. -/
  lt : Layout
  /-- `R >>> x` (else `x ⊘ R`). -/
  shift : Bool
  /-- The intermediate product `R ∘ x` into `lt`. -/
  first : Plan
  /-- `clifford` on `lr` (`R >>> x` only). -/
  conj : Option Plan
  /-- The product `T ⟑ R'` projected onto `lx`. -/
  second : Plan
  /-- Negate the result (`x ⊘ R` with an odd `R`: `involute(R) = -R`). -/
  negate : Bool
  deriving Inhabited

/-- The fused sandwiches of `V` (none for tangent spaces, whose `sandwichCore` differs):
every pair of graded or half layouts, both operations. -/
def planSandwiches (V : TensorBundle) : Array SandwichPlan := Id.run do
  if V.diffvars != 0 then return #[]
  let n := V.n
  let tRev := table V (.bin .reverseMul)
  let tMul := table V (.bin .mul)
  let tCl := table V (.un .clifford)
  let mut out := #[]
  for lr in gradedLayouts n do
    for lx in gradedLayouts n do
      let lt := sandwichMid lr lx
      let second := buildFrom tMul { V, op := .bin .mul, la := lt, lb := lr, lc := lx, project := true }
      let odd := (parityOf lr).getD false
      for shift in [false, true] do
        let first := buildFrom (if shift then tMul else tRev)
          { V, op := .bin (if shift then .mul else .reverseMul), la := lr, lb := lx, lc := lt }
        let conj := if shift then some (buildFrom tCl { V, op := .un .clifford, la := lr, lb := lr, lc := lr })
          else none
        match first, second, conj with
        | .ok f, .ok s, none =>
          if f.nested == 0 && s.nested == 0 then
            out := out.push { lr, lx, lt, shift, first := f, conj := none, second := s, negate := odd }
        | .ok f, .ok s, some (.ok c) =>
          if f.nested == 0 && s.nested == 0 && c.nested == 0 then
            out := out.push { lr, lx, lt, shift, first := f, conj := some c, second := s, negate := false }
        | _, _, _ => pure ()
  return out

/-- The type and value of a fused sandwich kernel `(r : Values α nr) (x : Values α nx) : Values α nx`. -/
def sandwichTerm (nr nx nt : Nat) (sp : SandwichPlan) : MetaM (Expr × Expr) := do
  withLocalDecl `α .implicit (mkSort Level.one) fun α => do
  withLocalDecl `inst .instImplicit (mkApp (mkConst ``Coeff) α) fun inst => do
    let ar := Arith.new α inst
    withLocalDeclD `r (ar.values nr) fun r => do
    withLocalDeclD `x (ar.values nx) fun x => do
      let args := #[α, inst, r, x]
      let names (s : String) (k : Nat) := (Array.range k).map fun i => Name.mkSimple s!"{s}{i}"
      withLets (names "r" nr) α ((Array.range nr).map (ar.get nr r ·)) fun rs => do
      withLets (names "x" nx) α ((Array.range nx).map (ar.get nx x ·)) fun xs => do
        let f := sp.first
        let ts := (Array.range nt).map fun k =>
          rowSum ar f k fun t => ar.mul rs[f.ia[t]!.toNat]! xs[f.ib[t]!.toNat]!
        withLets (names "t" nt) α ts fun tv => do
          let finish (cs : Array Expr) (ss : Array Expr) : MetaM (Expr × Expr) := do
            let s := sp.second
            let outs := (Array.range nx).map fun c =>
              let o := rowSum ar s c fun t => ar.mul tv[s.ia[t]!.toNat]! ss[s.ib[t]!.toNat]!
              if sp.negate then ar.neg o else o
            withLets (names "o" nx) α outs fun os => do
              let e ← mkLetFVars (rs ++ xs ++ tv ++ cs ++ os) (ar.packSet x os)
              return (← mkForallFVars args (ar.values nx), ← mkLambdaFVars args e)
          match sp.conj with
          | some c =>
            let cv := (Array.range nr).map fun j => rowSum ar c j fun t => rs[c.ia[t]!.toNat]!
            withLets (names "c" nr) α cv fun cs => finish cs cs
          | none => finish #[] rs

/-- The declaration name of a fused sandwich kernel. -/
def sandwichName (pre : Name) (sp : SandwichPlan) : Name :=
  pre ++ Name.mkSimple s!"k_{if sp.shift then "tsandwich" else "sandwich"}_{layoutTag sp.lr}_{layoutTag sp.lx}"

/-- Emit the fused sandwich kernels of `space` under `pre`, their dispatchers and the
`SandwichKernels` instance (`V` denotes the space). Returns the number of kernels. -/
def emitSandwiches (space : TensorBundle) (V : Term) (pre : Name) : CommandElabM Nat := do
  let n := space.n
  let sps := planSandwiches space
  if sps.isEmpty then return 0
  let mut names := #[]
  for sp in sps do
    let nm := sandwichName pre sp
    let (type, value) ← liftTermElabM <| sandwichTerm (sp.lr.size n) (sp.lx.size n) (sp.lt.size n) sp
    liftCoreM <| addDecl <| .defnDecl {
      name := nm, levelParams := [], type, value
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
    modifyEnv fun env => (Compiler.specializeAttr.setParam env nm #[]).toOption.getD env
    addDocStringCore nm s!"Generated fused sandwich (DESIGN.md §5.2): \
      {if sp.shift then "`R >>> x`" else "`x ⊘ R`"} for `R` a {layoutDoc sp.lr} and `x` a {layoutDoc sp.lx} \
      in `{space}` ({sp.first.size} + {sp.second.size} entries)."
    names := names.push nm
  for i in [0:(names.size + 31) / 32] do
    liftCoreM <| withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) <|
      compileDecls (names.extract (i * 32) ((i + 1) * 32))
  let nLit : Term := quote n
  let (lr, lx, r, x) := (mkIdent `lr, mkIdent `lx, mkIdent `r, mkIdent `x)
  for shift in [false, true] do
    let fb := mkCIdent (if shift then ``Grassmann.Kernel.tsandwichOut else ``Grassmann.Kernel.sandwichOut)
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for sp in sps.filter (·.shift == shift) do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $(← layoutStx sp.lr), $(← layoutStx sp.lx), $r, $x => $(mkCIdent (sandwichName pre sp)) $r $x))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $lr, $lx, $r, $x => $fb $V $lr $lx $r $x))
    let nm := pre ++ Name.mkSimple (if shift then "tsandwich" else "sandwich")
    elabCommand (← `(command|
      @[inline] def $(mkIdent (`_root_ ++ nm)) {α : Type} [AbstractTensors.Coeff α] ($lr $lx : DirectSum.Layout)
          ($r : StaticVectors.Values α (DirectSum.Layout.size $nLit $lr))
          ($x : StaticVectors.Values α (DirectSum.Layout.size $nLit $lx)) :
          StaticVectors.Values α (DirectSum.Layout.size $nLit $lx) :=
        match $lr:ident, $lx:ident, $r:ident, $x:ident with $alts:matchAlt*))
    addDocStringCore nm s!"Generated dispatch of the fused {if shift then "`>>>`" else "`⊘`"} of `{space}`."
  let instId := mkIdent (`_root_ ++ pre ++ `instSandwichKernels)
  elabCommand (← `(command|
    /-- The generated fused sandwich kernels of this space. -/
    instance $instId:ident : Grassmann.SandwichKernels $V where
      sandwich := fun $lr $lx $r $x => $(mkCIdent (pre ++ `sandwich)) $lr $lx $r $x
      tsandwich := fun $lr $lx $r $x => $(mkCIdent (pre ++ `tsandwich)) $lr $lx $r $x))
  return sps.size

end Kernel.Codegen

end Grassmann
