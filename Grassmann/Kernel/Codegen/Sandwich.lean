/-
Fused sandwich kernels (Julia's generated `product_sandwich`, Grassmann.jl
`src/algebra.jl:1560-1790`, grassmann-products.md §4.6).

The typed sandwiches of `Grassmann.Algebra.Products` evaluate `x ⊘ R` as two
kernel calls, `(~R) ⟑ x` and the projected product with `R` (and `R >>> x` as
three, `R ⟑ x`, `clifford(R)` and the projected product); the expression `R * x * ~R`
is three typed products. Each call allocates its result, and for the small spaces the
allocations dominate (docs/PERF.md). Julia generates one function per shape that keeps the
intermediate in registers. This module does the same:

* `class SandwichKernels V`: the sandwich `x ⊘ R` and `R >>> x` of a graded or
  half `x` by a graded or half `R`, projected onto the layout of `x`, and the unprojected
  `R ⟑ x ⟑ ~R` into the layout the typed products give it (`rsandwich`), generic in the
  coefficient type. The low-priority instance for every space is the computation of the typed
  layer (`sandwichCore`, the `>>>` composition, the three products), so the values are those of
  `Grassmann.Algebra.Products` by construction.
* **High-priority typed instances** of `⊘` (`Sandwich`) and `>>>`
  (`HShiftRight`) for the graded/half shapes, evaluating through
  `SandwichKernels V`.
* **`R * x * ~R` fuses by itself**: with `open Grassmann`, a product `a * b * ~a` whose two
  `a` are the same term elaborates to `RevSandwich.rsandwich a b` when the operand types have an
  instance (a chain or half `R`, a chain or half `x`: one kernel, one allocation), and to the
  three products otherwise. Both compute the same floating-point operations (`rsandwich`'s
  kernel sums in the typed kernels' order), so the rewrite changes no value.
* The emitter (`emitSandwiches`, run by `grassmann_kernels` for spaces without
  tangent generators): per layout pair `(R, x)` a straight-line kernel computing
  the intermediate product `T` as local scalars, then the projected product (and
  for `>>>` the Clifford conjugate of `R`, for `R * x * ~R` its reverse, as signed scalars).
  Every stage sums in the reference order of its plan, so a fused kernel agrees bit for bit
  with the kernel-by-kernel computation (up to the sign of zero). One allocation per
  sandwich (none when an operand of the result's size is exclusive: the result is written
  into it).

Integration note: the natural home of these operations is `Kernels V`
itself (more fields next to `bin`/`binProj`/`un`) with the typed instances
of `Grassmann.Algebra.Products` calling them; until then this module overrides
those instances for the graded/half shapes.
-/
import Grassmann.Algebra.Products
import Grassmann.Kernel.Codegen.Emit

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Kernel.Codegen

/-- The sandwich products of the space `V` on storage layouts (graded or half `R` and `x`),
generic in the coefficient type. -/
class SandwichKernels (V : TensorBundle) where
  /-- `x ⊘ R = (~R) ⟑ x ⟑ involute(R)`, projected onto `x`'s layout (`r` in layout `lr`). -/
  sandwich : {α : Type} → [Coeff α] → (lr lx : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lx.size V.n)
  /-- `R >>> x = R ⟑ x ⟑ clifford(R)`, projected onto `x`'s layout. -/
  tsandwich : {α : Type} → [Coeff α] → (lr lx : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lx.size V.n)
  /-- `R ⟑ x ⟑ ~R` (the typed `R * x * ~R`, unprojected) into layout `lc`, the result layout of
  the typed products (the half of `x`'s parity). -/
  rsandwich : {α : Type} → [Coeff α] → (lr lx lc : Layout) →
      Values α (lr.size V.n) → Values α (lx.size V.n) → Values α (lc.size V.n)

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

/-- `R * x * ~R` by the space's `Kernels`, as the typed products compute it: `R ⟑ x` into the
half of their parities, `~R`, and the product of the two into `lc`. -/
@[inline] def rsandwichThree (lr lx lc : Layout) (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) :
    Values α (lc.size V.n) :=
  let lt := sandwichMid lr lx
  Kernels.bin .mul lt lr lc (Kernels.bin .mul lr lx lt r x) (Kernels.un .reverse lr lr r)

/-- `sandwichTwo`, out of line (the fallback of generated dispatch; specialized on the
space, a closed constant at every call site, so that it is not rebuilt at run time). -/
@[noinline, specialize V] def sandwichOut (V : TensorBundle) [Kernels V] (lr lx : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lx.size V.n) :=
  sandwichTwo lr lx r x

/-- `tsandwichTwo`, out of line. -/
@[noinline, specialize V] def tsandwichOut (V : TensorBundle) [Kernels V] (lr lx : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lx.size V.n) :=
  tsandwichTwo lr lx r x

/-- `rsandwichThree`, out of line. -/
@[noinline, specialize V] def rsandwichOut (V : TensorBundle) [Kernels V] (lr lx lc : Layout)
    (r : Values α (lr.size V.n)) (x : Values α (lx.size V.n)) : Values α (lc.size V.n) :=
  rsandwichThree lr lx lc r x

end Kernel

/-- The kernel-by-kernel sandwiches for every space (low priority: generated instances win). -/
instance (priority := low) SandwichKernels.reference (V : TensorBundle) [Kernels V] : SandwichKernels V where
  sandwich lr lx r x := Kernel.sandwichTwo lr lx r x
  tsandwich lr lx r x := Kernel.tsandwichTwo lr lx r x
  rsandwich lr lx lc r x := Kernel.rsandwichThree lr lx lc r x

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

/-! ## `R * x * ~R` as one kernel -/

/-- The fused `R * x * ~R` (Julia evaluates the same three products; here one kernel): an
instance exists for a chain or half `R` and a chain or half `x`, with the result type of the
three typed products. `a * b * ~a` elaborates to `rsandwich a b` when an instance applies. -/
class RevSandwich (Y X : Type) (Z : outParam Type) where
  /-- `R * x * ~R`. -/
  rsandwich : Y → X → Z

section RevSandwich

variable {V : TensorBundle} {G H : Nat} {p q : Bool} {α : Type} [Coeff α] [SandwichKernels V] {X : Type}

instance [AsChain X V G α] : RevSandwich (Half V q α) X (Half V ((q ^^ (G % 2 == 1)) ^^ q) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (halfLayout q) (.chain G) (halfLayout ((q ^^ (G % 2 == 1)) ^^ q))
    R.v (AsChain.toChain x).v⟩⟩

instance : RevSandwich (Half V q α) (Half V p α) (Half V ((q ^^ p) ^^ q) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (halfLayout q) (halfLayout p) (halfLayout ((q ^^ p) ^^ q)) R.v x.v⟩⟩

instance [AsChain X V G α] :
    RevSandwich (Chain V H α) X (Half V (((H + G) % 2 == 1) ^^ (H % 2 == 1)) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (.chain H) (.chain G)
    (halfLayout (((H + G) % 2 == 1) ^^ (H % 2 == 1))) R.v (AsChain.toChain x).v⟩⟩

instance : RevSandwich (Chain V H α) (Half V p α) (Half V ((p ^^ (H % 2 == 1)) ^^ (H % 2 == 1)) α) :=
  ⟨fun R x => ⟨SandwichKernels.rsandwich (.chain H) (halfLayout p) (halfLayout ((p ^^ (H % 2 == 1)) ^^ (H % 2 == 1)))
    R.v x.v⟩⟩

end RevSandwich

namespace RevSandwichElab

open Lean Elab Term Meta

/-- The operand of a reverse `~t` (Grassmann's or AbstractTensors' prefix `~`). -/
def reverseOperand? (c : Syntax) : Option Syntax :=
  if c.getNumArgs == 2 && c[0].isAtom && c[0].getAtomVal == "~" then some c[1] else none

/-- Elaborate `a * b * ~a`: `RevSandwich.rsandwich a b` when the operand types (elaborated first)
have an instance and the result has the expected type, else the three products (the operands
are elaborated once either way). -/
def elabPattern (a b c : Syntax) (expected? : Option Expr) : TermElabM Expr := do
  let ea ← elabTerm a none
  let eb ← elabTerm b none
  let plain : TermElabM Expr := do
    elabTerm (← `(binop% HMul.hMul (binop% HMul.hMul $(← exprToSyntax ea) $(← exprToSyntax eb)) $(⟨c⟩)))
      expected?
  let ta ← instantiateMVars (← inferType ea)
  let tb ← instantiateMVars (← inferType eb)
  if ta.hasMVar || tb.hasMVar then return ← plain
  let s ← saveState
  try
    let u ← mkFreshLevelMVar
    let Z ← mkFreshExprMVar (mkSort (.succ u))
    let cls := mkApp3 (mkConst ``Grassmann.RevSandwich) ta tb Z
    let some inst ← (synthInstance? cls : MetaM _) | throwError "no RevSandwich instance"
    let Z ← instantiateMVars Z
    let e := mkApp6 (mkConst ``Grassmann.RevSandwich.rsandwich) ta tb Z inst ea eb
    match expected? with
    | some ty =>
      unless ← isDefEq Z ty do throwError "type mismatch"
      return e
    | none => return e
  catch _ =>
    s.restore (restoreInfo := true)
    plain

/-- `rsandwich% R x c`: `R * x * c` for `c = ~R` (the expansion of that pattern, see
`elabPattern`). -/
syntax (name := rsandwichStx) "rsandwich% " term:max term:max term:max : term

/-- Elaborate `rsandwich% R x c` (`elabPattern`). -/
@[term_elab rsandwichStx] def elabRSandwich : TermElab := fun stx expected? =>
  match stx with
  | `(rsandwich% $a $b $c) => elabPattern a b c expected?
  | _ => throwUnsupportedSyntax

end RevSandwichElab

/-- `a * b * ~a` with `open Grassmann`: one `RevSandwich` kernel when the types allow it (a
macro, so that it is tried before the core `*` macro; any other product is left to it). -/
scoped macro_rules
  | `($a * $b * $c) => do
    let some r := RevSandwichElab.reverseOperand? c.raw | Lean.Macro.throwUnsupported
    unless a.raw.structEq r do Lean.Macro.throwUnsupported
    `(rsandwich% $a $b $c)

namespace Kernel.Codegen

open Lean Meta Elab Command

/-- Which sandwich a fused kernel computes. -/
inductive SandwichKind where
  /-- `x ⊘ R` (projected onto `x`). -/
  | sandwich
  /-- `R >>> x` (projected onto `x`). -/
  | tsandwich
  /-- `R * x * ~R` (unprojected, into the half of `x`'s parity). -/
  | rsandwich
  deriving DecidableEq, Repr, Inhabited

/-- The plans of a fused sandwich of `R` (layout `lr`) on `x` (layout `lx`):
the intermediate product (`reverseMul` for `⊘`, `mul` otherwise), the conjugate of `R`
(`clifford` for `>>>`, `reverse` for `R * x * ~R`) and the second product (projected onto `lx`
for `⊘` and `>>>`). -/
structure SandwichPlan where
  /-- Layout of `R`. -/
  lr : Layout
  /-- Layout of `x`. -/
  lx : Layout
  /-- Layout of the intermediate product. -/
  lt : Layout
  /-- Layout of the result (`lx` for `⊘` and `>>>`). -/
  lc : Layout
  /-- Which sandwich. -/
  kind : SandwichKind
  /-- The intermediate product `R ∘ x` into `lt`. -/
  first : Plan
  /-- The conjugate of `R` (`>>>` and `R * x * ~R`). -/
  conj : Option Plan
  /-- The product `T ⟑ R'` into `lc`. -/
  second : Plan
  /-- Negate the result (`x ⊘ R` with an odd `R`: `involute(R) = -R`). -/
  negate : Bool
  deriving Inhabited

/-- `R >>> x` (else `x ⊘ R`; `R * x * ~R` counts as `R >>> x`-like here: `R` on the left). -/
def SandwichPlan.shift (sp : SandwichPlan) : Bool := sp.kind != .sandwich

/-- The versor layouts of the fused `R * x * ~R` of an `n`-generator space (rotors, vectors,
bivectors and pseudovectors, and the odd half); emitted for `n ≤ 5`. -/
def rsandwichVersors (n : Nat) : List Layout :=
  if n > 5 then [] else
  ([Layout.even, .odd, .chain 1, .chain 2, .chain (n - 1)].filter fun l => match l with
    | .chain g => 0 < g && g < n
    | _ => true).eraseDups

/-- The fused sandwiches of `V` (none for tangent spaces, whose `sandwichCore` differs):
every pair of graded or half layouts for `⊘` and `>>>`, and the versor layouts
(`rsandwichVersors`) with every graded or half `x` for `R * x * ~R`. -/
def planSandwiches (V : TensorBundle) : Array SandwichPlan := Id.run do
  if V.diffvars != 0 then return #[]
  let n := V.n
  let tRev := table V (.bin .reverseMul)
  let tMul := table V (.bin .mul)
  let tCl := table V (.un .clifford)
  let tRe := table V (.un .reverse)
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
        let kind := if shift then SandwichKind.tsandwich else .sandwich
        match first, second, conj with
        | .ok f, .ok s, none =>
          if f.nested == 0 && s.nested == 0 then
            out := out.push { lr, lx, lt, lc := lx, kind, first := f, conj := none, second := s, negate := odd }
        | .ok f, .ok s, some (.ok c) =>
          if f.nested == 0 && s.nested == 0 && c.nested == 0 then
            out := out.push { lr, lx, lt, lc := lx, kind, first := f, conj := some c, second := s, negate := false }
        | _, _, _ => pure ()
  for lr in rsandwichVersors n do
    for lx in gradedLayouts n do
      let lt := sandwichMid lr lx
      let lc := sandwichMid lt lr
      let first := buildFrom tMul { V, op := .bin .mul, la := lr, lb := lx, lc := lt }
      let conj := buildFrom tRe { V, op := .un .reverse, la := lr, lb := lr, lc := lr }
      let second := buildFrom tMul { V, op := .bin .mul, la := lt, lb := lr, lc }
      match first, conj, second with
      | .ok f, .ok c, .ok s =>
        if f.nested == 0 && s.nested == 0 && c.nested == 0 then
          out := out.push
            { lr, lx, lt, lc, kind := .rsandwich, first := f, conj := some c, second := s, negate := false }
      | _, _, _ => pure ()
  return out

/-- The type and value of a fused sandwich kernel `(r : Values α nr) (x : Values α nx) : Values α nc`
(written into an operand of the result's size, the exclusive one when both are). -/
def sandwichTerm (nr nx nt nc : Nat) (sp : SandwichPlan) (coefs : Array (Rat × Name) := #[]) :
    MetaM (Expr × Expr) := do
  let base := chooseBase #[some nr, some nx] nc
  withLocalDecl `α .implicit (mkSort Level.one) fun α => do
  withLocalDecl `inst .instImplicit (mkApp (mkConst ``Coeff) α) fun inst => do
    let ar := Arith.new α inst coefs
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
            let outs := (Array.range nc).map fun c =>
              let o := rowSum ar s c fun t => ar.mul tv[s.ia[t]!.toNat]! ss[s.ib[t]!.toNat]!
              if sp.negate then ar.neg o else o
            withLets (names "o" nc) α outs fun os => do
              let b := match base with
                | .arg 0 => r
                | .arg _ => x
                | .pick _ _ => ar.pick nc r x
                | .zeros => ar.zeros nc
              let e ← mkLetFVars (rs ++ xs ++ tv ++ cs ++ os) (ar.packSet b os)
              return (← mkForallFVars args (ar.values nc), ← mkLambdaFVars args e)
          match sp.conj with
          | some c =>
            let cv := (Array.range nr).map fun j => rowSum ar c j fun t => rs[c.ia[t]!.toNat]!
            withLets (names "c" nr) α cv fun cs => finish cs cs
          | none => finish #[] rs

/-- The declaration name of a fused sandwich kernel. -/
def sandwichName (pre : Name) (sp : SandwichPlan) : Name :=
  let tag := match sp.kind with
    | .sandwich => "sandwich" | .tsandwich => "tsandwich" | .rsandwich => "rsandwich"
  pre ++ Name.mkSimple s!"k_{tag}_{layoutTag sp.lr}_{layoutTag sp.lx}"

/-- The plans of a fused sandwich (for collecting its coefficients). -/
def SandwichPlan.plans (sp : SandwichPlan) : Array Plan := #[sp.first, sp.second] ++ sp.conj.toArray

/-- A description of a fused sandwich. -/
def SandwichPlan.describe (sp : SandwichPlan) : String :=
  match sp.kind with
  | .sandwich => "`x ⊘ R`" | .tsandwich => "`R >>> x`" | .rsandwich => "`R * x * ~R`"

/-- Emit the fused sandwich kernels `sps` of `space` under `pre`, their dispatchers and the
`SandwichKernels` instance (`V` denotes the space). Returns the number of kernels. -/
def emitSandwiches (space : TensorBundle) (V : Term) (pre : Name) (sps : Array SandwichPlan)
    (coefs : Array (Rat × Name) := #[]) : CommandElabM Nat := do
  let n := space.n
  if sps.isEmpty then return 0
  let mut names := #[]
  for sp in sps do
    let nm := sandwichName pre sp
    let (type, value) ← liftTermElabM <|
      sandwichTerm (sp.lr.size n) (sp.lx.size n) (sp.lt.size n) (sp.lc.size n) sp coefs
    liftCoreM <| addDecl <| .defnDecl {
      name := nm, levelParams := [], type, value
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
    modifyEnv fun env => (Compiler.specializeAttr.setParam env nm #[]).toOption.getD env
    addDocStringCore nm s!"Generated fused sandwich (DESIGN.md §5.2): {sp.describe} for `R` a \
      {layoutDoc sp.lr} and `x` a {layoutDoc sp.lx} in `{space}` ({sp.first.size} + {sp.second.size} entries)."
    names := names.push nm
  compileKernels names
  let nLit : Term := quote n
  let (lr, lx, lc, r, x) := (mkIdent `lr, mkIdent `lx, mkIdent `lc, mkIdent `r, mkIdent `x)
  for kind in [SandwichKind.sandwich, .tsandwich] do
    let fb := mkCIdent (if kind == .tsandwich then ``Grassmann.Kernel.tsandwichOut else ``Grassmann.Kernel.sandwichOut)
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for sp in sps.filter (·.kind == kind) do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $(← layoutStx sp.lr), $(← layoutStx sp.lx), $r, $x => $(mkCIdent (sandwichName pre sp)) $r $x))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $lr, $lx, $r, $x => $fb $V $lr $lx $r $x))
    let nm := pre ++ Name.mkSimple (if kind == .tsandwich then "tsandwich" else "sandwich")
    elabCommand (← `(command|
      @[inline] def $(mkIdent (`_root_ ++ nm)) {α : Type} [AbstractTensors.Coeff α] ($lr $lx : DirectSum.Layout)
          ($r : StaticVectors.Values α (DirectSum.Layout.size $nLit $lr))
          ($x : StaticVectors.Values α (DirectSum.Layout.size $nLit $lx)) :
          StaticVectors.Values α (DirectSum.Layout.size $nLit $lx) :=
        match $lr:ident, $lx:ident, $r:ident, $x:ident with $alts:matchAlt*))
    addDocStringCore nm s!"Generated dispatch of the fused {if kind == .tsandwich then "`>>>`" else "`⊘`"} of `{space}`."
  -- `R * x * ~R`
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for sp in sps.filter (·.kind == .rsandwich) do
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(← layoutStx sp.lr), $(← layoutStx sp.lx), $(← layoutStx sp.lc), $r, $x =>
        $(mkCIdent (sandwichName pre sp)) $r $x))
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
    | $lr, $lx, $lc, $r, $x => Grassmann.Kernel.rsandwichOut $V $lr $lx $lc $r $x))
  let rnm := pre ++ `rsandwich
  elabCommand (← `(command|
    @[inline] def $(mkIdent (`_root_ ++ rnm)) {α : Type} [AbstractTensors.Coeff α] ($lr $lx $lc : DirectSum.Layout)
        ($r : StaticVectors.Values α (DirectSum.Layout.size $nLit $lr))
        ($x : StaticVectors.Values α (DirectSum.Layout.size $nLit $lx)) :
        StaticVectors.Values α (DirectSum.Layout.size $nLit $lc) :=
      match $lr:ident, $lx:ident, $lc:ident, $r:ident, $x:ident with $alts:matchAlt*))
  addDocStringCore rnm s!"Generated dispatch of the fused `R * x * ~R` of `{space}`."
  let instId := mkIdent (`_root_ ++ pre ++ `instSandwichKernels)
  elabCommand (← `(command|
    /-- The generated fused sandwich kernels of this space. -/
    instance $instId:ident : Grassmann.SandwichKernels $V where
      sandwich := fun $lr $lx $r $x => $(mkCIdent (pre ++ `sandwich)) $lr $lx $r $x
      tsandwich := fun $lr $lx $r $x => $(mkCIdent (pre ++ `tsandwich)) $lr $lx $r $x
      rsandwich := fun $lr $lx $lc $r $x => $(mkCIdent rnm) $lr $lx $lc $r $x))
  return sps.size

end Kernel.Codegen

end Grassmann
