/-
The `clifford` tactic: identities between multivector expressions in a
concrete space, by blade extensionality.

`clifford` proves `x = y` for `x y : Cl g` when `g : Fin n → R` has a numeral
dimension `n` (any commutative ring `R`, any metric: integer entries are
folded as constants, other entries stay symbolic). It

1. reifies both sides (and every hypothesis `h : a = b` between multivectors
   of the same space) into `Grassmann.Tactic.MExpr`, with scalar atoms
   (variables, unknown ring terms) and opaque multivectors (whose `2ⁿ`
   coordinates become atoms);
2. evaluates the `2ⁿ` coordinate polynomials of each side natively
   (`MExpr.eval`, the spec's blade tables with zero pruning), and states them
   as ring equations; the kernel re-checks this step by evaluation
   (`Grassmann.Tactic.eq_of_coords`, `coords_of_eq`);
3. closes every non-trivial coordinate equation with `grind` (the Gröbner
   ring solver; hypotheses such as `c^2 + s^2 = 1` and the coordinates of
   multivector hypotheses are used).

Variants: `clifford [p₁, …]` passes extra parameters to `grind`;
`clifford_nf` stops after step 2 and leaves the coordinate equations as goals.
docs/TACTICS.md has the full description and examples.
-/
import Lean
import Grassmann.Tactic.Coord

namespace Grassmann.Tactic

open Lean Meta Elab Tactic Grassmann.Spec

/-! ## Quoting reflected data -/

/-- The `Expr` of a `Poly` value. -/
partial def Poly.quote : Poly → Expr
  | .int k => mkApp (mkConst ``Poly.int) (toExpr k)
  | .atom i => mkApp (mkConst ``Poly.atom) (mkNatLit i)
  | .coeff v k => mkApp2 (mkConst ``Poly.coeff) (mkNatLit v) (mkNatLit k)
  | .met i => mkApp (mkConst ``Poly.met) (mkNatLit i)
  | .add p q => mkApp2 (mkConst ``Poly.add) p.quote q.quote
  | .mul p q => mkApp2 (mkConst ``Poly.mul) p.quote q.quote
  | .neg p => mkApp (mkConst ``Poly.neg) p.quote
  | .sub p q => mkApp2 (mkConst ``Poly.sub) p.quote q.quote
  | .pow p k => mkApp2 (mkConst ``Poly.pow) p.quote (mkNatLit k)

/-- The `Expr` of an `MExpr` value. -/
partial def MExpr.quote : MExpr → Expr
  | .var i => mkApp (mkConst ``MExpr.var) (mkNatLit i)
  | .blade a => mkApp (mkConst ``MExpr.blade) (mkNatLit a)
  | .scalar p => mkApp (mkConst ``MExpr.scalar) p.quote
  | .zero => mkConst ``MExpr.zero
  | .one => mkConst ``MExpr.one
  | .add x y => mkApp2 (mkConst ``MExpr.add) x.quote y.quote
  | .sub x y => mkApp2 (mkConst ``MExpr.sub) x.quote y.quote
  | .neg x => mkApp (mkConst ``MExpr.neg) x.quote
  | .smul p x => mkApp2 (mkConst ``MExpr.smul) p.quote x.quote
  | .mul x y => mkApp2 (mkConst ``MExpr.mul) x.quote y.quote
  | .wedge x y => mkApp2 (mkConst ``MExpr.wedge) x.quote y.quote
  | .contract x y => mkApp2 (mkConst ``MExpr.contract) x.quote y.quote
  | .vee x y => mkApp2 (mkConst ``MExpr.vee) x.quote y.quote
  | .reverse x => mkApp (mkConst ``MExpr.reverse) x.quote
  | .involute x => mkApp (mkConst ``MExpr.involute) x.quote
  | .clifford x => mkApp (mkConst ``MExpr.clifford) x.quote
  | .proj k x => mkApp2 (mkConst ``MExpr.proj) (mkNatLit k) x.quote
  | .compl x => mkApp (mkConst ``MExpr.compl) x.quote
  | .complInv x => mkApp (mkConst ``MExpr.complInv) x.quote
  | .hodge x => mkApp (mkConst ``MExpr.hodge) x.quote

/-- A list literal. -/
def mkListLit (u : Level) (α : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [u]) α x acc) (mkApp (mkConst ``List.nil [u]) α)

/-! ## Reification -/

/-- The space of the goal: `Cl g` with `g : Fin n → R`. -/
structure Space where
  /-- The universe of `R`. -/
  u : Level
  /-- The coefficient ring. -/
  R : Expr
  /-- Its `Lean.Grind.CommRing` instance. -/
  inst : Expr
  /-- The dimension, as it appears in the goal. -/
  n : Expr
  /-- The dimension's value. -/
  nVal : Nat
  /-- The metric. -/
  g : Expr
  /-- `Cl g`. -/
  clTy : Expr

/-- Atoms met while reifying. -/
structure RState where
  /-- Scalar atoms (`Poly.atom i`). -/
  atoms : Array Expr := #[]
  /-- Opaque multivectors (`MExpr.var i`). -/
  vars : Array Expr := #[]

/-- The reification monad. -/
abbrev ReifyM := ReaderT Space (StateRefT RState MetaM)

/-- Index of an expression in an atom array, up to reducible defeq; adds it if new. -/
def atomIndex (xs : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  for h : i in [0:xs.size] do
    if ← withReducible (isDefEq xs[i] e) then return some i
  return none

/-- A scalar atom. -/
def addAtom (e : Expr) : ReifyM Nat := do
  let s ← get
  if let some i ← atomIndex s.atoms e then return i
  modify fun s => { s with atoms := s.atoms.push e }
  return s.atoms.size

/-- An opaque multivector. -/
def addVar (e : Expr) : ReifyM Nat := do
  let s ← get
  if let some i ← atomIndex s.vars e then return i
  modify fun s => { s with vars := s.vars.push e }
  return s.vars.size

/-- The natural number a closed expression evaluates to. -/
def evalNatExpr? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some k := e.rawNatLit? then return some k
  if let some k := e.nat? then return some k
  if let some k ← Meta.evalNat e |>.run then return some k
  let e' ← whnfD e
  if let some k := e'.rawNatLit? then return some k
  return e'.nat?

/-- The mask of a closed `BitVec n` expression. -/
def evalBitVec? (e : Expr) : MetaM (Option Nat) := do
  if let some ⟨_, v⟩ ← getBitVecValue? e then return some v.toNat
  evalNatExpr? (mkApp2 (mkConst ``BitVec.toNat) (← inferBitVecWidth e) e)
where
  inferBitVecWidth (e : Expr) : MetaM Expr := do
    let ty ← whnfR (← inferType e)
    match_expr ty with
    | BitVec w => return w
    | _ => throwError "clifford: expected a `BitVec`, got{indentExpr e}"

/-- The value of a closed `Fin n` expression. -/
def evalFin? (e : Expr) : MetaM (Option Nat) := do
  if let some ⟨_, v⟩ ← getFinValue? e then return some v.val
  let ty ← whnfR (← inferType e)
  match_expr ty with
  | Fin m => evalNatExpr? (mkApp2 (mkConst ``Fin.val) m e)
  | _ => return none

/-- An integer numeral `OfNat.ofNat k` or `-OfNat.ofNat k` (`k > 0`). -/
def intNumeral? (e : Expr) : Option Int :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, k, _]) => k.rawNatLit?.map Int.ofNat
  | (``Neg.neg, #[_, _, a]) =>
    match a.getAppFnArgs with
    | (``OfNat.ofNat, #[_, k, _]) =>
      match k.rawNatLit? with
      | some (m + 1) => some (-((m + 1 : Nat) : Int))
      | _ => none
    | _ => none
  | _ => none

/-- Reify a scalar expression. Only constructions that denote the same term up
to definitional unfolding are used (`a - b` is `Poly.sub`, not `a + -b`). -/
partial def reifyPoly (e : Expr) : ReifyM Poly := do
  if let some k := intNumeral? e then return .int k
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reifyPoly a) (← reifyPoly b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← reifyPoly a) (← reifyPoly b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← reifyPoly a) (← reifyPoly b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← reifyPoly a)
  | (``HPow.hPow, #[_, natTy, _, _, a, k]) =>
    if natTy.isConstOf ``Nat then
      if let some k ← evalNatExpr? k then return .pow (← reifyPoly a) k
    return .atom (← addAtom e)
  | _ => return .atom (← addAtom e)

/-- Reify a multivector expression. Unknown constants are unfolded (up to
`fuel` times); anything else is an opaque multivector. -/
partial def reifyMV (e : Expr) (fuel : Nat := 16) : ReifyM MExpr := do
  let sp ← read
  let args := e.getAppArgs
  let last := args.back!
  let last2 := args[args.size - 2]!
  let asVar : ReifyM MExpr := do
    if fuel > 0 then
      if let .const c _ := e.getAppFn then
        unless c == ``Cl.mk do
          if let some e' ← unfoldDefinition? e then
            return ← reifyMV e'.headBeta (fuel - 1)
    return .var (← addVar e)
  match e.getAppFn with
  | .const c _ =>
    match c, args.size with
    | ``HAdd.hAdd, 6 => return .add (← reifyMV last2 fuel) (← reifyMV last fuel)
    | ``HSub.hSub, 6 => return .sub (← reifyMV last2 fuel) (← reifyMV last fuel)
    | ``HMul.hMul, 6 => return .mul (← reifyMV last2 fuel) (← reifyMV last fuel)
    | ``Neg.neg, 3 => return .neg (← reifyMV last fuel)
    | ``HSMul.hSMul, 6 => return .smul (← reifyPoly last2) (← reifyMV last fuel)
    | ``OfNat.ofNat, 3 =>
      match args[1]!.rawNatLit? with
      | some 0 => return .zero
      | some 1 => return .one
      | _ => asVar
    | ``Zero.zero, 2 => return .zero
    | ``One.one, 2 => return .one
    | ``Cl.blade, 5 =>
      match ← evalBitVec? last with
      | some a => return .blade a
      | none => asVar
    | ``Cl.gen, 5 =>
      match ← evalFin? last with
      | some i => return .blade (2 ^ i)
      | none => asVar
    | ``Cl.scalar, 5 => return .scalar (← reifyPoly last)
    | ``Cl.pseudoscalar, 4 => return .blade (2 ^ sp.nVal - 1)
    | ``Cl.wedge, 6 => return .wedge (← reifyMV last2 fuel) (← reifyMV last fuel)
    | ``Cl.contract, 6 => return .contract (← reifyMV last2 fuel) (← reifyMV last fuel)
    | ``Cl.vee, 6 => return .vee (← reifyMV last2 fuel) (← reifyMV last fuel)
    | ``Cl.reverse, 5 => return .reverse (← reifyMV last fuel)
    | ``Cl.involute, 5 => return .involute (← reifyMV last fuel)
    | ``Cl.clifford, 5 => return .clifford (← reifyMV last fuel)
    | ``Cl.compl, 5 => return .compl (← reifyMV last fuel)
    | ``Cl.complInv, 5 => return .complInv (← reifyMV last fuel)
    | ``Cl.hodge, 5 => return .hodge (← reifyMV last fuel)
    | ``Cl.proj, 6 =>
      match ← evalNatExpr? last2 with
      | some k => return .proj k (← reifyMV last fuel)
      | none => asVar
    | _, _ => asVar
  | _ => asVar

/-! ## Metric entries -/

/-- The index `i : Fin n` as a numeral (`Fin.mk` if `Fin n` has no numerals). -/
def finLit (sp : Space) (i : Nat) : MetaM Expr := do
  try
    let e ← mkNumeral (mkApp (mkConst ``Fin) sp.n) i
    if ← isDefEq (mkApp2 (mkConst ``Fin.val) sp.n e) (mkNatLit i) then return e
  catch _ => pure ()
  let h ← mkDecideProof (mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat)
    (mkNatLit i) sp.n)
  return mkApp3 (mkConst ``Fin.mk) sp.n (mkNatLit i) h


/-- Read an expression as an integer: numerals, unfolding definitions and
deciding `if`s with closed conditions. -/
partial def evalIntValue? (e : Expr) (fuel : Nat := 32) : MetaM (Option Int) := do
  if fuel = 0 then return none
  let e := (← instantiateMVars e).headBeta
  if let some k := intNumeral? e then return some k
  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``ite _ =>
    if args.size != 5 then return none
    let d ← whnfD args[2]!
    if d.isAppOf ``Decidable.isTrue then evalIntValue? args[3]! (fuel - 1)
    else if d.isAppOf ``Decidable.isFalse then evalIntValue? args[4]! (fuel - 1)
    else return none
  | .const ``dite _ =>
    if args.size != 5 then return none
    let d ← whnfD args[2]!
    if d.isAppOf ``Decidable.isTrue then evalIntValue? (mkApp args[3]! d.appArg!) (fuel - 1)
    else if d.isAppOf ``Decidable.isFalse then evalIntValue? (mkApp args[4]! d.appArg!) (fuel - 1)
    else return none
  | .const .. =>
    match ← unfoldDefinition? e with
    | some e' => evalIntValue? e' (fuel - 1)
    | none => return none
  | _ => return none

/-- The metric entries: `int k` when `g i` is (definitionally) the numeral `k`,
the atom `met i` otherwise. -/
def metricEntries (sp : Space) : MetaM (List Poly) := do
  let mut ms := #[]
  for i in [0:sp.nVal] do
    let gi := mkApp sp.g (← finLit sp i)
    let entry ← match ← evalIntValue? gi with
      | some k =>
        let lit := mkApp3 (mkConst ``intLit [sp.u]) sp.R sp.inst (toExpr k)
        let ext := mkApp5 (mkConst ``extendMetric [sp.u]) sp.R sp.inst sp.n sp.g (mkNatLit i)
        if ← isDefEq lit ext then pure (Poly.int k) else pure (Poly.met i)
      | none => pure (Poly.met i)
    ms := ms.push entry
  return ms.toList

/-! ## Building coordinate equations -/

/-- The operations of `R`, synthesized once. -/
structure RingOps where
  /-- `HAdd R R R`. -/
  add : Expr
  /-- `HMul R R R`. -/
  mul : Expr
  /-- `HSub R R R`. -/
  sub : Expr
  /-- `Neg R`. -/
  neg : Expr
  /-- `HPow R Nat R`. -/
  pow : Expr

/-- Synthesize the ring operations of the space's coefficient ring. -/
def RingOps.mk' (sp : Space) : MetaM RingOps := do
  let u := sp.u
  let R := sp.R
  let hadd ← synthInstance (mkApp3 (mkConst ``HAdd [u, u, u]) R R R)
  let hmul ← synthInstance (mkApp3 (mkConst ``HMul [u, u, u]) R R R)
  let hsub ← synthInstance (mkApp3 (mkConst ``HSub [u, u, u]) R R R)
  let neg ← synthInstance (mkApp (mkConst ``Neg [u]) R)
  let hpow ← synthInstance (mkApp3 (mkConst ``HPow [u, 0, u]) R (mkConst ``Nat) R)
  return {
    add := mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) R R R hadd
    mul := mkApp4 (mkConst ``HMul.hMul [u, u, u]) R R R hmul
    sub := mkApp4 (mkConst ``HSub.hSub [u, u, u]) R R R hsub
    neg := mkApp2 (mkConst ``Neg.neg [u]) R neg
    pow := mkApp4 (mkConst ``HPow.hPow [u, 0, u]) R (mkConst ``Nat) R hpow }

/-- The ring expression a `Poly` denotes (definitionally equal to `Poly.denote`,
with the atoms substituted). -/
def Poly.toRExpr (sp : Space) (ops : RingOps) (atoms vars : Array Expr) : Poly → MetaM Expr
  | .int k => do
    if k ≥ 0 then mkNumeral sp.R k.toNat
    else return mkApp ops.neg (← mkNumeral sp.R k.natAbs)
  | .atom i => return atoms[i]!
  | .coeff v k =>
    return mkApp5 (mkConst ``Cl.coeff [sp.u]) sp.R sp.n sp.g vars[v]!
      (mkApp2 (mkConst ``BitVec.ofNat) sp.n (mkNatLit k))
  | .met i => return mkApp sp.g (← finLit sp i)
  | .add p q => return mkApp2 ops.add (← p.toRExpr sp ops atoms vars) (← q.toRExpr sp ops atoms vars)
  | .mul p q => return mkApp2 ops.mul (← p.toRExpr sp ops atoms vars) (← q.toRExpr sp ops atoms vars)
  | .sub p q => return mkApp2 ops.sub (← p.toRExpr sp ops atoms vars) (← q.toRExpr sp ops atoms vars)
  | .neg p => return mkApp ops.neg (← p.toRExpr sp ops atoms vars)
  | .pow p k => return mkApp2 ops.pow (← p.toRExpr sp ops atoms vars) (mkNatLit k)

/-- The name of blade `c` (`1`, `e₁`, `e₁₂`, …) for goal tags. -/
def bladeName (c : Nat) : String :=
  if c == 0 then "scalar" else
  let digits := (List.range 64).filter (c.testBit ·) |>.map fun i =>
    let d := i + 1
    if d < 10 then String.singleton (Char.ofNat (0x2080 + d)) else s!"_{d}"
  "e" ++ String.join digits

/-- The coordinate equations of `x = y`: for each blade `c`, the pair of ring
expressions and whether they are syntactically equal polynomials. -/
structure Coords where
  /-- `rx_c = ry_c` for every blade. -/
  eqs : Array Expr
  /-- `true` when the two polynomials are identical (the equation is `rfl`). -/
  trivial : Array Bool
  /-- The nested conjunction `eq₀ ∧ (eq₁ ∧ (… ∧ True))`, suffix by suffix
  (`conjs[c]` is the conjunction of the equations from `c` on). -/
  conjs : Array Expr

/-- Compute the coordinate equations of two reified expressions. -/
def coordsOf (sp : Space) (ops : RingOps) (ms : List Poly) (atoms vars : Array Expr) (x y : MExpr) :
    MetaM Coords := do
  let lx := (x.eval sp.nVal ms).toArray
  let ly := (y.eval sp.nVal ms).toArray
  let mut eqs := #[]
  let mut trivial := #[]
  for c in [0:2 ^ sp.nVal] do
    let p := lx[c]!
    let q := ly[c]!
    let rp ← p.toRExpr sp ops atoms vars
    let rq ← q.toRExpr sp ops atoms vars
    eqs := eqs.push (mkApp3 (mkConst ``Eq [sp.u.succ]) sp.R rp rq)
    trivial := trivial.push (p == q)
  let mut conjs := #[mkConst ``True]
  for c in (List.range (2 ^ sp.nVal)).reverse do
    conjs := conjs.push (mkApp2 (mkConst ``And) eqs[c]! conjs.back!)
  return { eqs, trivial, conjs := conjs.reverse }

/-! ## The tactic core -/

/-- Recognize `Cl g` and collect the space data. -/
def spaceOf? (ty : Expr) : MetaM (Option Space) := do
  let ty ← whnfR (← instantiateMVars ty)
  let .app (.app (.app (.const ``Cl [u]) R) n) g := ty | return none
  let some nVal ← evalNatExpr? n | return none
  let inst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommRing [u]) R)
  return some { u, R, inst, n, nVal, g, clTy := ty }

/-- Prove `x = y` in a concrete space, up to the coordinate equations: returns
the goals for the coordinate equations that are not syntactically trivial,
tagged with their blade names. Multivector hypotheses of the same space become
coordinate hypotheses. -/
def cliffordCore (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let tgt ← instantiateMVars (← goal.getType)
  let tgt ← zetaReduce tgt
  let some (ty, lhs, rhs) := tgt.eq? |
    throwError "clifford: the goal is not an equation{indentExpr tgt}"
  let some sp ← spaceOf? ty |
    throwError "clifford: the goal is not an equation of multivectors `Cl g` with `g : Fin n → R` \
      and a numeral `n`{indentExpr ty}"
  if sp.nVal > 6 then
    throwError "clifford: dimension {sp.nVal} is too large (the coordinates are computed densely; n ≤ 6)"
  -- multivector hypotheses of the same space
  let mut hyps : Array (Expr × Expr × Expr) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let hty ← instantiateMVars decl.type
    let some (hTy, a, b) := hty.eq? | continue
    let hTy ← whnfR hTy
    unless hTy.isAppOf ``Cl do continue
    unless ← withReducible (isDefEq hTy sp.clTy) do continue
    hyps := hyps.push (decl.toExpr, a, b)
  -- reify everything in one state, so that atoms are shared
  let act : ReifyM (MExpr × MExpr × Array (MExpr × MExpr)) := do
    let mx ← reifyMV lhs
    let my ← reifyMV rhs
    let hs ← hyps.mapM fun (_, a, b) => return (← reifyMV a, ← reifyMV b)
    return (mx, my, hs)
  let ((mx, my, hs), st) ← (act.run sp).run {}
  let ms ← metricEntries sp
  let ops ← RingOps.mk' sp
  let ρ := mkListLit sp.u sp.R st.atoms.toList
  let vs := mkListLit sp.u sp.clTy st.vars.toList
  let msE := mkListLit 0 (mkConst ``Poly) (ms.map Poly.quote)
  -- `MetricOK g ρ vs ms`, entry by entry (each entry is `rfl`)
  let mut hbelow := mkConst ``True.intro
  let mut belowTy := mkConst ``True
  for i in [0:sp.nVal] do
    let ext := mkApp5 (mkConst ``extendMetric [sp.u]) sp.R sp.inst sp.n sp.g (mkNatLit i)
    let entryTy := mkApp3 (mkConst ``Eq [sp.u.succ]) sp.R ext ext
    hbelow := mkApp4 (mkConst ``And.intro) belowTy entryTy hbelow (mkApp2 (mkConst ``Eq.refl [sp.u.succ]) sp.R ext)
    belowTy := mkApp2 (mkConst ``And) belowTy entryTy
  let hms := mkApp8 (mkConst ``metricOK_of_allBelow [sp.u]) sp.R sp.inst sp.n sp.g ρ vs msE hbelow
  -- coordinate hypotheses
  let mut newHyps : Array Hypothesis := #[]
  for h : k in [0:hs.size] do
    let (ma, mb) := hs[k]
    let (hE, _, _) := hyps[k]!
    let co ← coordsOf sp ops ms st.atoms st.vars ma mb
    let all := mkApp (mkApp10 (mkConst ``coords_of_eq [sp.u]) sp.R sp.inst sp.n sp.g ρ vs msE hms
      ma.quote mb.quote) hE
    -- project the non-trivial components
    let mut proj := all
    for c in [0:2 ^ sp.nVal] do
      unless co.trivial[c]! do
        let comp := mkApp3 (mkConst ``And.left) co.eqs[c]! co.conjs[c + 1]! proj
        newHyps := newHyps.push { userName := (← mkFreshUserName `hc), type := co.eqs[c]!, value := comp }
      proj := mkApp3 (mkConst ``And.right) co.eqs[c]! co.conjs[c + 1]! proj
  let (_, goal) ← goal.assertHypotheses newHyps
  goal.withContext do
    let co ← coordsOf sp ops ms st.atoms st.vars mx my
    -- the conjunction, with one new goal per non-trivial coordinate
    let mut goals := #[]
    let mut proofs := #[]
    for c in [0:2 ^ sp.nVal] do
      if co.trivial[c]! then
        let some (_, rp, _) := co.eqs[c]!.eq? | unreachable!
        proofs := proofs.push (mkApp2 (mkConst ``Eq.refl [sp.u.succ]) sp.R rp)
      else
        let m ← mkFreshExprSyntheticOpaqueMVar co.eqs[c]! (tag := Name.mkSimple (bladeName c))
        goals := goals.push m.mvarId!
        proofs := proofs.push m
    let mut conj := mkConst ``True.intro
    for c in (List.range (2 ^ sp.nVal)).reverse do
      conj := mkApp4 (mkConst ``And.intro) co.eqs[c]! co.conjs[c + 1]! proofs[c]! conj
    let pf := mkApp (mkApp10 (mkConst ``eq_of_coords [sp.u]) sp.R sp.inst sp.n sp.g ρ vs msE hms
      mx.quote my.quote) conj
    goal.assign (← mkExpectedTypeHint pf tgt)
    return goals.toList

/-! ## Syntax -/

/--
`clifford` proves an equation between multivectors of a concrete space by
blade extensionality: it computes the `2ⁿ` coordinates of both sides from the
blade tables of `Grassmann.Spec` and closes each coordinate equation with
`grind`.

* The goal is `x = y` with `x y : Cl g`, `g : Fin n → R`, `n` a numeral
  (at most 6), `R` any `Lean.Grind.CommRing`.
* Understood: `+ - * •`, `0`, `1`, `Cl.scalar`, `Cl.blade`, `Cl.gen`,
  `Cl.pseudoscalar`, `Cl.wedge`, `Cl.contract`, `Cl.vee`, `Cl.reverse`,
  `Cl.involute`, `Cl.clifford`, `Cl.proj`, `Cl.compl`, `Cl.complInv`,
  `Cl.hodge`; definitions are unfolded; any other multivector is opaque (its
  coordinates become atoms).
* Metric entries that are integer numerals (after unfolding `g`) are folded
  as constants; others stay symbolic (`g ⟨i, _⟩`).
* Hypotheses `h : a = b` between multivectors of the same space are turned
  into coordinate hypotheses; scalar hypotheses are used by `grind` as usual.

`clifford [p, …]` passes extra parameters to `grind`; `clifford_nf` leaves the
coordinate equations as goals (one per blade, tagged `e₁₂` etc.).
-/
syntax (name := cliffordTac) "clifford" (" [" withoutPosition(Lean.Parser.Tactic.grindParam,*) "]")? :
  tactic

@[inherit_doc cliffordTac]
syntax (name := cliffordNF) "clifford_nf" : tactic

@[tactic cliffordNF] def evalCliffordNF : Tactic := fun _ => do
  let goal ← getMainGoal
  let gs ← cliffordCore goal
  replaceMainGoal gs

@[tactic cliffordTac] def evalClifford : Tactic := fun stx => do
  let goal ← getMainGoal
  let gs ← cliffordCore goal
  let closer ← if stx[1].isNone then `(tactic| grind) else
    let ps : Syntax.TSepArray `Lean.Parser.Tactic.grindParam "," := ⟨stx[1][1].getSepArgs⟩
    `(tactic| grind [$ps,*])
  for g in gs do
    setGoals [g]
    if let some (_, l, r) := (← instantiateMVars (← g.getType)).eq? then
      if let (some a, some b) := (intNumeral? l, intNumeral? r) then
        throwError "clifford: the {← g.getTag} coordinates differ: {a} on the left, {b} on the right"
    try
      evalTactic closer
    catch e =>
      throwError "clifford: `grind` could not prove the {← g.getTag} coordinate{indentExpr (← g.getType)}\n\
        {e.toMessageData}"
  setGoals []

end Grassmann.Tactic
