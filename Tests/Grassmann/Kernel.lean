/-
The reference kernels against DirectSum's blade-level rules.

For every test space, every `BinOp` and every pair of storage layouts (and
every `UnOp` and layout), the kernel result on random dense `Rat` inputs,
evaluated into the full layout, equals the bilinear (linear) extension of the
blade rules computed independently here, blade pair by blade pair, from
`TensorBundle.apply₂`/`apply₁`. Conformal spaces follow Grassmann's
container-level complements (oracle defect `conformal-blade-complement`), so
there the complement-based operations are compared with DirectSum's
container-level blade functions (`complementrightChain`, ...) instead.

Also checked: projecting plans keep exactly the part of the product in the
result layout; the strict plans behind every typed result type build without a
contribution outside the result layout (all grade pairs); the plan cache
returns identical plans; complements in a dyadic space fail with Julia's error.
-/
import Tests.Grassmann.Common

open Grassmann DirectSum StaticVectors

namespace GrassmannTests.Kernel

/-- A random `Rat` vector of length `n`. -/
def randRat (n : Nat) : Tests.Gen (Values Rat n) := do
  let v ← randValues n
  return v.map fun (k : Int) => (k : Rat)

/-- The container-level terms of a unary operation on blade `b` in a conformal
space (Julia's `Chain`/`Multivector` kernels), from DirectSum's blade functions. -/
def conformalUnary (V : TensorBundle) (op : UnOp) (b : UInt64) : Option (Except String Terms) :=
  match op with
  | .complementright => some (V.complementrightChain b)
  | .complementleft => some (V.complementleftChain b)
  | .complementrighthodge => some (V.complementrighthodgeChain b)
  | .complementlefthodge => some (V.complementlefthodgeChain b)
  | .metric => some (.ok (V.metricChain b))
  | _ => none

/-- Unary operations whose container semantics in a conformal space have no
blade-level counterpart (Julia throws for `antimetric` there). -/
def conformalSkipUnary : List UnOp := [.antimetric, .complementrightanti, .complementleftanti]

/-- Binary operations built from complements. -/
def complementBinary : List BinOp := [.cross, .veedot, .antidot]

/-- The independent reference of `op` between layouts, into the full layout. -/
def refBinary (V : TensorBundle) (op : BinOp) (la lb : Layout) (x y : Array Rat) : Option (Array Rat) :=
  Id.run do
    let n := V.n
    let mut out := Array.replicate (2 ^ n) (0 : Rat)
    for a in la.blades n, i in [0:la.size n] do
      for b in lb.blades n, j in [0:lb.size n] do
        match V.apply₂ op a b with
        | .ok r =>
          for t in r.bladeTerms do
            if t.z == 0 then
              out := out.modify (Leibniz.basisRank n t.bits) (· + t.coef * x[i]! * y[j]!)
        | .error _ => return none
    return some out

/-- The independent reference of a unary `op` from layout `la`, into the full layout. -/
def refUnary (V : TensorBundle) (op : UnOp) (la : Layout) (x : Array Rat) : Option (Array Rat) :=
  Id.run do
    let n := V.n
    let mut out := Array.replicate (2 ^ n) (0 : Rat)
    for a in la.blades n, i in [0:la.size n] do
      let ts : Except String Terms :=
        if V.hasconformal then
          match conformalUnary V op a with
          | some r => r
          | none => (V.apply₁ op a).map fun r => r.bladeTerms.map fun t => (t.bits, t.coef)
        else (V.apply₁ op a).map fun r => r.bladeTerms.filter (·.z == 0) |>.map fun t => (t.bits, t.coef)
      match ts with
      | .ok ts => for (k, c) in ts do out := out.modify (Leibniz.basisRank n k) (· + c * x[i]!)
      | .error _ => return none
    return some out

/-- The result layouts of the typed binary instances for chain/half operands. -/
def typedResults (n : Nat) : List (BinOp × Layout × Layout × Layout) := Id.run do
  let half := fun (b : Bool) => if b then Layout.odd else .even
  let odd := fun (g : Nat) => g % 2 == 1
  let mut out := []
  for g in [0:n + 1] do
    for h in [0:n + 1] do
      out := (.mul, .chain g, .chain h, half (odd (g + h))) :: (.wedge, .chain g, .chain h, .chain (g + h))
        :: (.vee, .chain g, .chain h, .chain (g + h - n)) :: (.contraction, .chain g, .chain h, .chain (g - h))
        :: out
    for q in [false, true] do
      for op in [BinOp.mul, .wedge, .contraction] do
        out := (op, .chain g, half q, half (q ^^ odd g)) :: (op, half q, .chain g, half (q ^^ odd g)) :: out
      out := (.vee, .chain g, half q, half (q ^^ odd g ^^ odd n))
        :: (.vee, half q, .chain g, half (q ^^ odd g ^^ odd n)) :: out
  for p in [false, true] do
    for q in [false, true] do
      for op in [BinOp.mul, .wedge, .contraction] do
        out := (op, half p, half q, half (p ^^ q)) :: out
      out := (.vee, half p, half q, half (p ^^ q ^^ odd n)) :: out
  return out

/-- Run the kernel suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  let mut rng := Tests.Rng.ofSeed 424242
  for (nm, V) in spaces do
    let n := V.n
    let ls := layouts n
    -- binary operations, every layout pair
    for op in BinOp.all do
      for la in ls do
        for lb in ls do
          let ((x, y), r) := StateT.run (do return (← randRat (la.size n), ← randRat (lb.size n)) : Tests.Gen _) rng
          rng := r
          let got := (Kernels.bin (V := V) op la lb .full x y).toArray
          if V.hasconformal && complementBinary.contains op then
            -- container semantics: compare with the composition of typed containers
            let xm := convertLayout n la .full x
            let ym := convertLayout n lb .full y
            let want : Multivector V Rat := match op with
              | .cross => ⋆((⟨xm⟩ : Multivector V Rat) ∧ (⟨ym⟩ : Multivector V Rat) : Multivector V Rat)
              | .veedot => Multivector.complementleft
                  (Multivector.complementright ⟨xm⟩ * Multivector.complementright ⟨ym⟩)
              | _ => Multivector.complementleft (Multivector.complementright ⟨xm⟩ ⋅
                  Multivector.complementright ⟨ym⟩ : Multivector V Rat)
            t := t.check (got == want.v.toArray) s!"{nm} {repr op} {repr la}×{repr lb}: ≠ container composition"
          else
            match refBinary V op la lb x.toArray y.toArray with
            | some want => t := t.check (got == want) s!"{nm} {repr op} {repr la}×{repr lb}: kernel ≠ blade reference"
            | none => t := t.skip "blade rule error"
      -- projecting plans: the part of the full product in a chain layout
      for g in [0:n + 1] do
        let ((x, y), r) := StateT.run (do return (← randRat (2 ^ n), ← randRat (2 ^ n)) : Tests.Gen _) rng
        rng := r
        let full := Kernels.bin (V := V) op .full .full .full x y
        let proj := Kernels.binProj (V := V) op .full .full (.chain g) x y
        t := t.check (proj.toArray == (convertLayout n .full (.chain g) full).toArray)
          s!"{nm} {repr op} projection onto grade {g}"
    -- unary operations, every layout
    for op in UnOp.all do
      if V.hasconformal && conformalSkipUnary.contains op then
        t := t.skip "conformal antimetric (Julia throws)"
        continue
      for la in ls do
        let (x, r) := StateT.run (randRat (la.size n)) rng
        rng := r
        let got := (Kernels.un (V := V) op la .full x).toArray
        match refUnary V op la x.toArray with
        | some want => t := t.check (got == want) s!"{nm} {repr op} {repr la}: kernel ≠ blade reference"
        | none => t := t.skip "blade rule error"
    -- the strict plans behind the typed result types
    for (op, la, lb, lc) in typedResults n do
      t := t.check (Grassmann.Kernel.build { V, op := .bin op, la, lb, lc }).toBool
        s!"{nm} {repr op} {repr la}×{repr lb} ⊄ {repr lc}"
    -- the cache returns the plan it built
    let k : Grassmann.Kernel.PlanKey := { V, op := .bin .mul, la := .full, lb := .full, lc := .full }
    let same := match Grassmann.Kernel.plan k, Grassmann.Kernel.build k with
      | .ok p, .ok q => p.entries == q.entries
      | _, _ => false
    t := t.check same s!"{nm}: cached plan ≠ built plan"
  -- dyadic spaces: complements fail with Julia's message; products still plan
  let mixed := (S!"++") ⊕ (S!"++")′
  let kc : Grassmann.Kernel.PlanKey := { V := mixed, op := .un .complementright, la := .full, lb := .full, lc := .full }
  let km : Grassmann.Kernel.PlanKey := { V := mixed, op := .bin .mul, la := .full, lb := .full, lc := .full }
  t := t.check (Grassmann.Kernel.build kc).isOk.not "dyadic complement must fail"
  t := t.check (Grassmann.Kernel.build km).isOk "dyadic product must plan"
  return t

end GrassmannTests.Kernel
