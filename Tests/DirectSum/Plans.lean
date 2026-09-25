/-
Tests of the blade-level interface for the Grassmann core (`DirectSum.Ops`):

* the result-container rules of DESIGN.md §4.2: for every operation and every
  pair of `Chain` grades, `plan₂` into `chainResult` succeeds (no contribution
  falls outside the container Julia's types predict), and the unary
  involutions/complements map `Chain G` to `Chain G` / `Chain (n-G)`;
* `Spinor`/`CoSpinor` products land in the half of the right parity;
* a plan interpreter over dense `Rat` vectors reproduces the blade-level
  products (bilinearity of the plan), and the full geometric-product plan is
  associative on random multivectors;
* `terms₂`/`terms₁` agree with the `BladeResult` of `apply₂`/`apply₁`;
* the AbstractTensors kind classes see a `Submanifold V G` as a grade-`G` term.
-/
import Tests.DirectSum.Common
import Tests.Util.Random
import DirectSum.Ops

open DirectSum DirectSum.Bits

namespace DirectSumTests.Plans

/-- Spaces without tangent or dyadic structure (where Julia's container rules apply). -/
def spaces : List (String × TensorBundle) :=
  [ ("E3", ℝ^3), ("M4", S!"-+++"), ("I4", ℝ4), ("D3", D!"1,2,-3"), ("D3deg", D!"1,1,0"),
    ("P4orig", S!"∅+++"), ("dual3", (S!"+-+")′), ("C3", S!"∞∅+"), ("C5", S!"∞∅+++"),
    ("MT3", .metricTensor #[#[1, 1/2, 0], #[1/2, 1, 1/2], #[0, 1/2, 1]]), ("E0", ℝ^0), ("E1", ℝ^1) ]

/-- Apply a binary plan to dense coefficient vectors. -/
def runPlan (p : Array PlanEntry) (x y : Array Rat) (size : Nat) : Array Rat :=
  p.foldl (init := Array.replicate size 0) fun out e =>
    out.modify e.ic (· + e.coef * x[e.ia]! * y[e.ib]!)

/-- The reference value of `op` on dense vectors in layouts `la`, `lb`, as a
dense vector in `lc`, computed blade pair by blade pair through `apply₂`. -/
def reference (V : TensorBundle) (op : BinOp) (la lb lc : Layout) (x y : Array Rat) : Array Rat := Id.run do
  let mut out := Array.replicate (lc.size V.n) 0
  for a in la.blades V.n, i in [0:la.size V.n] do
    for b in lb.blades V.n, j in [0:lb.size V.n] do
      if let .ok r := V.apply₂ op a b then
        for (k, c) in r.terms do
          if lc.contains V.n k then out := out.modify (lc.rank V.n k) (· + c * x[i]! * y[j]!)
  return out

/-- A random small-integer dense vector. -/
def randVec (g : Tests.Rng) (size : Nat) : Array Rat × Tests.Rng := Id.run do
  let mut g := g
  let mut v := #[]
  for _ in [0:size] do
    let (k, g') := g.int (-3) 3
    g := g'
    v := v.push (k : Rat)
  return (v, g)

/-- `terms` agree with the `BladeResult` they flatten (or both fail). -/
def sameTerms (ts : Except String (Array BladeTerm)) (r : Except String BladeResult) : Bool :=
  match ts, r with
  | .ok ts, .ok r => ts.map (fun (bt : BladeTerm) => (bt.bits, bt.coef)) == r.terms.filter (·.2 != 0)
  | .error _, .error _ => true
  | _, _ => false

/-- Run the interface suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  let mut rng := Tests.Rng.ofSeed 20260924
  for (nm, V) in spaces do
    let n := V.n
    -- container rules for Chain × Chain
    for op in BinOp.all do
      for g in [0:n + 1] do
        for h in [0:n + 1] do
          let lc := V.chainResult op g h
          match V.plan₂ op (.chain g) (.chain h) lc with
          | .ok p =>
            let (x, r1) := randVec rng (Layout.size n (.chain g))
            let (y, r2) := randVec r1 (Layout.size n (.chain h))
            rng := r2
            t := t.check (runPlan p x y (lc.size n) == reference V op (.chain g) (.chain h) lc x y)
              s!"{nm} {repr op} chain {g}×{h}: plan ≠ reference"
          | .error e => t := t.bad s!"{nm} {repr op} chain {g}×{h} → {repr lc}: {e}"
    -- halves: products preserve the Z₂ grading
    for (la, lb, lc) in [(Layout.even, Layout.even, Layout.even), (.even, .odd, .odd), (.odd, .even, .odd),
        (.odd, .odd, .even)] do
      t := t.check (V.plan₂ .mul la lb lc).toBool s!"{nm} half product {repr la}×{repr lb} ⊄ {repr lc}"
    -- unary: involutions keep the grade, complements map G ↦ n - G
    for g in [0:n + 1] do
      for op in [UnOp.reverse, .involute, .clifford, .conj, .antireverse, .metric] do
        t := t.check (V.plan₁ op (.chain g) (.chain g)).toBool s!"{nm} {repr op} chain {g}"
      for op in [UnOp.complementright, .complementleft, .complementrighthodge, .complementlefthodge] do
        t := t.check (V.plan₁ op (.chain g) (.chain (n - g))).toBool s!"{nm} {repr op} chain {g}"
    -- terms₂ / terms₁ are the BladeResult terms
    let blades := Leibniz.indexBasisAll n
    let mut agreeTerms := true
    for a in blades do
      for op in UnOp.all do
        agreeTerms := agreeTerms && sameTerms (V.terms₁ op a) (V.apply₁ op a)
      for b in blades do
        for op in BinOp.all do
          agreeTerms := agreeTerms && sameTerms (V.terms₂ op a b) (V.apply₂ op a b)
    t := t.check agreeTerms s!"{nm} terms₁/terms₂ ≠ apply₁/apply₂ terms"
    -- the full geometric-product plan is associative on random multivectors
    if n ≤ 4 then
      match V.plan₂ .mul .full .full .full with
      | .ok p =>
        let size := 2 ^ n
        for _ in [0:5] do
          let (x, r1) := randVec rng size
          let (y, r2) := randVec r1 size
          let (z, r3) := randVec r2 size
          rng := r3
          t := t.check (runPlan p (runPlan p x y size) z size == runPlan p x (runPlan p y z size) size)
            s!"{nm} full plan not associative"
      | .error e => t := t.bad s!"{nm} full mul plan: {e}"
  -- dyadic spaces: complements are undefined, products still plan
  let mixed := ℝ^2 ⊕ (ℝ^2)′
  t := t.check (!(mixed.plan₁ .complementright (.chain 1) (.chain 3)).toBool) "mixed2 complement must fail"
  t := t.check (mixed.plan₂ .mul .full .full .full).toBool "mixed2 full product plan"
  return t

/-! Compile-time checks of the typed-blade view. -/

example : AbstractTensors.rank (⟨3⟩ : Submanifold ℝ3 2) = 2 := rfl
example : AbstractTensors.mdims (⟨3⟩ : Submanifold (ℝ^5) 2) = 5 := rfl
#guard ((Submanifold.ofLabel? "v13" : Option (Submanifold ℝ3 2)).map (·.bits)) == some 5
#guard ((Submanifold.ofLabel? "v13" : Option (Submanifold ℝ3 1)).map (·.bits)) == none
#guard ((Submanifold.ofLabel? "v∞∅1" : Option (Submanifold CGA3 3)).map (·.bits)) == some 7
example : Layout.size 4 .even = 8 ∧ Layout.size 5 .odd = 16 ∧ Layout.size 4 (.chain 2) = 6 := by decide

end DirectSumTests.Plans
