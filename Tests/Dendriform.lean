import Dendriform
import Tests.AbstractLattices.Harness
import Tests.Dendriform.Static
import Tests.Util.Random

/-!
Dendriform tests: goldens from `oracle/dendriform/gen.jl` (`oracle/golden/dendriform/`),
compared through the Julia-convention layer (`Dendriform.Julia`) where Julia's degenerate
shortcuts matter, plus randomized checks of the proven identities on the concrete
functions. Compile-time checks live in `Tests.Dendriform.Static`.
-/

open Dendriform Tests.Small

namespace Tests.Dendriform

/-- A tree from its Loday name in a golden. -/
def jTree (j : Lean.Json) : TestM Tree := do
  let ns ← jNats j
  match Tree.ofName? ns.toList with
  | some t => return t
  | none => throw <| IO.userError s!"invalid Loday name {ns}"

/-- A runtime-degree grove from `{d, rows}`. -/
def jGrove (j : Lean.Json) : TestM SomeGrove := do
  let d ← gNat j "d"
  let ts ← (← gArr j "rows").mapM jTree
  match Grove.ofList? d ts.toList with
  | some g => return ⟨d, g⟩
  | none => throw <| IO.userError "grove rows of the wrong degree"

/-- Render a grove result the way the golden encodes it. -/
def showGrove (g : SomeGrove) : String := s!"{g.1}:{g.2.rows.map Tree.name}"

/-- Render a golden grove result (`{d, rows}` or `{err}`). -/
def showGolden (j : Lean.Json) : TestM String := do
  match j.getObjVal? "err" with
  | .ok e => return s!"error {← jStr e}"
  | .error _ =>
    let d ← gNat j "d"
    let rs ← (← gArr j "rows").mapM jNats
    return s!"{d}:{rs.toList.map (·.toList)}"

/-- Render an `Except` grove result. -/
def showResult (r : Except String SomeGrove) : String :=
  match r with
  | .ok g => showGrove g
  | .error e => s!"error {e}"

/-- Julia's `string(::Rational)`. -/
def fmtRat (r : Rat) : String := s!"{r.num}//{r.den}"

/-- The single-row grove of a tree, with its degree. -/
def single (t : Tree) : SomeGrove := ⟨t.deg, Grove.ofTree ⟨t, rfl⟩⟩

def totalgroves : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/totalgroves.json"
  for c in ← gArr j "groves" do
    let d ← gNat c "d"
    let names ← (← gArr c "names").mapM jNats
    checkEq s!"Y{d} names" ((totalGrove d).trees.map fun t => t.name.toArray) names
    checkEq s!"Y{d} tree integers" (totalGrove d).tis (← gNats c "ti")
    if let .ok rs := (← jField c "rational_shift").getArr? then
      checkEq s!"TreeRational({d})" ((treeRationals d).map fmtRat).toArray (← rs.mapM jStr)
      let rn ← gArr c "rational_noshift"
      checkEq s!"TreeRational({d}) unshifted" ((treeRationals d false).map fmtRat).toArray
        (← rn.mapM jStr)
    -- tree index is the rank, and PBTree(d, i) inverts it
    if d > 0 then
      check s!"Y{d} treeIndex" ((totalGrove d).trees.toList.zipIdx.all fun (t, i) =>
        t.treeIndex == i + 1 && treeOfIndex? d (i + 1) == some t)
  let cats ← (← gArr j "catalan").mapM jNat
  checkEq "catalan 0..20" ((List.range 21).map catalan).toArray cats
  checkEq "ΘMax 1..12" ((List.range 12).map fun d => Tree.thetaMax (d + 1)).toArray
    (← gNats j "thetamax")

def treeOps : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/tree_ops.json"
  for c in ← gArr j "pairs" do
    let x ← jTree (← jField c "x")
    let y ← jTree (← jField c "y")
    let lbl := s!"{x.name} {y.name}"
    checkEq s!"{lbl} +" (showGrove (Julia.add (single x) (single y))) (← showGolden (← jField c "sum"))
    checkEq s!"{lbl} ⊣" (showResult (Julia.dashv (single x) (single y)))
      (← showGolden (← jField c "dashv"))
    checkEq s!"{lbl} ⊢" (showResult (Julia.vdash (single x) (single y)))
      (← showGolden (← jField c "vdash"))
    if let .ok m := (← jField c "mul").getObj? then
      checkEq s!"{lbl} *" (showResult (Julia.mul (single x) (single y)))
        (← showGolden (Lean.Json.obj m))
    checkEq s!"{lbl} ∨" (Tree.node x y).name.toArray (← gNats c "graft")
    checkEq s!"{lbl} /" (x / y).name.toArray (← gNats c "over")
    checkEq s!"{lbl} \\" (x \ y).name.toArray (← gNats c "under")
  for c in ← gArr j "single" do
    let x ← jTree (← jField c "x")
    let lbl := s!"{x.name}"
    checkEq s!"{lbl} σ" x.σ.name.toArray (← gNats c "sigma")
    checkEq s!"{lbl} left" x.left.name.toArray (← gNats c "left")
    checkEq s!"{lbl} right" x.right.name.toArray (← gNats c "right")
    if x.deg > 0 then
      checkEq s!"{lbl} treeindex" x.treeIndex (← gNat c "index")
      checkEq s!"{lbl} rational" (fmtRat x.treeRational) (← gStr c "rational")
    checkEq s!"{lbl} TreeInteger" x.treeInteger (← gNat c "ti")
    checkEq s!"{lbl} posetnext" ((Tree.nextList x).map (·.name.toArray)).toArray
      (← (← gArr c "next").mapM jNats)
    checkEq s!"{lbl} posetprev" ((Tree.prevList x).map (·.name.toArray)).toArray
      (← (← gArr c "prev").mapM jNats)
    checkEq s!"{lbl} print" (x.print) (← gStr c "print")
    checkEq s!"{lbl} print display" (x.print true) (← gStr c "print_display")
    checkEq s!"{lbl} primitive" x.isPrimitive (← gBool c "primitive")

def poset : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/poset.json"
  for c in ← gArr j "pairs" do
    let x ← jTree (← jField c "x")
    let y ← jTree (← jField c "y")
    let lbl := s!"{x.name} {y.name}"
    checkEq s!"{lbl} <" (Tree.tamariLt x y) (← gBool c "lt")
    checkEq s!"{lbl} ≤" (Tree.tamariLe x y) (← gBool c "le")
    checkEq s!"{lbl} >" (Tree.tamariGt x y) (← gBool c "gt")
    checkEq s!"{lbl} ≥" (Tree.tamariGe x y) (← gBool c "ge")
    checkEq s!"{lbl} ⋖" (Tree.covers x y) (← gBool c "covers")
    checkEq s!"{lbl} ⋗" (Tree.coveredBy x y) (← gBool c "coveredby")
    if let .ok bs := (← jField c "between").getArr? then
      checkEq s!"{lbl} ⊴" ((betweenList x y).map (·.name.toArray)).toArray (← bs.mapM jNats)

def groveOps : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/grove_ops.json"
  for c in ← gArr j "groves" do
    let g ← jGrove (← jField c "g")
    let lbl := showGrove g
    checkEq s!"{lbl} groveindex" g.2.index (← gNat c "index")
    let bits := (List.range (catalan g.1)).map fun i => if g.2.bits.testBit i then 1 else 0
    checkEq s!"{lbl} grovebit" bits.toArray (← gNats c "bits")
    checkEq s!"{lbl} treeindex" g.2.treeIndices.toArray (← gNats c "treeindex")
    checkEq s!"{lbl} GroveBin" (toString (GroveBin.ofGrove g.2)) (← gStr c "bin")
    checkEq s!"{lbl} print" g.2.print (← gStr c "print")
    checkEq s!"{lbl} print display" (g.2.print true) (← gStr c "print_display")
    checkEq s!"{lbl} σ" (showGrove ⟨g.1, g.2.σ⟩) (← showGolden (← jField c "sigma"))
    checkEq s!"{lbl} grovesort!" (g.2.sort.rows.map (·.name.toArray)).toArray
      (← (← gArr c "sorted").mapM jNats)
  for c in ← gArr j "pairs" do
    let x ← jGrove (← jField c "x")
    let y ← jGrove (← jField c "y")
    let lbl := s!"{showGrove x} | {showGrove y}"
    checkEq s!"{lbl} +" (showGrove (Julia.add x y)) (← showGolden (← jField c "sum"))
    checkEq s!"{lbl} ⊣" (showResult (Julia.dashv x y)) (← showGolden (← jField c "dashv"))
    checkEq s!"{lbl} ⊢" (showResult (Julia.vdash x y)) (← showGolden (← jField c "vdash"))
    if let .ok m := (← jField c "mul").getObj? then
      checkEq s!"{lbl} *" (showResult (Julia.mul x y)) (← showGolden (Lean.Json.obj m))
    checkEq s!"{lbl} ==" (Julia.eq x y) (← gBool c "eq")
    checkEq s!"{lbl} < (index)" (decide (x.2.index < y.2.index)) (← gBool c "lt_index")
    if h : x.1 = y.1 then
      let (u, dups) := Grove.unionCount [h ▸ x.2, y.2]
      checkEq s!"{lbl} ∪" (showGrove ⟨y.1, u⟩) (← showGolden (← jField c "union"))
      checkEq s!"{lbl} ∪ duplicates" dups (← gNat c "union_dups")
  for c in ← gArr j "loday" do
    let p ← gNat c "p"
    let q ← gNat c "q"
    let op ← gStr c "op"
    let r : String := match op with
      | "sum" => toString (GroveBin.ofGrove (Grove.total p + Grove.total q))
      | _ => toString (GroveBin.ofGrove (Grove.total p * Grove.total q))
    checkEq s!"Y{p} {op} Y{q}" r (← gStr c "bin")

def degenerate : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/degenerate.json"
  let gs ← jField j "groves"
  for c in ← gArr j "cases" do
    let op ← gStr c "op"
    let xn ← gStr c "x"
    let yn ← gStr c "y"
    let x ← jGrove (← jField gs xn)
    let y ← jGrove (← jField gs yn)
    let got := match op with
      | "dashv" => showResult (Julia.dashv x y)
      | "vdash" => showResult (Julia.vdash x y)
      | "sum" => showGrove (Julia.add x y)
      | _ => showResult (Julia.mul x y)
    checkEq s!"{xn} {op} {yn}" got (← showGolden (← jField c "out"))

def display : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/display.json"
  for c in ← gArr j "bins" do
    let b : GroveBin := ⟨← gNat c "d", ← gNat c "size", ← gNat c "gbin"⟩
    checkEq s!"GroveBin {b.degr} {b.gbin}" (toString b) (← gStr c "str")
  checkEq "print ∅" (Tree.leaf.print) (← gStr j "empty_tree")
  checkEq "print ∅ display" (Tree.leaf.print true) (← gStr j "empty_tree_display")
  checkEq "print Grove(0)" (Julia.zero.print) (← gStr j "zero_grove")
  checkEq "print Grove(|)" ((single .leaf).print) (← gStr j "leaf_grove")
  -- README: Grove(3,7) ⊣ ([1,2] ∪ [2,1])
  let readme := Grove.dashv (Grove.ofIndex 3 7) (Grove.union (Grove.ofIndex 2 1) (Grove.ofIndex 2 2))
  let rj ← jField j "readme"
  checkEq "README rows" (showGrove ⟨5, readme⟩) (← showGolden (← jField rj "g"))
  checkEq "README print" readme.print (← gStr rj "print")
  checkEq "README print display" (readme.print true) (← gStr rj "print_display")
  checkEq "README GroveBin" (toString (GroveBin.ofGrove readme)) (← gStr rj "bin")
  -- README: Grove(2,3) * ([1,2,3] ∪ [3,2,1]) |> GroveBin
  let m := Grove.ofIndex 2 3 * Grove.ofIndex 3 (1 + 16)
  checkEq "README product" (toString (GroveBin.ofGrove m)) (← gStr j "readme_mul")

def float16 : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/float16.json"
  for c in ← gArr j "rationals" do
    let n ← gNat c "num"
    let d ← gNat c "den"
    checkEq s!"Float16({n}//{d})" (toString (JuliaBase.Float16.ofRat n d)) (← gStr c "str")
  let bits ← (← gArr j "bits").mapM jStr
  for h : b in [0:bits.size] do
    let x : JuliaBase.Float16 := ⟨b / 1024, b % 1024⟩
    checkEq s!"Float16 bits {b}" (toString x) bits[b]

def intervalTools : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/intervals.json"
  for c in ← gArr j "cases" do
    let d ← gNat c "d"
    checkEq s!"intervals({d})" (intervals d) (← (← gArr c "intervals").mapM jNat)
    checkEq s!"intcomp({d})" (intcomp d).1 (← gNats c "intcomp")
    checkEq s!"intcompt({d})" (intcompt d).1 (← gNats c "intcompt")
    checkEq s!"intervals_full({d})" (intervalsFull d) (← jBools (← jField c "full"))
    checkEq s!"print_interval_bin({d})" (printIntervalBin d) (← gStr c "print_interval_bin")
    checkEq s!"print_intcomp_bin({d})" (printIntcompBin d) (← gStr c "print_intcomp_bin")
    checkEq s!"print_intcompt_bin({d})" (printIntcomptBin d) (← gStr c "print_intcompt_bin")

def misc : TestM Unit := do
  let j ← readJson "oracle/golden/dendriform/misc.json"
  let t (ns : List Nat) : Tree := (Tree.ofName? ns).getD .leaf
  checkEq "[2,1,7,4,1,3,1] < [2,1,7,4,3,2,1]"
    (Tree.tamariLt (t [2, 1, 7, 4, 1, 3, 1]) (t [2, 1, 7, 4, 3, 2, 1])) (← gBool j "lt7")
  checkEq "TreeRational([1,3,1])" (fmtRat (t [1, 3, 1]).treeRational) (← gStr j "treerational_131")
  checkEq "groveindex([1,2,3] ∪ [3,2,1])"
    (Grove.union (Grove.ofIndex 3 1) (Grove.ofIndex 3 16)).index (← gNat j "groveindex_union")
  let big := Grove.ofIndex 5 1000 + Grove.ofIndex 3 7
  checkEq "Grove(5,1000) + Grove(3,7)" (showGrove ⟨8, big⟩) (← showGolden (← jField j "big_sum"))
  checkEq "Grove(8, groveindex(…)) == …" (decide (Grove.Equiv (Grove.ofIndex 8 big.index) big))
    (← gBool j "big_sum_eq")
  checkEq "CnInv" ((List.range 10).map fun d => (catalanInv? (catalan (d + 1))).getD 0).toArray
    (← gNats j "catalan_inv")

def compositions : TestM Unit := do
  for d in [1, 2, 3, 4] do
    let j ← readJson s!"oracle/golden/dendriform/compositions_{d}.json"
    for c in ← gArr j "cases" do
      let ind ← gNat c "ind"
      let (text, n) := groveComposition d ind
      checkEq s!"grovecomposition({d}, {ind})" text (← gStr c "text")
      checkEq s!"grovecomposition({d}, {ind}) count" n (← gNat c "count")

/-! ## Randomized checks of the proven identities on concrete groves -/

def randomGrove (g : Tests.Rng) (d : Nat) : Grove d × Tests.Rng :=
  let (s, g) := g.nat (2 ^ catalan d - 1)
  (Grove.ofIndex d (s + 1), g)

/-- Multiset equality by sorting (with the derived `Ord` on trees): `O(n log n)`,
equivalent to `Grove.Equiv` (which is `List.Perm`). -/
def sameRows {a b : Nat} (x : Grove a) (y : Grove b) : Bool :=
  let le (s t : Tree) : Bool := compare s t != Ordering.gt
  x.rows.length == y.rows.length && x.rows.mergeSort le == y.rows.mergeSort le

def properties : TestM Unit := do
  let mut rng := Tests.Rng.ofSeed 0x5EED
  for _ in [0:60] do
    let (a, r) := rng.nat 3; rng := r
    let (b, r) := rng.nat 3; rng := r
    let (c, r) := rng.nat 2; rng := r
    let (x, r) := randomGrove rng (a + 1); rng := r
    let (y, r) := randomGrove rng (b + 1); rng := r
    let (z, r) := randomGrove rng (c + 1); rng := r
    let lbl := s!"{x.rows.map Tree.name} {y.rows.map Tree.name} {z.rows.map Tree.name}"
    check s!"(x⊣y)⊣z ≅ x⊣(y+z) {lbl}" (sameRows (Grove.dashv (Grove.dashv x y) z)
      (Grove.dashv x (y + z)))
    check s!"(x⊢y)⊣z ≅ x⊢(y⊣z) {lbl}" (sameRows (Grove.dashv (Grove.vdash x y) z)
      (Grove.vdash x (Grove.dashv y z)))
    check s!"(x+y)⊢z ≅ x⊢(y⊢z) {lbl}" (sameRows (Grove.vdash (x + y) z)
      (Grove.vdash x (Grove.vdash y z)))
    check s!"(x+y)+z ≅ x+(y+z) {lbl}" (sameRows ((x + y) + z) (x + (y + z)))
    check s!"σ(x+y) ≅ σy+σx {lbl}" (sameRows (x + y).σ (y.σ + x.σ))
    if (a + 1) * (b + 1) ≤ 6 then
      -- σ is multiplicative (DF test/runtests.jl:56): observed, not proven
      check s!"σ(x*y) ≅ σx*σy {lbl}" (sameRows (x * y).σ (x.σ * y.σ))
      check s!"deg(x*y) {lbl}" ((x * y).rows.all (·.deg == (a + 1) * (b + 1)))
    if (a + b + 2) * (c + 1) ≤ 6 then
      -- the product distributes over + on the left (Loday): observed
      check s!"(x+y)*z ≅ x*z+y*z {lbl}" (sameRows ((x + y) * z) (x * z + y * z))
  -- Loday: Y_p + Y_q = Y_{p+q} and Y_p * Y_q = Y_{pq}, as multisets
  for p in [1, 2, 3, 4] do
    for q in [1, 2, 3] do
      check s!"Y{p} + Y{q} ≅ Y{p+q}" (sameRows (Grove.total p + Grove.total q) (Grove.total (p + q)))
      if p * q ≤ 8 then
        check s!"Y{p} * Y{q} ≅ Y{p*q}" (sameRows (Grove.total p * Grove.total q)
          (Grove.total (p * q)))

/-- The remaining conversions of DF/morphism.jl, against the port-notes §6.4 examples. -/
def extras : TestM Unit := do
  for d in [1, 2, 3, 4, 5] do
    let Y := totalGrove d
    check s!"TreeLoday∘TreeBase = id (Y{d})" (Y.trees.all fun t => Tree.ofMu? t.mu == some t)
    check s!"treeindex(d, TI) (Y{d})" ((List.range Y.tis.size).all fun i =>
      treeIndexOfInteger d Y.tis[i]! == i + 1)
    checkEq s!"GroveError(Y{d})" (groveError Y.trees.toList) (List.replicate Y.trees.size 0)
    check s!"GroveError(reversed Y{d}) ≠ 0" (d == 1 || groveError Y.trees.toList.reverse
      != List.replicate Y.trees.size 0)
  -- `TreeBase([1,2,3]).μ = [[3],[2],[1]]`, `grovebit(Grove(3,5)) = [1,0,1,0,0]`
  checkEq "TreeBase([1,2,3])" ((Tree.ofName? [1, 2, 3]).map Tree.mu) (some [[3], [2], [1]])
  checkEq "Grove(BitVector [1,0,1,0,0])"
    ((SomeGrove.ofBits? [true, false, true, false, false]).map showGrove)
    (some (showGrove ⟨3, Grove.ofIndex 3 5⟩))
  checkEq "Grove(3,1) < Grove(3,2)" ((Grove.ofIndex 3 1).indexLt (Grove.ofIndex 3 2)) true
  checkEq "treeindex([2,1,3])" ((Tree.ofName? [2, 1, 3]).map Tree.treeIndex) (some 2)
  checkEq "PBTree(3,2)" ((treeOfIndex? 3 2).map Tree.name) (some [2, 1, 3])
  checkEq "invalid name" (Tree.ofName? [1, 1, 3]).isNone true

/-- Suite entry point for the `lake test` driver. -/
def run : IO (Nat × Nat) := runSuite "Dendriform" do
  totalgroves; treeOps; poset; groveOps; degenerate; display; float16; intervalTools; misc
  compositions; properties; extras

end Tests.Dendriform
