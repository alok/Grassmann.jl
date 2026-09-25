import AbstractAnalysis
import Tests.AbstractAnalysis.Harness

/-!
Oracle tests for semimagmas, permutation groups and their Julia quirks
(`oracle/golden/abstractanalysis/groups.json`).
-/

open Lean AbstractAnalysis JuliaBase Tests.Golden

namespace Tests.AbstractAnalysis.Groups

/-- A golden permutation of `1..N`. -/
def jPerm (N : Nat) (j : Json) : Perm N := Perm.ofList! ((jNats j).toList)

/-- Golden list of permutations as 1-based image lists. -/
def jPermLists (j : Json) : List (List Nat) := (jArr j).toList.map fun p => (jNats p).toList

/-- A semimagma's elements as image lists. -/
def lists {N : Nat} {L : Law (Perm N)} (G : Semimagma (Perm N) L) : List (List Nat) := G.v.toList.map Perm.toList

/-- Checks on the subgroup-dependent operations for groups inside `S_N`. -/
def subgroupCase (N : Nat) (i : Nat) (r : Json) : TestM Unit := do
  let G := SymmetricGroup N
  let H : Semimagma (Perm N) (Perm.law N) := ⟨(jArr (jGet r "H")).map (jPerm N)⟩
  let tag := s!"S{N}.sub{i}"
  checkEq s!"{tag}.center(Julia)" (lists (Julia.center H)) (jPermLists (jGet r "center"))
  checkEq s!"{tag}.centralizer" (lists (Semimagma.centralizer H G)) (jPermLists (jGet r "centralizer"))
  checkEq s!"{tag}.normalizer" (lists (Semimagma.normalizer H G)) (jPermLists (jGet r "normalizer"))
  checkEq s!"{tag}.isnormal" (Semimagma.isNormal H G) (jBool (jGet r "isnormal"))
  checkEq s!"{tag}.issubgroup" (Semimagma.isSubgroup H G) (jBool (jGet r "issubgroup"))
  checkEq s!"{tag}.isabelian" (Semimagma.isAbelian H) (jBool (jGet r "isabelian"))
  checkEq s!"{tag}.isgroup" (Semimagma.isGroup H) (jBool (jGet r "isgroup"))
  checkEq s!"{tag}.commutator" (lists (Semimagma.commutator H H)) (jPermLists (jGet r "commutator"))
  checkEq s!"{tag}.leftcosets(Julia)" ((Julia.leftCosets H G).toList.map lists)
    ((jArr (jGet r "leftcosets")).toList.map jPermLists)
  checkEq s!"{tag}.rightcosets(Julia)" ((Julia.rightCosets H G).toList.map lists)
    ((jArr (jGet r "rightcosets")).toList.map jPermLists)
  checkEq s!"{tag}.subgroup" (lists (Semimagma.subgroup H)) (jPermLists (jGet r "subgroup"))
  -- clean API: the set-deduplicated cosets partition G into |G|/|H| blocks
  let cosets := Semimagma.leftCosets H G
  check s!"{tag}.cosets partition" (Semimagma.isGroup H == false ||
    cosets.size * H.v.toList.eraseDups.length == G.v.size)

/-- Julia `Complex{Int}` as `[re, im]`. -/
def jGauss (j : Json) : Complex Int := let a := jArr j; ⟨jInt a[0]!, jInt a[1]!⟩

instance : ToString (Complex Int) := ⟨JuliaRepr.repr⟩

/-- The suite. -/
def suite : TestM Unit := do
  let j ← loadJson "oracle/golden/abstractanalysis/groups.json"
  let sym := jGet j "symmetric"
  checkEq "S1" (lists (SymmetricGroup 1)) (jPermLists (jGet sym "1"))
  checkEq "S2" (lists (SymmetricGroup 2)) (jPermLists (jGet sym "2"))
  checkEq "S3" (lists (SymmetricGroup 3)) (jPermLists (jGet sym "3"))
  checkEq "S4" (lists (SymmetricGroup 4)) (jPermLists (jGet sym "4"))
  let alt := jGet j "alternating"
  checkEq "A3" (lists (AlternatingGroup 3)) (jPermLists (jGet alt "3"))
  checkEq "A4" (lists (AlternatingGroup 4)) (jPermLists (jGet alt "4"))
  -- elementwise: inverse, powers, cycles, transposition count, sign
  for e in jArr (jGet j "elements") do
    let l := (jNats (jGet e "p")).toList
    let go {N : Nat} (p : Perm N) : TestM Unit := do
      let tag := s!"{l}"
      checkEq s!"{tag}.inv" p⁻¹.toList (jNats (jGet e "inv")).toList
      for k in [-3, -2, -1, 0, 1, 2, 3] do
        checkEq s!"{tag}^{k}" (p ^ (k : Int)).toList (jNats (jGet (jGet e "pow") (toString k))).toList
      checkEq s!"{tag}.cycles" (p.cycles.map (·.map (·.1 + 1))) ((jArr (jGet e "cycles")).toList.map fun c => (jNats c).toList)
      checkEq s!"{tag}.order" p.transpositionCount (jNat (jGet e "order"))
      checkEq s!"{tag}.levicivita" p.sign (jInt (jGet e "levicivita"))
      checkEq s!"{tag}.iseven" p.isEven (jBool (jGet e "iseven"))
    if l.length == 3 then go (Perm.ofList! l : Perm 3) else go (Perm.ofList! l : Perm 4)
  -- all pairs in S3 and S4: *, /, \
  for e in jArr (jGet j "pairs") do
    let lp := (jNats (jGet e "p")).toList
    let lq := (jNats (jGet e "q")).toList
    let go {N : Nat} (p q : Perm N) : TestM Unit := do
      checkEq s!"{lp}*{lq}" (p * q).toList (jNats (jGet e "mul")).toList
      checkEq s!"{lp}/{lq}" (p.div q).toList (jNats (jGet e "div")).toList
      checkEq s!"{lp}\\{lq}" (p.ldiv q).toList (jNats (jGet e "ldiv")).toList
    if lp.length == 3 then go (Perm.ofList! lp : Perm 3) (Perm.ofList! lq) else go (Perm.ofList! lp : Perm 4) (Perm.ofList! lq)
  for e in jArr (jGet j "cyclic") do
    let p : Perm 4 := jPerm 4 (jGet e "p")
    checkEq s!"group([{p.toList}])" (lists (Semimagma.group (L := Perm.law 4) #[p])) (jPermLists (jGet e "group"))
  for e in jArr (jGet j "magma2") do
    let p : Perm 4 := jPerm 4 (jGet e "p")
    let q : Perm 4 := jPerm 4 (jGet e "q")
    checkEq s!"magma([{p.toList},{q.toList}])" (lists (Semimagma.magma (L := Perm.law 4) ⟨#[p, q]⟩))
      (jPermLists (jGet e "magma"))
  let mut i := 0
  for r in jArr (jGet j "subgroups") do
    i := i + 1
    let n := ((jArr (jGet r "H"))[0]? |>.map (fun p => (jArr p).size)).getD 4
    if n == 3 then subgroupCase 3 i r else subgroupCase 4 i r
  -- modular magmas and Z_n groups
  for e in jArr (jGet j "modmagmas") do
    let n := jInt (jGet e "n")
    let g := jInt (jGet e "g")
    checkEq s!"magma({g}, *mod {n})" (Semimagma.cyclic (L := ⟨fun a b => (a * b) % n, id⟩) g).v.toList
      (jInts (jGet e "magma")).toList
  for e in jArr (jGet j "zgroups") do
    let n := jInt (jGet e "n")
    let g := jInt (jGet e "g")
    let G := Semimagma.group (L := ⟨fun a b => (a + b) % n, fun a => (-a) % n⟩) #[g]
    checkEq s!"group([{g}], +mod {n})" G.v.toList (jInts (jGet e "group")).toList
    checkEq s!"iscyclic Z{n}⟨{g}⟩" (Julia.isCyclic G) (jBool (jGet e "iscyclic"))
  -- Gaussian units
  let gj := jGet j "gaussian"
  let m := Semimagma.cyclic (L := Law.gaussian) ⟨0, 1⟩
  let gl := fun (key : String) => (jArr (jGet gj key)).toList.map jGauss
  checkEq "magma(im)" m.v.toList (gl "m")
  checkEq "orders(magma(im))" (m.v.toList.map fun z => (Semimagma.cyclic (L := Law.gaussian) z).order)
    ((jNats (jGet gj "orders")).toList)
  checkEq "cayley" (m.cayley.toList.map Array.toList) ((jArr (jGet gj "cayley")).toList.map fun row => (jArr row).toList.map jGauss)
  checkEq "2*m" (Semimagma.composeLeft ⟨2, 0⟩ m (· * ·)).v.toList (gl "times2")
  checkEq "m+1" (Semimagma.composeRight m ⟨1, 0⟩ (· + ·)).v.toList (gl "plus1")
  checkEq "m*m" (Semimagma.compose m m (· * ·)).v.toList (gl "mm")
  checkEq "isgroup(m)" (Semimagma.isGroup m) (jBool (jGet gj "isgroup"))
  checkEq "isabelian(m)" (Semimagma.isAbelian m) (jBool (jGet gj "isabelian"))
  checkEq "iscyclic(m)" (Julia.isCyclic m) (jBool (jGet gj "iscyclic"))
  checkEq "subgroup(m)" (Semimagma.subgroup m).v.toList (gl "subgroup")
  -- roots of unity (Julia's own sin/cos vs libm: 2 ulps)
  for e in jArr (jGet j "unityroots") do
    let n := jNat (jGet e "n")
    let zs := jArr (jGet e "z")
    let got := (unityRoots n).v
    check s!"unityroots({n}).size" (got.size == zs.size)
    for k in [0:min got.size zs.size] do
      let z := jArr zs[k]!
      checkFloat s!"unityroots({n})[{k}].re" got[k]!.re (jFloat z[0]!) 0 2
      let im := jFloat z[1]!
      -- near-zero parts (e.g. sin(π)) are pure rounding noise: absolute tolerance
      check s!"unityroots({n})[{k}].im" ((got[k]!.im - im).abs ≤ 1e-15 + 4.5e-16 * im.abs)
  -- cycles
  let cj := jGet j "cycles"
  checkEq "Permutation(Cycle(1,3,4))" (Cycle.ofList [1, 3, 4] : Cycle 4).toPerm.toList (jNats (jGet cj "cycle134")).toList
  checkEq "CycleProduct" (cycleProduct [(Cycle.ofList [1, 2] : Cycle 4), Cycle.ofList [3, 4]]).toList
    (jNats (jGet cj "product")).toList
  checkEq "Cycle == rotation (Julia)" (Julia.cycleEq (Cycle.ofList [1, 2, 3] : Cycle 4) (Cycle.ofList [2, 3, 1]))
    (jBool (jGet cj "eq_rot"))
  checkEq "Cycle == reversal (Julia quirk)" (Julia.cycleEq (Cycle.ofList [1, 2, 3] : Cycle 4) (Cycle.ofList [1, 3, 2]))
    (jBool (jGet cj "eq_rev"))
  checkEq "isdisjoint" (Cycle.isDisjoint (Cycle.ofList [1, 2] : Cycle 4) (Cycle.ofList [3, 4])) (jBool (jGet cj "disjoint"))
  checkEq "clean Cycle equality sees orientation"
    ((Cycle.ofList [1, 2, 3] : Cycle 4).toPerm == (Cycle.ofList [1, 3, 2] : Cycle 4).toPerm) false
  checkEq "DihedralGroup" (lists (DihedralGroup (Cycle.ofList [1, 2, 3, 4] : Cycle 4).toPerm (Cycle.ofList [1, 3]).toPerm))
    (jPermLists (jGet j "dihedral"))
  -- clean API: true center, group order vs transposition count
  checkEq "center(S3)" (lists (Semimagma.center (SymmetricGroup 3))) [[1, 2, 3]]
  checkEq "center(S4)" (lists (Semimagma.center (SymmetricGroup 4))) [[1, 2, 3, 4]]
  checkEq "groupOrder (1 2 3 4)" (Cycle.ofList [1, 2, 3, 4] : Cycle 4).toPerm.groupOrder 4
  checkEq "isCyclic S3 (clean)" (Semimagma.isCyclic (SymmetricGroup 3)) false
  checkEq "isCyclic A3 (clean)" (Semimagma.isCyclic (AlternatingGroup 3)) true

end Tests.AbstractAnalysis.Groups
