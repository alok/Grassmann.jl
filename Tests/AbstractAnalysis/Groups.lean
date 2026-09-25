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
  checkEq s!"{tag}.isGroupHashed" (Semimagma.isGroupHashed H) (jBool (jGet r "isgroup"))
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
    checkEq s!"groupHashed([{p.toList}])" (lists (Semimagma.groupHashed (L := Perm.law 4) #[p]))
      (jPermLists (jGet e "group"))
  for e in jArr (jGet j "magma2") do
    let p : Perm 4 := jPerm 4 (jGet e "p")
    let q : Perm 4 := jPerm 4 (jGet e "q")
    checkEq s!"magma([{p.toList},{q.toList}])" (lists (Semimagma.magma (L := Perm.law 4) ⟨#[p, q]⟩))
      (jPermLists (jGet e "magma"))
    checkEq s!"magmaHashed([{p.toList},{q.toList}])"
      (lists (Semimagma.magmaHashed (L := Perm.law 4) ⟨#[p, q]⟩)) (jPermLists (jGet e "magma"))
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
    checkEq s!"groupHashed([{g}], +mod {n})"
      (Semimagma.groupHashed (L := ⟨fun a b => (a + b) % n, fun a => (-a) % n⟩) #[g]).v.toList
      (jInts (jGet e "group")).toList
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
  -- parity, decompose, orders (P2)
  let pj := jGet j "parity"
  for e in jArr (jGet pj "decompose") do
    let p := jPerm 4 (jGet e "p")
    checkEq s!"decompose({p.toList})" (decomposeRepr p.decompose) (jStr (jGet e "show"))
    -- the pieces multiply back to `p`
    let back := match p.decompose with
      | .inl c => c.toPerm
      | .inr c => c.toPerm
    checkEq s!"decompose({p.toList}) recomposes" back.toList p.toList
  let S3 := SymmetricGroup 3
  let S4 := SymmetricGroup 4
  let odd4 : Semimagma (Perm 4) (Perm.law 4) := ⟨S4.v.filter Perm.isOdd⟩
  let ev := jGet pj "iseven"
  checkEq "iseven(S3)" (Semimagma.isEven S3) (jBool (jGet ev "S3"))
  checkEq "iseven(A3)" (Semimagma.isEven (AlternatingGroup 3)) (jBool (jGet ev "A3"))
  checkEq "iseven(A4)" (Semimagma.isEven (AlternatingGroup 4)) (jBool (jGet ev "A4"))
  checkEq "iseven(odd4)" (Semimagma.isEven odd4) (jBool (jGet ev "odd4"))
  let od := jGet pj "isodd"
  checkEq "isodd(S3)" (Semimagma.isOdd S3) (jBool (jGet od "S3"))
  checkEq "isodd(A4)" (Semimagma.isOdd (AlternatingGroup 4)) (jBool (jGet od "A4"))
  checkEq "isodd(odd4)" (Semimagma.isOdd odd4) (jBool (jGet od "odd4"))
  checkEq "isodd(cycles)" [(Cycle.ofList [1, 2] : Cycle 4).isOdd, (Cycle.ofList [1, 2, 3] : Cycle 4).isOdd,
      (Cycle.ofList [1, 2, 3, 4] : Cycle 4).isOdd]
    ((jArr (jGet pj "cycle_isodd")).toList.map jBool)
  for e in jArr (jGet pj "zorders") do
    let n := jInt (jGet e "n")
    let g := jInt (jGet e "g")
    let G := Semimagma.group (L := ⟨fun a b => (a + b) % n, fun a => (-a) % n⟩) #[g]
    checkEq s!"orders(Z{n}⟨{g}⟩)" (Semimagma.orders G).toList (jNats (jGet e "orders")).toList
  checkEq "orders(magma(im))" (Semimagma.orders m).toList ((jNats (jGet gj "orders")).toList)
  -- `orders` on permutations (Julia throws): the cyclic subgroup orders are the lcm of cycle lengths
  checkEq "orders(S4) = groupOrder" (Semimagma.orders S4).toList (S4.v.toList.map Perm.groupOrder)
  -- commutators, Transposition, cycle commutation
  let a : Perm 4 := (Cycle.ofList [1, 2, 3] : Cycle 4).toPerm
  let b : Perm 4 := (Cycle.ofList [1, 2] : Cycle 4).toPerm
  checkEq "commutator g⁻¹h⁻¹gh" (Perm.commutator a b).toList (a⁻¹ * b⁻¹ * a * b).toList
  checkEq "commutator of commuting = 1" (Perm.commutator a (a * a)).toList [1, 2, 3, 4]
  checkEq "commutators of S4 are even" (S4.v.all fun g => S4.v.all fun h => (Perm.commutator g h).isEven) true
  checkEq "Transposition (1,2)" ((Transposition.mk? 1 2 : Option (Transposition 4)).map (·.1.toList)) (some [1, 2])
  checkEq "Transposition (1,1)" ((Transposition.mk? 1 1 : Option (Transposition 4)).isSome) false
  let c4 : Cycle 4 := Cycle.ofList [1, 2, 3, 4]
  let c4' : Cycle 4 := Cycle.ofList [1, 2, 4, 3]
  checkEq "isabelian (1234),(1243) Julia" (Julia.cycleIsAbelian c4 c4') true
  checkEq "isabelian (1234),(1243)" (Cycle.isAbelian c4 c4') false
  checkEq "isabelian (123),(132)" (Cycle.isAbelian (Cycle.ofList [1, 2, 3] : Cycle 4) (Cycle.ofList [1, 3, 2])) true
  checkEq "isabelian (12),(34)" (Cycle.isAbelian (Cycle.ofList [1, 2] : Cycle 4) (Cycle.ofList [3, 4])) true
  checkEq "CycleProduct order" (S4.v.toList.map fun p => p.cycleProductOf.transpositionCount)
    (S4.v.toList.map Perm.transpositionCount)
  checkEq "CycleProduct sign" (S4.v.toList.map fun p => p.cycleProductOf.sign) (S4.v.toList.map Perm.sign)
  -- `g * H`, `H + g` on semimagmas (plain operation)
  checkEq "2*m (HMul)" ((⟨2, 0⟩ : JuliaBase.Complex Int) * m).v.toList (gl "times2")
  checkEq "m+1 (HAdd)" (m + (⟨1, 0⟩ : JuliaBase.Complex Int)).v.toList (gl "plus1")
  -- categories
  checkEq "isCategory(S3, 1)" (Semimagma.isCategory S3 1) true
  checkEq "isGroupoid(S3)" (Semimagma.isGroupoid S3) true
  checkEq "isSemicategory(S3)" (Semimagma.isSemicategory S3) true
  -- ModsExt: residues with `==` as `gequal`
  let z7 : Semimagma (Fin 7) (Law.mulMod 6) := Semimagma.group #[3]
  checkEq "U(7) = ⟨3⟩" z7.order 6
  checkEq "U(7) is a group" (Semimagma.isGroup z7) true
  checkEq "U(7) is cyclic" (Semimagma.isCyclic z7) true
  let z12 : Semimagma (Fin 12) (Law.addMod 11) := Semimagma.group #[8]
  checkEq "Z12⟨8⟩" (z12.v.toList.map (·.1)) [8, 4, 0]
  checkEq "Z12⟨8⟩ group" (Semimagma.isGroup z12) true
  checkEq "invMod 7 3" (invMod 7 3) 5
  checkEq "invMod 12 5" (invMod 12 5) 5
  -- the hash index on a large closure: S₆ from a transposition and a 6-cycle (720 elements)
  let t6 : Perm 6 := (Cycle.ofList [1, 2] : Cycle 6).toPerm
  let r6 : Perm 6 := (Cycle.ofList [1, 2, 3, 4, 5, 6] : Cycle 6).toPerm
  let s6 := Semimagma.magmaHashed (L := Perm.law 6) ⟨#[t6, r6]⟩
  checkEq "magmaHashed(S6).order" s6.order 720
  checkEq "isGroupHashed(S5)" (Semimagma.isGroupHashed (SymmetricGroup 5)) true
  checkEq "isGroupHashed(odd4)" (Semimagma.isGroupHashed odd4) false
  checkEq "isGroupHashed(Z12⟨8⟩ ∪ {1})" (Semimagma.isGroupHashed
    (⟨#[0, 4, 8, 1]⟩ : Semimagma Int ⟨fun a b => (a + b) % 12, fun a => (-a) % 12⟩)) false
  -- a closed, inverse-complete but non-associative table: x∘y = x - y (mod 3), inverse = id
  let sub3 : Semimagma Int ⟨fun a b => (a - b) % 3, id⟩ := ⟨#[0, 1, 2]⟩
  checkEq "isGroupHashed(Z3, -)" (Semimagma.isGroupHashed sub3) (Semimagma.isGroup sub3)
  checkEq "isGroup(Z3, -) = false" (Semimagma.isGroup sub3) false
  checkEq "magmaHashed(S6) = SymmetricGroup 6 (as sets)"
    ((Semimagma.subset s6 (SymmetricGroup 6)) && (Semimagma.subset (SymmetricGroup 6) s6)) true
  let s5 := Semimagma.magma (L := Perm.law 5) ⟨#[(Cycle.ofList [1, 2] : Cycle 5).toPerm,
    (Cycle.ofList [1, 2, 3, 4, 5] : Cycle 5).toPerm]⟩
  checkEq "magmaHashed(S5) = magma(S5) (same order)" (lists (Semimagma.magmaHashed (L := Perm.law 5)
    ⟨#[(Cycle.ofList [1, 2] : Cycle 5).toPerm, (Cycle.ofList [1, 2, 3, 4, 5] : Cycle 5).toPerm]⟩))
    (lists s5)
  checkEq "invMod units of 30" ((List.range 30).filter (Nat.gcd · 30 == 1) |>.all fun a => a * invMod 30 a % 30 == 1) true

end Tests.AbstractAnalysis.Groups
