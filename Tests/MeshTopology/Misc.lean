import Tests.MeshTopology.Util

/-!
Goldens of `misc.json` (CrossRange, simplex numbers, the Leibniz/Grassmann combinatorics,
Float range resampling) and `product.json` (ProductTopology).
-/

open Lean MeshTopology Tests.Small JuliaBase

namespace Tests.MeshTopology.Misc

/-- The float-range inputs of `resample_ranges`, by case name. -/
def resampleCase : String → Option FloatRange
  | "OneTo(5),9" => some ((AxisMap.oneTo 5).resampleFloat 9)
  | "2:6,5" => some ((AxisMap.unitRange 2 6).resampleFloat 5)
  | "1:2:9,3" => some ((AxisMap.stepRange' 1 2 9).resampleFloat 3)
  | "9:-2:1,7" => some ((AxisMap.stepRange' 9 (-2) 1).resampleFloat 7)
  | "LinRange(0,1,5),9" => some ((FloatRange.lin (LinRange.mk' 0 1 5)).resample 9)
  | "LinRange(-pi,pi,7),13" =>
    let pi := 3.141592653589793
    some ((FloatRange.lin (LinRange.mk' (-pi) pi 7)).resample 13)
  | "0.0:0.1:1.0,21" => some ((FloatRange.stepLen (colon 0.0 0.1 1.0)).resample 21)
  | "0.0:0.1:1.0,4" => some ((FloatRange.stepLen (colon 0.0 0.1 1.0)).resample 4)
  | "range(0,2pi,length=7),13" =>
    some ((FloatRange.stepLen (range 0 (2 * 3.141592653589793) 7)).resample 13)
  | "range(-1,1,length=5),(9,)" => some ((FloatRange.stepLen (rangeInt (-1) 1 5)).resample 9)
  | "[1.0,2.0,4.0],5" => some (resampleVector (FloatArray.mk #[1.0, 2.0, 4.0]) 5)
  | "[1.0,2.0,4.0]" => some (resampleVector (FloatArray.mk #[1.0, 2.0, 4.0]))
  | "[0.5,-3.0],(4,)" => some (resampleVector (FloatArray.mk #[0.5, -3.0]) 4)
  | "1:5,(9,)" => some ((AxisMap.unitRange 1 5).resampleFloat 9)
  | _ => none

/-- Run `misc.json`. -/
def misc : TestM Unit := do
  let j ← readJson "oracle/golden/meshtopology/misc.json"
  for c in ← gArr j "crossrange" do
    let n ← gNat c "n"
    checkJ s!"crossrange({n})" (jnat (crossShift n)) (← jField c "m")
    checkJ s!"CrossRange({n})" (jints (AxisMap.cross n).toArray) (← jField c "vals")
  for c in ← gArr j "simplexnumber" do
    let N ← gNat c "N"
    let n ← gNat c "n"
    checkJ s!"simplexnumber({N},{n})" (jnat (simplexNumber N n)) (← jField c "out")
  for c in ← gArr j "lagrange_counts" do
    let N ← gNat c "N"
    let M ← gNat c "M"
    checkJ s!"lagrangesimplex({N},{M})" (jnat (lagrangeSimplex N M)) (← jField c "lagrangesimplex")
    checkJ s!"centersimplex({N},{M})" (jnat (centerSimplex N M)) (← jField c "centersimplex")
    checkJ s!"facetsimplex({N},{M})" (jnat (facetSimplex N M)) (← jField c "facetsimplex")
    checkJ s!"edgesimplex({N},{M})" (jnat (edgeSimplex N M)) (← jField c "edgesimplex")
  for c in ← gArr j "indexparity" do
    let v ← intsOf (← jField c "in")
    let (odd, s) := indexParity v
    checkJ s!"indexparity!({v})" (Json.arr #[jbool odd, jints s])
      (Json.arr #[← jField c "odd", ← jField c "sorted"])
  for c in ← gArr j "combinations" do
    let v ← natsOf (← jField c "v")
    let k ← gNat c "k"
    checkJ s!"combinations({v},{k})" (Json.arr ((combinations v k).map jnats)) (← jField c "out")
  for c in ← gArr j "combo" do
    let n ← gNat c "n"
    let g ← gNat c "g"
    checkJ s!"combo({n},{g})" (Json.arr ((combo n g).map jnats)) (← jField c "out")
  for c in ← gArr j "boundary" do
    let M ← gNat c "M"
    checkJ s!"∂({M})" (jints (boundarySigns M)) (← jField c "out")
  for c in ← gArr j "resample_ranges" do
    let name ← gStr c "case"
    let out ← jField c "out"
    match resampleCase name with
    | none => check s!"resample {name}" false
    | some r =>
      checkJ s!"resample {name} type" (jstr r.typeName) (← jField out "type")
      let bits := r.toFloatArray.toList.map fun x => jstr (toString x.toBits.toNat)
      checkJ s!"resample {name}" (Json.arr bits.toArray) (← jField out "bits")

/-- A product topology of runtime dimension. -/
structure SomeProduct where
  /-- Dimension. -/
  N : Nat
  /-- The product. -/
  p : ProductTopology N

/-- The products of `product.json`, by name. -/
def productCase : String → Option SomeProduct
  | "PT(3,4)" => some ⟨2, .ofSizes #v[3, 4]⟩
  | "PT(5)" => some ⟨1, .ofSizes #v[5]⟩
  | "PT(1:3,2:5)" => some ⟨2, .ofAxes #v[.unitRange 1 3, .unitRange 2 5]⟩
  | "PT(5:-1:1,CR(5))" => some ⟨2, .ofAxes #v[.stepRange' 5 (-1) 1, .cross 5]⟩
  | "PT(1:1:4)" => some ⟨1, .single (.stepRange' 1 1 4)⟩
  | "PT(CR(6))" => some ⟨1, .single (.cross 6)⟩
  | "PT([3,1,2],[5,4])" => some ⟨2, .ofAxes #v[.vec #[3, 1, 2], .vec #[5, 4]]⟩
  | "PT(2,3,4)" => some ⟨3, .ofSizes #v[2, 3, 4]⟩
  | "PT(2,3,2,3)" => some ⟨4, .ofSizes #v[2, 3, 2, 3]⟩
  | "PT(2,2,3,2,2)" => some ⟨5, .ofSizes #v[2, 2, 3, 2, 2]⟩
  | "[1,1]:[3,4]" => some ⟨2, .colon #v[1, 1] #v[3, 4]⟩
  | "[1,1]:[1,2]:[3,6]" => some ⟨2, .colonStep #v[1, 1] #v[1, 2] #v[3, 6]⟩
  | "[2,4,1]:[3,5,2]" => some ⟨3, .colon #v[2, 4, 1] #v[3, 5, 2]⟩
  | "PT(3,4)×PT(5)" => some ⟨3, (ProductTopology.ofSizes #v[3, 4]).cross (.ofSizes #v[5])⟩
  | "PT(3,4)×[7,8]" => some ⟨3, (ProductTopology.ofSizes #v[3, 4]).crossAxis (.vec #[7, 8])⟩
  | "[7,8]×PT(3)" => some ⟨2, ProductTopology.axisCross (.vec #[7, 8]) (.ofSizes #v[3])⟩
  | "PT(3)×4" => some ⟨2, (ProductTopology.ofSizes #v[3]).crossAxis (.oneTo 4)⟩
  | "4×PT(2,3)" => some ⟨3, ProductTopology.axisCross (.oneTo 4) (.ofSizes #v[2, 3])⟩
  | _ => none

/-- Run `product.json`. -/
def product : TestM Unit := do
  let j ← readJson "oracle/golden/meshtopology/product.json"
  for c in ← gArr j "products" do
    let name ← gStr c "name"
    let some ⟨N, p⟩ := productCase name | check s!"product {name}" false; continue
    checkJ s!"{name} axes" (jproduct p) (← jField c "axes")
    checkJ s!"{name} size" (jvecN p.size) (← jField c "size")
    checkJ s!"{name} collect" (jgrid p.size.toList (p.toArray.map jvec)) (← jField c "collect")
    checkJ s!"{name} linear" (jvecs ((Array.range p.length).map fun k => p.getLinear (k + 1)))
      (← jField c "linear")
    checkJ s!"{name} summary" (jstr p.summary) (← jField c "summary")
    checkJ s!"{name} show" (jstr p.showString) (← jField c "show")
    if 1 ≤ N then
      checkOptJ s!"{name} resize" ((p.resize? 7).map jproduct) (← jField c "resize")
      checkOptJ s!"{name} resample" ((p.resample? (p.size.map (· + 2))).map jproduct)
        (← jField c "resample")
      let ex1 ← gArr c "exclude1"
      for h : k in [0:N] do
        checkJ s!"{name} exclude {k + 1}" (jproduct (p.exclude ⟨k, h.2.1⟩)) ex1[k]!
    for key in ["exclude2", "exclude3"] do
      if let .ok ex := c.getObjVal? key then
        for e in ← jArr ex do
          let axes ← natsOf (← jField e "ex")
          let ⟨_, q⟩ := p.excludeMany axes.toList
          checkJ s!"{name} exclude {axes}" (jproduct q) (← jField e "out")
    checkJ s!"{name} QuotientTopology" (jquotient (QuotientTopology.ofProduct p)) (← jField c "quotient")
  let e ← jField j "empty"
  checkJ "ProductTopology() summary" (jstr ProductTopology.empty.summary) (← jField e "summary")
  checkJ "ProductTopology() size" (jvecN ProductTopology.empty.size) (← jField e "size")

/-- Run both files. -/
def run : TestM Unit := do
  misc
  product

end Tests.MeshTopology.Misc
