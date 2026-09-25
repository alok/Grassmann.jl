import Tests.Fatou.Harness

/-!
Grid sizes and pixel coordinates against `oracle/golden/fatou/grids.json`
(port-notes/fatou.md G2, G3): the README and wiki rectangles, 250 random ones (decimal
bounds, `kπ/d` bounds, random floats, bounds touching 0) and constructed half-way ties in
the row count. Axes must agree bit for bit, including the `im*y` re-canonicalization.
-/

namespace Tests.Fatou.Grid

open _root_.Fatou Tests.Fatou

/-- Run the suite. -/
def run : TestM Unit := do
  let j ← readJson "grids.json"
  let cases ← gArr j "cases"
  for c in cases do
    let b ← gFs c "bounds"
    let n ← gNat c "n"
    let r : Rectangle := { bounds := ⟨b[0]!, b[1]!, b[2]!, b[3]!⟩, n }
    let lbl := s!"{b} n={n}"
    checkEq s!"rows {lbl}" r.rows (← gNat c "rows")
    checkEq s!"cols {lbl}" r.cols (← gNat c "cols")
    checkEq s!"x axis {lbl}" (fnv1a (floatBytes r.xs)) (← gStr c "fnvx")
    checkEq s!"y axis {lbl}" (fnv1a (floatBytes r.ys)) (← gStr c "fnvy")
    if let .ok gx := c.getObjVal? "gx" then
      let gx ← (← arr gx).mapM (fun x => (hexF x : IO Float))
      let gy ← gFs c "gy"
      check s!"x values {lbl}" (r.xs.toList.zip gx.toList |>.all fun (a, e) => sameF a e)
      check s!"y values {lbl}" (r.ys.toList.zip gy.toList |>.all fun (a, e) => sameF a e)
      -- the materialized grid is the separable product of the axes
      let G := r.grid
      check s!"grid {lbl}" ((List.range (r.rows * r.cols)).all fun i =>
        sameF G.re[i]! gx[i % r.cols]! && sameF G.im[i]! gy[i / r.cols]!)
  -- Julia's argument checks
  checkEq "check ok" (({ bounds := .default } : Rectangle).check.toOption.isSome) true
  checkEq "check reversed" (({ bounds := ⟨1, -1, -1, 1⟩ } : Rectangle).check.toOption.isSome) false
  checkEq "check n" (({ n := 70000 } : Rectangle).check.toOption.isSome) false
  note s!"grids: {cases.size} rectangles"

end Tests.Fatou.Grid
