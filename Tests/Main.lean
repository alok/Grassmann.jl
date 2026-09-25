import Tests

/-- A registered test suite: a name and an action returning `(passed, failed)`. -/
structure Suite where
  name : String
  run : IO (Nat × Nat)

/-- Every suite `lake test` runs. Suites read goldens relative to the repository root. -/
def suites : List Suite := [
  ⟨"JuliaBase", Tests.JuliaBase.run⟩,
  ⟨"AbstractTensors", Tests.AbstractTensors.run⟩,
  ⟨"AbstractLattices", Tests.AbstractLattices.run⟩,
  ⟨"PrimitiveBits", Tests.PrimitiveBits.run⟩,
  ⟨"DeMorgan", Tests.DeMorgan.run⟩,
  ⟨"Dendriform", Tests.Dendriform.run⟩,
  ⟨"DirectSum", Tests.DirectSum.run⟩,
  ⟨"AbstractAnalysis", Tests.AbstractAnalysis.run⟩,
  ⟨"Wilkinson", Tests.Wilkinson.run⟩,
  ⟨"FieldAlgebra", Tests.FieldAlgebra.run⟩,
  ⟨"UnitSystems", Tests.UnitSystems.run⟩,
  ⟨"Similitude", Tests.Similitude.run⟩,
  ⟨"MeasureSystems", Tests.MeasureSystems.run⟩,
  ⟨"MeshTopology", Tests.MeshTopology.run⟩,
  ⟨"Fatou", Tests.Fatou.run⟩,
  ⟨"Geophysics", Tests.Geophysics.run⟩,
  ⟨"Grassmann", Tests.Grassmann.run⟩,
  ⟨"Golden", Tests.Golden.run⟩
]

/-- Test driver: `lake test` runs everything; `lake exe tests A B` runs the named suites. -/
def main (args : List String) : IO UInt32 := do
  let chosen := if args.isEmpty then suites else suites.filter (args.contains ·.name)
  let mut totalPass := 0
  let mut totalFail := 0
  for s in chosen do
    let t0 ← IO.monoMsNow
    let (p, f) ← s.run
    let t1 ← IO.monoMsNow
    IO.println s!"[{if f == 0 then "PASS" else "FAIL"}] {s.name}: {p} passed, {f} failed ({t1 - t0} ms)"
    totalPass := totalPass + p
    totalFail := totalFail + f
  IO.println s!"TOTAL: {totalPass} passed, {totalFail} failed"
  return if totalFail == 0 then 0 else 1
