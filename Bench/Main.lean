import Bench

/-- A registered benchmark suite. `smoke` runs a tiny configuration (used by CI). -/
structure BenchSuite where
  name : String
  run : (smoke : Bool) → IO Unit

/-- Every benchmark `lake exe bench` runs. -/
def benches : List BenchSuite := [
  ⟨"math", fun smoke => Bench.Math.run smoke⟩,
  ⟨"MeshTopology", fun smoke => Tests.MeshTopology.Bench.run (smoke := smoke)⟩,
  ⟨"Fatou", fun smoke => Tests.Fatou.Bench.run (smoke := smoke)⟩
]

/-- Benchmark driver: `lake exe bench [--smoke] [suite …]`. -/
def main (args : List String) : IO UInt32 := do
  let smoke := args.contains "--smoke"
  let names := args.filter (· != "--smoke")
  let chosen := if names.isEmpty then benches else benches.filter (names.contains ·.name)
  for b in chosen do
    IO.println s!"== {b.name}"
    b.run smoke
  return 0
