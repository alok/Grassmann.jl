/-
  GPUPhysics.lean - Executable for GPU Physics Pipeline

  Run with: lake exe gpuphysics
-/
import Grassmann.GPUPhysicsPipeline

open Grassmann.GPUPhysicsPipeline

def main (args : List String) : IO Unit := do
  IO.println "Grassmann GPU Physics Pipeline Generator"
  IO.println "========================================"
  IO.println ""

  let outputDir := args.head?.getD "."

  -- Generate all files
  generateGPUPhysicsPipeline outputDir

  IO.println ""
  IO.println "Running CPU benchmark..."
  runBenchmark

  IO.println ""
  IO.println "To run GPU physics with Unreal MCP visualization:"
  IO.println "  1. Start Unreal Engine with MCP plugin"
  IO.println "  2. Spawn 4 actors named Ball_0, Ball_1, Ball_2, Ball_3"
  IO.println "  3. Run: swift physics_runner.swift"
  IO.println ""
  IO.println "The simulation will stream positions to Unreal at 60fps!"
