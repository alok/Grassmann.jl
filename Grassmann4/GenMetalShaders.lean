/-
  GenMetalShaders.lean - Executable to generate Metal shaders

  Run with: lake exe genmetalshaders
-/
import Grassmann.MetalCodegen
import Grassmann.Blade  -- for R3

open Grassmann Grassmann.Metal in
def main : IO Unit := do
  -- Generate R3 shader
  let r3Shader := generateMetalShader R3 "R3"
  IO.FS.writeFile "r3_grassmann.metal" r3Shader
  IO.println "Generated r3_grassmann.metal"

  -- Generate Swift runner
  let r3Swift := generateSwiftRunner "R3" 3
  IO.FS.writeFile "r3_grassmann_runner.swift" r3Swift
  IO.println "Generated r3_grassmann_runner.swift"

  IO.println "Done! Files written to current directory."
