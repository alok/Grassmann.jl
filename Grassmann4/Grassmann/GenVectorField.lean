/-
  Generate vector field visualizations (2D SVG and 3D HTML)

  Replicates the Grassmann.jl vector field visualization:
  - 2D: exp(π/4 * e12) rotation
  - 3D: exp(π/4 * (e12 + e23)) compound rotation (exact Grassmann.jl example)
-/
import Grassmann.Visualization

open Grassmann.Visualization

def main : IO Unit := do
  IO.println "=== Grassmann Vector Field Visualization ==="
  IO.println ""

  -- 2D Vector Field
  IO.println "Generating 2D vector field (45° rotation)..."
  let R2D := rotor2D (pi / 4)
  let svg := generateVectorFieldSVG R2D 12 1.5
  IO.FS.writeFile "vector_field_2d.svg" svg
  IO.println s!"  Wrote vector_field_2d.svg ({svg.length} bytes)"

  -- 3D Vector Field (Grassmann.jl example)
  IO.println ""
  IO.println "Generating 3D vector field..."
  IO.println "  Rotor: exp(π/4 · (e₁₂ + e₂₃))"
  IO.println "  This is the exact Grassmann.jl README example!"

  -- Test the rotor first
  let R3D := grassmannExampleRotor
  let testV := vec3 1.0 0.0 0.0
  let rotated := applyRotor3D R3D testV
  IO.println s!"  Test: e₁ → ({fmtFloat (getX3 rotated)}, {fmtFloat (getY3 rotated)}, {fmtFloat (getZ3 rotated)})"

  -- Generate 3D visualization
  let html := generateVectorField3D 10 1.5  -- 10x10x10 grid like Grassmann.jl
  IO.FS.writeFile "vector_field_3d.html" html
  IO.println s!"  Wrote vector_field_3d.html ({html.length} bytes)"

  IO.println ""
  IO.println "Done! Open the files in a browser:"
  IO.println "  - vector_field_2d.svg (2D rotation)"
  IO.println "  - vector_field_3d.html (3D interactive, drag to rotate)"
