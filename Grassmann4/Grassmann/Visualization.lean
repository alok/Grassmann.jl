/-
  Grassmann/Visualization.lean - Vector Field Visualization

  Replicates Grassmann.jl's vectorfield visualization:
  - Compute how a rotor transforms vectors across a 2D grid
  - Output SVG for visualization

  Usage:
    #eval generateVectorFieldSVG (expBivector bivector) gridSize range
-/
import Grassmann.SparseMultivector
import Grassmann.RotorExp
import Grassmann.PrettyPrint

namespace Grassmann.Visualization

open Grassmann

/-- Pi constant for rotations -/
def pi : Float := 3.14159265358979323846

/-! ## Vector Field Computation -/

/-- A 2D point with its transformed vector -/
structure VectorAtPoint where
  x : Float      -- Original x position
  y : Float      -- Original y position
  vx : Float     -- Transformed vector x component
  vy : Float     -- Transformed vector y component
  deriving Repr

/-- Create a 2D vector from coordinates in R2 -/
def vec2 (x y : Float) : MultivectorS (Signature.euclidean 2) Float :=
  let e1 : MultivectorS (Signature.euclidean 2) Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS (Signature.euclidean 2) Float := MultivectorS.basis ⟨1, by omega⟩
  e1.smul x + e2.smul y

/-- Extract x component (e1 coefficient) from a 2D multivector -/
def getX (v : MultivectorS (Signature.euclidean 2) Float) : Float :=
  v.coeff 1  -- e1 has bitmask 1

/-- Extract y component (e2 coefficient) from a 2D multivector -/
def getY (v : MultivectorS (Signature.euclidean 2) Float) : Float :=
  v.coeff 2  -- e2 has bitmask 2

/-- Apply rotor transformation: R * v * R† -/
def applyRotor (R v : MultivectorS (Signature.euclidean 2) Float) :
    MultivectorS (Signature.euclidean 2) Float :=
  R * v * R†ₛ

/-- Compute vector field: for each grid point, compute the transformed vector direction -/
def computeVectorField (R : MultivectorS (Signature.euclidean 2) Float)
    (gridSize : Nat) (range : Float) : List VectorAtPoint :=
  let step := 2 * range / gridSize.toFloat
  let start := -range
  let points := (List.range gridSize).flatMap fun i =>
    (List.range gridSize).map fun j =>
      let x := start + i.toFloat * step + step / 2
      let y := start + j.toFloat * step + step / 2
      let v := vec2 x y
      let transformed := applyRotor R v
      -- The vector field shows the *difference* (how the rotor moves the vector)
      let vx := getX transformed - x
      let vy := getY transformed - y
      { x := x, y := y, vx := vx, vy := vy : VectorAtPoint }
  points

/-! ## SVG Generation -/

/-- Format a float for SVG (limited precision) -/
def fmtFloat (x : Float) : String :=
  -- Simple formatting: multiply by 100, round, divide by 100
  let scaled := (x * 100).round / 100
  toString scaled

/-- Generate SVG arrow for a vector at a point -/
def svgArrow (p : VectorAtPoint) (scale : Float) (viewScale : Float) : String :=
  let cx := (p.x + 1.5) * viewScale  -- Shift to positive coordinates
  let cy := (1.5 - p.y) * viewScale  -- Flip y for SVG coordinates
  let mag := Float.sqrt (p.vx * p.vx + p.vy * p.vy)
  if mag < 0.001 then ""
  else
    let dx := p.vx / mag * scale
    let dy := -p.vy / mag * scale  -- Flip y
    let x2 := cx + dx
    let y2 := cy + dy
    s!"<line x1=\"{fmtFloat cx}\" y1=\"{fmtFloat cy}\" x2=\"{fmtFloat x2}\" y2=\"{fmtFloat y2}\" stroke=\"blue\" stroke-width=\"1\" marker-end=\"url(#arrow)\"/>\n"

/-- Generate complete SVG for vector field -/
def generateSVG (points : List VectorAtPoint) (width height : Nat) : String :=
  let viewScale := width.toFloat / 3.0  -- Map [-1.5, 1.5] to [0, width]
  let arrowScale := 15.0  -- Arrow length in pixels
  let arrows := String.join (points.map fun p => svgArrow p arrowScale viewScale)
  s!"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" viewBox=\"0 0 {width} {height}\">
  <defs>
    <marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"10\" refX=\"9\" refY=\"3\" orient=\"auto\" markerUnits=\"strokeWidth\">
      <path d=\"M0,0 L0,6 L9,3 z\" fill=\"blue\" />
    </marker>
  </defs>
  <rect width=\"100%\" height=\"100%\" fill=\"white\"/>
  <text x=\"10\" y=\"20\" font-family=\"monospace\" font-size=\"12\">Rotor Vector Field</text>
{arrows}</svg>"

/-! ## Main API -/

/-- Generate SVG for a rotor's vector field
    Example: generateVectorFieldSVG (expBivector B) 15 1.5 -/
def generateVectorFieldSVG (R : MultivectorS (Signature.euclidean 2) Float)
    (gridSize : Nat := 12) (range : Float := 1.5) : String :=
  let points := computeVectorField R gridSize range
  generateSVG points 400 400

/-! ## Convenience: Create Rotors -/

/-- Create a 2D rotor from angle (in radians) -/
def rotor2D (angle : Float) : MultivectorS (Signature.euclidean 2) Float :=
  let e1 : MultivectorS (Signature.euclidean 2) Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS (Signature.euclidean 2) Float := MultivectorS.basis ⟨1, by omega⟩
  let B := e1 * e2  -- Bivector e12
  expBivector (B.smul (angle / 2))

/-! ## 3D Vector Field (Replicating Grassmann.jl example) -/

/-- A 3D point with its transformed vector -/
structure Vector3AtPoint where
  x : Float
  y : Float
  z : Float
  vx : Float
  vy : Float
  vz : Float
  deriving Repr

/-- R3 signature for 3D Euclidean space -/
abbrev R3Viz : Signature 3 := Signature.euclidean 3

/-- Create a 3D vector from coordinates -/
def vec3 (x y z : Float) : MultivectorS R3Viz Float :=
  let e1 : MultivectorS R3Viz Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R3Viz Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS R3Viz Float := MultivectorS.basis ⟨2, by omega⟩
  e1.smul x + e2.smul y + e3.smul z

/-- Extract components from 3D multivector -/
def getX3 (v : MultivectorS R3Viz Float) : Float := v.coeff 1  -- e1 = bit 0
def getY3 (v : MultivectorS R3Viz Float) : Float := v.coeff 2  -- e2 = bit 1
def getZ3 (v : MultivectorS R3Viz Float) : Float := v.coeff 4  -- e3 = bit 2

/-- Apply rotor transformation in 3D: R * v * R† -/
def applyRotor3D (R v : MultivectorS R3Viz Float) : MultivectorS R3Viz Float :=
  R * v * R†ₛ

/-- Create the e12 bivector -/
def e12_3D : MultivectorS R3Viz Float :=
  let e1 : MultivectorS R3Viz Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R3Viz Float := MultivectorS.basis ⟨1, by omega⟩
  e1 * e2

/-- Create the e23 bivector -/
def e23_3D : MultivectorS R3Viz Float :=
  let e2 : MultivectorS R3Viz Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS R3Viz Float := MultivectorS.basis ⟨2, by omega⟩
  e2 * e3

/-- Create the e13 bivector -/
def e13_3D : MultivectorS R3Viz Float :=
  let e1 : MultivectorS R3Viz Float := MultivectorS.basis ⟨0, by omega⟩
  let e3 : MultivectorS R3Viz Float := MultivectorS.basis ⟨2, by omega⟩
  e1 * e3

/-- Create the Grassmann.jl example rotor: exp(π/4 * (e12 + e23))
    This rotates simultaneously in the xy-plane and yz-plane -/
def grassmannExampleRotor : MultivectorS R3Viz Float :=
  let B := e12_3D + e23_3D
  expBivector (B.smul (pi / 4))

/-- Compute 3D vector field -/
def computeVectorField3D (R : MultivectorS R3Viz Float)
    (gridSize : Nat) (range : Float) : List Vector3AtPoint :=
  let step := 2 * range / gridSize.toFloat
  let start := -range
  (List.range gridSize).flatMap fun i =>
    (List.range gridSize).flatMap fun j =>
      (List.range gridSize).map fun k =>
        let x := start + i.toFloat * step + step / 2
        let y := start + j.toFloat * step + step / 2
        let z := start + k.toFloat * step + step / 2
        let v := vec3 x y z
        let transformed := applyRotor3D R v
        -- Vector field shows displacement
        let vx := getX3 transformed - x
        let vy := getY3 transformed - y
        let vz := getZ3 transformed - z
        { x := x, y := y, z := z, vx := vx, vy := vy, vz := vz }

/-- Generate JSON for 3D vector field (for Three.js visualization) -/
def generateJSON3D (points : List Vector3AtPoint) : String :=
  let lb := "{"  -- left brace
  let rb := "}"  -- right brace
  let jsonPoints := points.map fun p =>
    s!"{lb}\"x\":{fmtFloat p.x},\"y\":{fmtFloat p.y},\"z\":{fmtFloat p.z},\"vx\":{fmtFloat p.vx},\"vy\":{fmtFloat p.vy},\"vz\":{fmtFloat p.vz}{rb}"
  "[" ++ String.intercalate ",\n" jsonPoints ++ "]"

/-- Generate complete HTML with Three.js for 3D visualization -/
def generateHTML3D (points : List Vector3AtPoint) : String :=
  let jsonData := generateJSON3D points
  let lb := "{"
  let rb := "}"
  -- Build HTML with proper brace escaping
  "<!DOCTYPE html>\n" ++
  "<html>\n" ++
  "<head>\n" ++
  "  <title>3D Vector Field - Grassmann.jl Example</title>\n" ++
  s!"  <style>body {lb} margin: 0; overflow: hidden; {rb}</style>\n" ++
  "</head>\n" ++
  "<body>\n" ++
  "<script src=\"https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js\"></script>\n" ++
  "<script src=\"https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/controls/OrbitControls.js\"></script>\n" ++
  "<script>\n" ++
  s!"const data = {jsonData};\n" ++
  "\n" ++
  "// Scene setup\n" ++
  "const scene = new THREE.Scene();\n" ++
  "scene.background = new THREE.Color(0xf0f0f0);\n" ++
  "const camera = new THREE.PerspectiveCamera(75, window.innerWidth/window.innerHeight, 0.1, 1000);\n" ++
  "camera.position.set(3, 3, 3);\n" ++
  "\n" ++
  s!"const renderer = new THREE.WebGLRenderer({lb}antialias: true{rb});\n" ++
  "renderer.setSize(window.innerWidth, window.innerHeight);\n" ++
  "document.body.appendChild(renderer.domElement);\n" ++
  "\n" ++
  "const controls = new THREE.OrbitControls(camera, renderer.domElement);\n" ++
  "\n" ++
  "// Axes helper\n" ++
  "scene.add(new THREE.AxesHelper(2));\n" ++
  "\n" ++
  "// Grid\n" ++
  "const gridHelper = new THREE.GridHelper(3, 10);\n" ++
  "scene.add(gridHelper);\n" ++
  "\n" ++
  "// Arrow material\n" ++
  s!"const arrowMaterial = new THREE.LineBasicMaterial({lb}color: 0x0066ff{rb});\n" ++
  "\n" ++
  "// Create arrows\n" ++
  s!"data.forEach(p => {lb}\n" ++
  "  const mag = Math.sqrt(p.vx*p.vx + p.vy*p.vy + p.vz*p.vz);\n" ++
  s!"  if (mag > 0.01) {lb}\n" ++
  "    const scale = 0.15;\n" ++
  "    const dir = new THREE.Vector3(p.vx, p.vy, p.vz).normalize();\n" ++
  "    const arrowHelper = new THREE.ArrowHelper(dir, new THREE.Vector3(p.x, p.y, p.z), scale, 0x0066ff, 0.05, 0.03);\n" ++
  "    scene.add(arrowHelper);\n" ++
  s!"  {rb}\n" ++
  s!"{rb});\n" ++
  "\n" ++
  "// Title\n" ++
  "const titleDiv = document.createElement('div');\n" ++
  "titleDiv.style.cssText = 'position:absolute;top:10px;left:10px;color:#333;font-family:monospace;font-size:14px;';\n" ++
  "titleDiv.innerHTML = 'Rotor: exp(π/4 · (e₁₂ + e₂₃))<br>Drag to rotate, scroll to zoom';\n" ++
  "document.body.appendChild(titleDiv);\n" ++
  "\n" ++
  "// Animation loop\n" ++
  s!"function animate() {lb}\n" ++
  "  requestAnimationFrame(animate);\n" ++
  "  controls.update();\n" ++
  "  renderer.render(scene, camera);\n" ++
  s!"{rb}\n" ++
  "animate();\n" ++
  "\n" ++
  s!"window.addEventListener('resize', () => {lb}\n" ++
  "  camera.aspect = window.innerWidth/window.innerHeight;\n" ++
  "  camera.updateProjectionMatrix();\n" ++
  "  renderer.setSize(window.innerWidth, window.innerHeight);\n" ++
  s!"{rb});\n" ++
  "</script>\n" ++
  "</body>\n" ++
  "</html>"

/-- Generate 3D vector field visualization (Grassmann.jl example)
    Rotor: exp(π/4 * (e12 + e23)) -/
def generateVectorField3D (gridSize : Nat := 10) (range : Float := 1.5) : String :=
  let R := grassmannExampleRotor
  let points := computeVectorField3D R gridSize range
  generateHTML3D points

/-! ## Tests -/

-- Test 3D vector creation
#eval! let v := vec3 1.0 2.0 3.0
       (getX3 v, getY3 v, getZ3 v)

-- Test bivector creation
#eval! e12_3D.nnz  -- Should be 1 (just e12)
#eval! e23_3D.nnz  -- Should be 1 (just e23)
#eval! (e12_3D + e23_3D).nnz  -- Should be 2

-- Test the Grassmann.jl rotor
#eval! let R := grassmannExampleRotor
       R.nnz  -- Should have multiple components

-- Test 3D rotation
#eval! let R := grassmannExampleRotor
       let v := vec3 1.0 0.0 0.0  -- e1
       let rotated := applyRotor3D R v
       (getX3 rotated, getY3 rotated, getZ3 rotated)

-- Test vector at origin (should have zero displacement)
#eval! let R := grassmannExampleRotor
       let v := vec3 0.0 0.0 0.0
       let rotated := applyRotor3D R v
       (getX3 rotated, getY3 rotated, getZ3 rotated)

-- Generate small 3D field
#eval! let points := computeVectorField3D grassmannExampleRotor 3 1.0
       points.length  -- Should be 27 (3x3x3)

-- Generate JSON preview
#eval! let points := computeVectorField3D grassmannExampleRotor 2 1.0
       (generateJSON3D points).length

-- Output HTML (use #eval IO.println to see full output)
#eval IO.println (generateVectorField3D 8 1.5)

end Grassmann.Visualization
