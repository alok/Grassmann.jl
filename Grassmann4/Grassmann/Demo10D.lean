/-
  Demo10D.lean - Random 4D multivector rotated in 10D, projected to 3D

  Demonstrates:
  1. Generate random 4D multivector
  2. Embed into 10D ambient space
  3. Rotate by random angle in random plane
  4. Project to 3D and visualize
-/
import Grassmann.SparseMultivector
import Grassmann.RotorExp

namespace Grassmann.Demo10D

open Grassmann

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-! ## Signatures -/

/-- 10-dimensional Euclidean space -/
def R10 : Signature 10 := Signature.euclidean 10

/-- 4-dimensional Euclidean space (for initial vector) -/
def R4 : Signature 4 := Signature.euclidean 4

/-! ## Random Number Generation (simple LCG for demo) -/

/-- Simple linear congruential generator state -/
structure RNG where
  seed : UInt64
  deriving Repr

/-- Initialize RNG -/
def RNG.new (seed : UInt64 := 12345) : RNG := { seed }

/-- Generate next random value and update state -/
def RNG.next (rng : RNG) : RNG × Float :=
  -- LCG parameters (Numerical Recipes)
  let a : UInt64 := 1664525
  let c : UInt64 := 1013904223
  let m : UInt64 := 0xFFFFFFFF
  let newSeed := (a * rng.seed + c) % m
  let float := (newSeed.toNat.toFloat / m.toNat.toFloat) * 2.0 - 1.0  -- Range [-1, 1]
  ({ seed := newSeed }, float)

/-- Generate n random floats -/
def RNG.nextN (rng : RNG) (n : Nat) : RNG × Array Float :=
  let rec go (rng : RNG) (k : Nat) (acc : Array Float) : RNG × Array Float :=
    if k = 0 then (rng, acc)
    else
      let (rng', val) := rng.next
      go rng' (k - 1) (acc.push val)
  go rng n #[]

/-! ## Random Multivector Generation -/

/-- Create a random 4D vector (grade-1 multivector) -/
def random4DVector (rng : RNG) : RNG × MultivectorS R4 Float :=
  let (rng', vals) := rng.nextN 4
  let e1 : MultivectorS R4 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R4 Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS R4 Float := MultivectorS.basis ⟨2, by omega⟩
  let e4 : MultivectorS R4 Float := MultivectorS.basis ⟨3, by omega⟩
  let mv := e1.smul (vals[0]!) + e2.smul (vals[1]!) + e3.smul (vals[2]!) + e4.smul (vals[3]!)
  (rng', mv)

/-- Create a random 4D multivector with scalar + vector + bivector parts -/
def random4DMultivector (rng : RNG) : RNG × MultivectorS R4 Float :=
  -- 4D has 1 + 4 + 6 + 4 + 1 = 16 components
  -- We'll just do scalar + vector + bivector = 1 + 4 + 6 = 11 components
  let (rng', vals) := rng.nextN 11
  let e1 : MultivectorS R4 Float := MultivectorS.basis ⟨0, by omega⟩
  let e2 : MultivectorS R4 Float := MultivectorS.basis ⟨1, by omega⟩
  let e3 : MultivectorS R4 Float := MultivectorS.basis ⟨2, by omega⟩
  let e4 : MultivectorS R4 Float := MultivectorS.basis ⟨3, by omega⟩
  -- Scalar
  let mv := MultivectorS.scalar (vals[0]!)
  -- Vectors
  let mv := mv + e1.smul (vals[1]!) + e2.smul (vals[2]!) + e3.smul (vals[3]!) + e4.smul (vals[4]!)
  -- Bivectors: e12, e13, e14, e23, e24, e34
  let e12 := e1 * e2
  let e13 := e1 * e3
  let e14 := e1 * e4
  let e23 := e2 * e3
  let e24 := e2 * e4
  let e34 := e3 * e4
  let mv := mv + e12.smul (vals[5]!) + e13.smul (vals[6]!) + e14.smul (vals[7]!)
              + e23.smul (vals[8]!) + e24.smul (vals[9]!) + e34.smul (vals[10]!)
  (rng', mv)

/-! ## Embedding and Projection -/

/-- Embed a 4D multivector into 10D (uses first 4 dimensions) -/
def embed4Dto10D (mv4 : MultivectorS R4 Float) : MultivectorS R10 Float :=
  -- For each non-zero term in mv4, create corresponding term in R10
  -- Blade indices in 4D map directly to 10D (e.g., e12 = bit 0b0011 stays the same)
  let pairs := mv4.toList
  MultivectorS.ofList (pairs.map fun (idx, coeff) => (idx, coeff))

/-- Project 10D multivector to first 3 dimensions (extracts vector part) -/
def project10Dto3D (mv10 : MultivectorS R10 Float) : (Float × Float × Float) :=
  -- Extract e1, e2, e3 coefficients (blade indices 1, 2, 4)
  (mv10.coeff 1, mv10.coeff 2, mv10.coeff 4)

/-- Project to 4D (for comparison) -/
def project10Dto4D (mv10 : MultivectorS R10 Float) : (Float × Float × Float × Float) :=
  (mv10.coeff 1, mv10.coeff 2, mv10.coeff 4, mv10.coeff 8)

/-! ## Random Rotation in 10D -/

/-- Create basis vector i in R10 -/
def basisR10 (i : Fin 10) : MultivectorS R10 Float :=
  MultivectorS.basis i

/-- Create a random bivector (rotation plane) in 10D -/
def randomBivector10D (rng : RNG) : RNG × MultivectorS R10 Float :=
  -- Pick two random basis vectors and wedge them
  -- For variety, use a linear combination of several bivectors
  let (rng1, coeffs) := rng.nextN 10  -- Coefficients for some bivector combinations

  -- Create a few bivectors and combine them
  let e1 := basisR10 ⟨0, by omega⟩
  let e2 := basisR10 ⟨1, by omega⟩
  let e3 := basisR10 ⟨2, by omega⟩
  let e4 := basisR10 ⟨3, by omega⟩
  let e5 := basisR10 ⟨4, by omega⟩
  let e6 := basisR10 ⟨5, by omega⟩
  let e7 := basisR10 ⟨6, by omega⟩

  -- Mix of bivectors across dimensions (including higher ones)
  let B12 := e1 * e2  -- In first 4D subspace
  let B34 := e3 * e4
  let B15 := e1 * e5  -- Mixing first 4 with higher dims
  let B26 := e2 * e6
  let B37 := e3 * e7

  let bivector := B12.smul (coeffs[0]!) + B34.smul (coeffs[1]!)
                + B15.smul (coeffs[2]!) + B26.smul (coeffs[3]!)
                + B37.smul (coeffs[4]!)

  -- Normalize to unit bivector (B² = -1) for clean rotation
  let bivNorm := Float.sqrt (Float.abs ((bivector * bivector).scalarPart))
  let bivector' := if bivNorm > 0.001 then bivector.smul (1.0 / bivNorm) else bivector

  (rng1, bivector')

/-- Create a rotor from bivector and angle: R = cos(θ/2) + sin(θ/2)B -/
def rotor10D (B : MultivectorS R10 Float) (angle : Float) : MultivectorS R10 Float :=
  let halfAngle := angle / 2.0
  MultivectorS.scalar (Float.cos halfAngle) + B.smul (Float.sin halfAngle)

/-- Apply rotation: v' = R * v * R† -/
def rotate10D (R v : MultivectorS R10 Float) : MultivectorS R10 Float :=
  R * v * R†ₛ

/-! ## Main Demo -/

/-- Run the full demo: random 4D multivector -> embed in 10D -> rotate -> project to 3D -/
def runDemo (seed : UInt64 := 42) : IO Unit := do
  let rng := RNG.new seed

  -- Step 1: Generate random 4D multivector
  let (rng1, mv4) := random4DMultivector rng
  IO.println "=== Random 4D Multivector (original) ==="
  IO.println s!"  Non-zero components: {mv4.nnz}"
  IO.println s!"  Scalar part: {mv4.scalarPart}"

  -- Step 2: Embed into 10D
  let mv10 := embed4Dto10D mv4
  IO.println "\n=== Embedded in 10D ==="
  IO.println s!"  Non-zero components: {mv10.nnz}"
  let (x0, y0, z0, w0) := project10Dto4D mv10
  IO.println s!"  First 4 vector components: ({x0}, {y0}, {z0}, {w0})"

  -- Step 3: Generate random rotation
  let (rng2, bivector) := randomBivector10D rng1
  let (_, angleVal) := rng2.next
  let angle := angleVal * pi  -- Random angle in [-π, π]
  IO.println s!"\n=== Random Rotation ==="
  IO.println s!"  Angle: {angle} radians ({angle * 180 / pi}°)"
  IO.println s!"  Bivector (rotation plane) components: {bivector.nnz}"

  -- Create rotor
  let R := rotor10D bivector angle
  IO.println s!"  Rotor components: {R.nnz}"
  IO.println s!"  Rotor scalar part: {R.scalarPart}"

  -- Step 4: Apply rotation
  let mv10_rotated := rotate10D R mv10
  IO.println "\n=== After Rotation ==="
  IO.println s!"  Non-zero components: {mv10_rotated.nnz}"

  -- Step 5: Project to 3D
  let (x1, y1, z1) := project10Dto3D mv10
  let (x2, y2, z2) := project10Dto3D mv10_rotated
  IO.println "\n=== 3D Projection (vector part) ==="
  IO.println s!"  Before rotation: ({x1}, {y1}, {z1})"
  IO.println s!"  After rotation:  ({x2}, {y2}, {z2})"

  -- Compute displacement for visualization
  let dx := x2 - x1
  let dy := y2 - y1
  let dz := z2 - z1
  IO.println s!"\n  Displacement: ({dx}, {dy}, {dz})"
  let mag := Float.sqrt (dx*dx + dy*dy + dz*dz)
  IO.println s!"  Displacement magnitude: {mag}"

  -- Verify rotor is approximately unit
  let RRrev := (R * R†ₛ).scalarPart
  IO.println s!"\n  Rotor normalization check (R*R† ≈ 1): {RRrev}"

  IO.println "\n=== Demo Complete ==="

/-! ## SVG Visualization of Multiple Rotated Vectors -/

/-- Generate SVG showing multiple random 4D vectors rotated in 10D, projected to 3D -/
def generateVisualizationSVG (numVectors : Nat := 20) (seed : UInt64 := 42) : String :=
  let rng := RNG.new seed

  -- Create a fixed rotation for all vectors
  let (rng1, bivector) := randomBivector10D rng
  let angle := pi / 3  -- 60 degrees
  let R := rotor10D bivector angle

  -- Generate multiple random 4D vectors, embed, rotate, project
  let rec generateVectors (rng : RNG) (n : Nat) (acc : Array (Float × Float × Float × Float × Float × Float)) :
      Array (Float × Float × Float × Float × Float × Float) :=
    if n = 0 then acc
    else
      let (rng', mv4) := random4DVector rng
      let mv10 := embed4Dto10D mv4
      let mv10_rot := rotate10D R mv10
      let (x1, y1, z1) := project10Dto3D mv10
      let (x2, y2, z2) := project10Dto3D mv10_rot
      generateVectors rng' (n - 1) (acc.push (x1, y1, z1, x2, y2, z2))

  let vectors := generateVectors rng1 numVectors #[]

  -- Generate SVG
  let width := 500
  let height := 500
  let scale := 150.0
  let cx := width / 2
  let cy := height / 2

  -- Project 3D to 2D (simple orthographic: drop z, shift by z for depth)
  let project3Dto2D (x y z : Float) : (Float × Float) :=
    (x + z * 0.3, y + z * 0.3)  -- Simple isometric-ish projection

  let arrows := vectors.foldl (init := "") fun acc (x1, y1, z1, x2, y2, z2) =>
    let (px1, py1) := project3Dto2D x1 y1 z1
    let (px2, py2) := project3Dto2D x2 y2 z2
    let sx1 := cx.toFloat + px1 * scale
    let sy1 := cy.toFloat - py1 * scale  -- Flip y
    let sx2 := cx.toFloat + px2 * scale
    let sy2 := cy.toFloat - py2 * scale
    acc ++
      s!"  <line x1=\"{sx1}\" y1=\"{sy1}\" x2=\"{sx2}\" y2=\"{sy2}\" stroke=\"blue\" stroke-width=\"2\" marker-end=\"url(#arrow)\"/>\n" ++
      s!"  <circle cx=\"{sx1}\" cy=\"{sy1}\" r=\"3\" fill=\"green\"/>\n"

  s!"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">
  <defs>
    <marker id=\"arrow\" markerWidth=\"10\" markerHeight=\"10\" refX=\"9\" refY=\"3\" orient=\"auto\">
      <path d=\"M0,0 L0,6 L9,3 z\" fill=\"blue\"/>
    </marker>
  </defs>
  <rect width=\"100%\" height=\"100%\" fill=\"#f8f8f8\"/>
  <text x=\"10\" y=\"25\" font-family=\"monospace\" font-size=\"14\">4D vectors in 10D space, rotated, projected to 3D</text>
  <text x=\"10\" y=\"45\" font-family=\"monospace\" font-size=\"11\" fill=\"#666\">Green dots = original, Blue arrows = after rotation</text>
  <!-- Axes -->
  <line x1=\"{cx}\" y1=\"20\" x2=\"{cx}\" y2=\"{height - 20}\" stroke=\"#ddd\" stroke-width=\"1\"/>
  <line x1=\"20\" y1=\"{cy}\" x2=\"{width - 20}\" y2=\"{cy}\" stroke=\"#ddd\" stroke-width=\"1\"/>
{arrows}</svg>"

/-! ## Tests -/

-- Test RNG
#eval! let rng := RNG.new 42
       let (_, vals) := rng.nextN 5
       vals.toList

-- Test random 4D vector
#eval! let rng := RNG.new 42
       let (_, mv) := random4DVector rng
       mv.nnz  -- Should be 4 (or less if some cancel)

-- Test random 4D multivector
#eval! let rng := RNG.new 42
       let (_, mv) := random4DMultivector rng
       (mv.nnz, mv.scalarPart)

-- Test embedding
#eval! let mv4 : MultivectorS R4 Float := MultivectorS.basis ⟨0, by omega⟩  -- e1
       let mv10 := embed4Dto10D mv4
       (mv10.coeff 1, mv10.coeff 2)  -- Should be (1, 0)

-- Test rotation in 10D
#eval! let e1 : MultivectorS R10 Float := basisR10 ⟨0, by omega⟩
       let e2 : MultivectorS R10 Float := basisR10 ⟨1, by omega⟩
       let B := e1 * e2  -- e12 bivector
       let R := rotor10D B (pi / 2)  -- 90 degree rotation
       let rotated := rotate10D R e1
       (rotated.coeff 1, rotated.coeff 2)  -- e1 should become e2 (approx)

-- Run the main demo
#eval! runDemo 42

-- Generate SVG
#eval! IO.println (generateVisualizationSVG 15 42)

end Grassmann.Demo10D
