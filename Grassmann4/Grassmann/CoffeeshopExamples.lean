/-
  Grassmann/CoffeeshopExamples.lean - Ganja.js Coffeeshop-style Examples

  Port of examples from https://enkimute.github.io/ganja.js/examples/coffeeshop.html
  Demonstrates geometric algebra operations in various signatures.

  References:
  - https://github.com/enkimute/ganja.js
  - https://bivector.net/tools.html
-/
import Grassmann.DSL
import Grassmann.SparseMultivector
import LeanPlot

open Grassmann Grassmann.DSL
open LeanPlot LeanPlot.Render

namespace CoffeeshopExamples

/-! ## Utility Functions -/

def approxEq (a b : Float) (eps : Float := 1e-6) : Bool :=
  Float.abs (a - b) < eps

def pi : Float := 3.14159265358979323846

end CoffeeshopExamples

open CoffeeshopExamples

/-! ═══════════════════════════════════════════════════════════════════════════
    COMPLEX NUMBERS - Cl(0,1)
    The simplest non-trivial Clifford algebra: i² = -1
═══════════════════════════════════════════════════════════════════════════ -/

-- Complex number example: (2 + 3i) * (1 + 2i) = -4 + 7i
#eval Cl(0,1) {
  let z1 := MultivectorS.scalar 2.0 + e₁.smul 3.0  -- 2 + 3i
  let z2 := MultivectorS.scalar 1.0 + e₁.smul 2.0  -- 1 + 2i
  let product := z1 * z2
  let real := product.scalarPart
  let imag := product.coeff 1
  s!"(2+3i)(1+2i) = {real} + {imag}i  (expect: -4 + 7i)"
}

-- Euler's formula: e^(iθ) = cos(θ) + i·sin(θ)
#eval Cl(0,1) {
  -- For i² = -1, exp(θi) = cos(θ) + sin(θ)i
  let theta := pi / 4  -- 45 degrees
  let c := Float.cos theta
  let s := Float.sin theta
  let euler := MultivectorS.scalar c + e₁.smul s
  -- Verify: euler² should rotate by 90 degrees
  let rotated := euler * euler
  let real := rotated.scalarPart
  let imag := rotated.coeff 1
  s!"e^(iπ/4) squared: {real} + {imag}i  (expect: 0 + 1i)"
}

-- Complex magnitude: |3 + 4i| = 5
#eval Cl(0,1) {
  let z := MultivectorS.scalar 3.0 + e₁.smul 4.0  -- 3 + 4i
  let zConj := MultivectorS.scalar 3.0 + e₁.smul (-4.0)  -- 3 - 4i
  let magSq := (z * zConj).scalarPart
  let mag := Float.sqrt magSq
  if approxEq mag 5.0 then "|3+4i| = 5 ✓" else s!"|3+4i| = {mag} ✗"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    DUAL NUMBERS - Cl(0,0,1)
    ε² = 0, useful for automatic differentiation
═══════════════════════════════════════════════════════════════════════════ -/

-- Dual numbers: (a + bε)(c + dε) = ac + (ad + bc)ε
#eval Cl(0,0,1) {
  let d1 := MultivectorS.scalar 2.0 + e₁.smul 3.0  -- 2 + 3ε
  let d2 := MultivectorS.scalar 4.0 + e₁.smul 5.0  -- 4 + 5ε
  let product := d1 * d2
  let real := product.scalarPart
  let dual := product.coeff 1
  -- (2 + 3ε)(4 + 5ε) = 8 + (10 + 12)ε = 8 + 22ε
  s!"(2+3ε)(4+5ε) = {real} + {dual}ε  (expect: 8 + 22ε)"
}

-- Automatic differentiation: f(x) = x², f'(x) = 2x
-- Evaluate at x=3: f(3+ε) = 9 + 6ε, so f(3)=9, f'(3)=6
#eval Cl(0,0,1) {
  let x := MultivectorS.scalar 3.0 + e₁  -- 3 + ε
  let xSquared := x * x  -- f(x) = x²
  let value := xSquared.scalarPart  -- f(3)
  let deriv := xSquared.coeff 1     -- f'(3)
  s!"x² at x=3: value={value}, derivative={deriv}  (expect: 9, 6)"
}

-- ε² = 0 (the defining property of dual numbers)
#eval Cl(0,0,1) {
  let eps := e₁
  let epsSq := (eps * eps).scalarPart
  if approxEq epsSq 0.0 then "ε² = 0 ✓" else s!"ε² = {epsSq} ✗"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    QUATERNIONS - Cl(0,2)
    i² = j² = k² = ijk = -1
═══════════════════════════════════════════════════════════════════════════ -/

-- Quaternion basis: i² = j² = k² = -1
#eval Cl(0,2) {
  let i := e₁
  let j := e₂
  let k := e₁₂  -- k = ij in quaternion terms

  let iSq := (i * i).scalarPart
  let jSq := (j * j).scalarPart
  let kSq := (k * k).scalarPart

  if approxEq iSq (-1.0) && approxEq jSq (-1.0) && approxEq kSq (-1.0)
  then "i²=j²=k²=-1 ✓"
  else s!"i²={iSq}, j²={jSq}, k²={kSq} ✗"
}

-- Quaternion product: ij = k, ji = -k
#eval Cl(0,2) {
  let i := e₁
  let j := e₂
  let ij := i * j
  let ji := j * i
  let ijCoeff := ij.coeff 3  -- e₁₂ component
  let jiCoeff := ji.coeff 3

  if approxEq ijCoeff 1.0 && approxEq jiCoeff (-1.0)
  then "ij=k, ji=-k ✓"
  else s!"ij coeff={ijCoeff}, ji coeff={jiCoeff} ✗"
}

-- Unit quaternion rotation: rotate vector (1,0,0) by 90° around z-axis
-- q = cos(45°) + sin(45°)k, gives (0,1,0)
#eval Cl(0,2) {
  -- Quaternion q for 90° rotation around z (k axis)
  let angle := pi / 2
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)
  let k := e₁₂
  let q := MultivectorS.scalar c + k.smul s

  -- In quaternions, we encode vector (x,y,z) as xi + yj + zk
  -- Here i=e₁, j=e₂ for the quaternion multiplication
  let v := e₁  -- vector (1,0,0) encoded as i

  -- Rotate: q * v * q†
  let qConj := MultivectorS.scalar c + k.smul (-s)  -- conjugate
  let rotated := q * v * qConj

  let xNew := rotated.coeff 1  -- e₁ component
  let yNew := rotated.coeff 2  -- e₂ component

  s!"Rotate (1,0,0) by 90° around z: ({xNew}, {yNew})  (expect: (0, 1))"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    R3 - 3D EUCLIDEAN ALGEBRA Cl(3,0,0)
    Vectors, bivectors, rotations
═══════════════════════════════════════════════════════════════════════════ -/

-- Vector dot product via geometric product: u·v = ½(uv + vu)
#eval R3 {
  let u := e₁.smul 3.0 + e₂.smul 4.0  -- (3, 4, 0)
  let v := e₁.smul 1.0 + e₂.smul 2.0  -- (1, 2, 0)

  let uv := u * v
  let vu := v * u
  let dotProduct := ((uv + vu).scalarPart) / 2.0  -- 3*1 + 4*2 = 11

  if approxEq dotProduct 11.0 then "u·v = 11 ✓" else s!"u·v = {dotProduct} ✗"
}

-- Vector cross product via wedge: u×v from u∧v
#eval R3 {
  let u := e₁  -- (1, 0, 0)
  let v := e₂  -- (0, 1, 0)

  let wedge := u ⋀ₛ v  -- e₁ ∧ e₂ = e₁₂

  -- e₁₂ corresponds to z-axis in cross product (Hodge dual)
  let zComp := wedge.coeff 3  -- e₁₂ = bit pattern 0b11 = 3

  if approxEq zComp 1.0
  then "e₁ × e₂ = e₃ direction ✓"
  else s!"wedge e₁₂ = {zComp} ✗"
}

-- Rotor rotation: rotate (1,0,0) by 90° around z-axis
#eval R3 {
  let angle := pi / 2
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)

  -- Rotor for rotation in e₁e₂ plane (around z-axis)
  let B := e₁₂  -- bivector representing rotation plane
  let R := MultivectorS.scalar c + B.smul (-s)  -- R = cos(θ/2) - sin(θ/2)B
  let Rrev := MultivectorS.scalar c + B.smul s  -- R† = cos(θ/2) + sin(θ/2)B

  let v := e₁  -- vector (1, 0, 0)
  let rotated := R * v * Rrev

  let x := rotated.coeff 1
  let y := rotated.coeff 2
  let z := rotated.coeff 4  -- e₃ = bit 4

  s!"Rotate (1,0,0) by 90°: ({x}, {y}, {z})  (expect: (0, 1, 0))"
}

-- Reflection: reflect (1,1,0) across the yz-plane (normal = e₁)
#eval R3 {
  let n := e₁  -- normal to yz-plane
  let v := e₁ + e₂  -- vector (1, 1, 0)

  -- Reflection: v' = -n v n (for unit n)
  let reflected := (n.smul (-1.0)) * v * n

  let x := reflected.coeff 1
  let y := reflected.coeff 2

  s!"Reflect (1,1,0) across yz: ({x}, {y})  (expect: (-1, 1))"
}

-- Pseudoscalar I = e₁₂₃ squares to -1 in R³
#eval R3 {
  let I := e₁₂₃
  let ISq := (I * I).scalarPart
  if approxEq ISq (-1.0) then "I² = -1 ✓" else s!"I² = {ISq} ✗"
}

-- Hodge dual: ⋆e₁ = e₂₃ in R³
#eval R3 {
  let I := e₁₂₃
  let star_e1 := e₁ * I  -- ⋆e₁ = e₁ · I
  -- e₁ * e₁₂₃ = e₂₃ (or -e₂₃ depending on convention)
  let coeff := star_e1.coeff 6  -- e₂₃ = bits 0b110 = 6
  s!"⋆e₁ = {coeff}·e₂₃  (expect: ±1)"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    PGA3D - 3D PROJECTIVE GEOMETRIC ALGEBRA Cl(3,0,1)
    Points, lines, planes in homogeneous coordinates
═══════════════════════════════════════════════════════════════════════════ -/

-- In PGA, e₀ (our e₄) is the degenerate direction: e₀² = 0
#eval PGA3 {
  let e0 := e₄  -- degenerate basis vector
  let e0Sq := (e0 * e0).scalarPart
  if approxEq e0Sq 0.0 then "e₀² = 0 ✓" else s!"e₀² = {e0Sq} ✗"
}

-- Plane representation: ax + by + cz + d = 0 → a·e₁ + b·e₂ + c·e₃ + d·e₀
#eval PGA3 {
  -- Plane x = 1 (yz-plane shifted by 1)
  let plane := e₁ + e₄  -- 1·e₁ + 0·e₂ + 0·e₃ + 1·e₀
  s!"Plane x=1: grade-1 element with {plane.nnz} non-zero coefficients"
}

-- Point representation in PGA: point at (x,y,z) is the pseudoscalar
-- P = e₁₂₃ + x·e₀₂₃ + y·e₀₃₁ + z·e₀₁₂ (Using regressive product / join)
#eval PGA3 {
  -- The ideal point (direction) is just e₁₂₃
  let idealPoint := e₁₂₃
  let grade := idealPoint.nnz
  s!"Ideal point (at infinity): element with {grade} non-zero component"
}

-- Line as meet of two planes: L = P₁ ∧ P₂
#eval PGA3 {
  let P1 := e₁  -- plane x = 0 (yz-plane)
  let P2 := e₂  -- plane y = 0 (xz-plane)
  let L := P1 ⋀ₛ P2  -- z-axis
  let e12Coeff := L.coeff 3  -- e₁₂ component
  s!"z-axis from planes: e₁∧e₂ coeff = {e12Coeff}  (expect: 1)"
}

-- Translator: move along x-axis by distance d
-- T = 1 + (d/2)·e₀₁
#eval PGA3 {
  let d := 2.0
  let T := MultivectorS.scalar 1.0 + (e₁ ⋀ₛ e₄).smul (d / 2.0)

  -- In full PGA, translation moves points: T * P * T†
  -- Here we just verify the translator structure
  let scalarPart := T.scalarPart
  s!"Translator by {d} along x: scalar={scalarPart}"
}

-- Rotor in PGA: rotation around z-axis by angle θ
-- R = cos(θ/2) + sin(θ/2)·e₁₂
#eval PGA3 {
  let angle := pi / 2
  let c := Float.cos (angle / 2)
  let s := Float.sin (angle / 2)

  let rotor := MultivectorS.scalar c + e₁₂.smul s

  -- Rotor squared should give 180° rotation
  let rotorSq := rotor * rotor
  let scalar := rotorSq.scalarPart
  let e12Coeff := rotorSq.coeff 3

  s!"90° rotor squared: scalar={scalar}, e₁₂={e12Coeff}  (expect: 0, 1)"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    SPACETIME ALGEBRA - Cl(1,3)
    Minkowski space with (+,-,-,-) signature
═══════════════════════════════════════════════════════════════════════════ -/

-- Spacetime signature: e₁²=1 (time), e₂²=e₃²=e₄²=-1 (space)
#eval STA {
  let t := (e₁ * e₁).scalarPart
  let x := (e₂ * e₂).scalarPart
  let y := (e₃ * e₃).scalarPart
  let z := (e₄ * e₄).scalarPart

  if approxEq t 1.0 && approxEq x (-1.0) && approxEq y (-1.0) && approxEq z (-1.0)
  then "STA signature (+,-,-,-) ✓"
  else s!"Signature: t={t}, x={x}, y={y}, z={z} ✗"
}

-- Spacetime interval: (Δt)² - (Δx)² - (Δy)² - (Δz)²
#eval STA {
  -- 4-vector: v = t·e₁ + x·e₂ + y·e₃ + z·e₄
  let v := e₁.smul 5.0 + e₂.smul 3.0 + e₃.smul 0.0 + e₄.smul 4.0  -- (5,3,0,4)

  -- v² = t² - x² - y² - z² = 25 - 9 - 0 - 16 = 0 (lightlike!)
  let vSq := (v * v).scalarPart

  if approxEq vSq 0.0
  then "Lightlike 4-vector: v² = 0 ✓"
  else s!"v² = {vSq} ✗"
}

-- Pseudoscalar in STA: I = e₁₂₃₄, I² = ?
#eval STA {
  let I := e₁₂₃₄
  let ISq := (I * I).scalarPart
  s!"STA pseudoscalar I² = {ISq}  (depends on signature convention)"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    CGA - CONFORMAL GEOMETRIC ALGEBRA Cl(4,1)
    Circles, spheres, and conformal transformations
═══════════════════════════════════════════════════════════════════════════ -/

-- CGA signature: first 4 positive, last negative
#eval CGA3 {
  let sig := [
    (e₁ * e₁).scalarPart,
    (e₂ * e₂).scalarPart,
    (e₃ * e₃).scalarPart,
    (e₄ * e₄).scalarPart,
    (e₅ * e₅).scalarPart
  ]
  s!"CGA signature: {sig}  (expect: [1,1,1,1,-1])"
}

-- Null vectors in CGA: e∞ = e₊ + e₋ = e₄ + e₅, e₀ = (e₋ - e₊)/2 = (e₅ - e₄)/2
-- In Cl(4,1): e₄² = +1, e₅² = -1
-- e∞² = e₀² = 0, e∞·e₀ = -1 (normalized), or n∞·n₀ = -2 (unnormalized n₀ = e₅ - e₄)
#eval CGA3 {
  -- Unnormalized null basis (for n∞·n₀ = -2)
  let n0 := e₅ + e₄.smul (-1.0)  -- n₀ = e₅ - e₄ (e₋ - e₊)
  let ninf := e₄ + e₅            -- n∞ = e₄ + e₅ (e₊ + e₋)

  let n0Sq := (n0 * n0).scalarPart
  let ninfSq := (ninf * ninf).scalarPart
  let product := (n0 * ninf + ninf * n0).scalarPart / 2.0

  s!"n₀²={n0Sq}, n∞²={ninfSq}, n₀·n∞={product}  (expect: 0, 0, -2)"
}

-- Point in CGA: P = p + ½|p|²·e∞ + e₀ where p is the Euclidean point
-- Using NORMALIZED null basis: e₀ = (e₅ - e₄)/2, e∞ = e₄ + e₅
-- This ensures P² = 0 for any point
#eval CGA3 {
  -- Point at (1, 0, 0)
  let p := e₁
  -- Normalized null basis for proper embedding
  let e0 := (e₅ + e₄.smul (-1.0)).smul 0.5  -- e₀ = (e₅ - e₄)/2
  let einf := e₄ + e₅                        -- e∞ = e₄ + e₅

  -- P = p + ½|p|²·e∞ + e₀
  let pSq := (p * p).scalarPart  -- |p|² = 1
  let P := p + einf.smul (pSq / 2.0) + e0

  -- A point should satisfy P² = 0 (null vector)
  let PSq := (P * P).scalarPart

  s!"Point (1,0,0) in CGA: P²={PSq}  (expect: 0)"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    SPLIT-COMPLEX NUMBERS - Cl(1,0)
    j² = +1 (hyperbolic numbers)
═══════════════════════════════════════════════════════════════════════════ -/

-- Split-complex: j² = +1 (unlike i² = -1)
#eval Cl(1,0) {
  let j := e₁
  let jSq := (j * j).scalarPart
  if approxEq jSq 1.0 then "j² = +1 ✓" else s!"j² = {jSq} ✗"
}

-- Hyperbolic functions: cosh + j·sinh
#eval Cl(1,0) {
  let t := 1.0
  let c := Float.cosh t
  let s := Float.sinh t
  let h := MultivectorS.scalar c + e₁.smul s

  -- h² should give cosh(2t) + j·sinh(2t)
  let h2 := h * h
  let realPart := h2.scalarPart
  let jPart := h2.coeff 1

  let expected_real := Float.cosh (2.0 * t)
  let expected_j := Float.sinh (2.0 * t)

  s!"(cosh t + j·sinh t)² = {realPart} + {jPart}j  (expect: {expected_real}, {expected_j})"
}

-- Null cone: (a + jb)(a - jb) = a² - b² = 0 when a = ±b
#eval Cl(1,0) {
  let a := 3.0
  let b := 3.0
  let z := MultivectorS.scalar a + e₁.smul b
  let zBar := MultivectorS.scalar a + e₁.smul (-b)
  let product := (z * zBar).scalarPart  -- a² - b²
  s!"(3+3j)(3-3j) = {product}  (expect: 0, null element)"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    QUATERNION MANDELBROT - Cl(0,2)
    Port of Ganja.js quaternion_mandelbrot coffeeshop example
═══════════════════════════════════════════════════════════════════════════ -/

-- Quaternion Mandelbrot: z = z² + c with quaternion arithmetic
-- Iteration count gives coloring; here we output ASCII art

def mandelbrotIterate (cx cy : Float) (maxIter : Nat := 40) : Nat :=
  -- Use fuel-based iteration to avoid termination issues
  let rec go : Nat → Float → Float → Nat
    | 0, _, _ => 0
    | n + 1, zr, zi =>
      let mag2 := zr * zr + zi * zi
      if mag2 > 4.0 then maxIter - (n + 1)
      else
        -- z = z² + c: (zr + zi·i)² = zr² - zi² + 2·zr·zi·i
        let newZr := zr * zr - zi * zi + cx
        let newZi := 2.0 * zr * zi + cy
        go n newZr newZi
  go maxIter 0.0 0.0

-- Color palette for Mandelbrot (classic blue-black-orange scheme)
def mandelbrotColor (iter : Nat) (maxIter : Nat := 40) : RGB :=
  if iter >= maxIter then RGB.black
  else
    -- Smooth coloring based on iteration count
    let t := iter.toFloat / maxIter.toFloat
    -- Classic Mandelbrot colors: black → blue → white → orange → black
    if t < 0.25 then
      let s := t * 4
      ⟨(s * 50).toUInt8, (s * 100).toUInt8, (s * 200).toUInt8⟩  -- Black to blue
    else if t < 0.5 then
      let s := (t - 0.25) * 4
      ⟨(50 + s * 205).toUInt8, (100 + s * 155).toUInt8, (200 + s * 55).toUInt8⟩  -- Blue to white
    else if t < 0.75 then
      let s := (t - 0.5) * 4
      ⟨255, (255 - s * 128).toUInt8, (255 - s * 180).toUInt8⟩  -- White to orange
    else
      let s := (t - 0.75) * 4
      ⟨(255 - s * 200).toUInt8, (127 - s * 100).toUInt8, (75 - s * 75).toUInt8⟩  -- Orange to dark

-- Generate Mandelbrot as a bitmap
def mandelbrotBitmap (width height : Nat) (maxIter : Nat := 100) : Bitmap := Id.run do
  let mut bmp := Bitmap.create width height
  for py in [:height] do
    for px in [:width] do
      -- Map pixel to complex plane: x ∈ [-2.5, 1], y ∈ [-1.2, 1.2]
      let cx := (px.toFloat / width.toFloat) * 3.5 - 2.5
      let cy := (py.toFloat / height.toFloat) * 2.4 - 1.2
      let iter := mandelbrotIterate cx cy maxIter
      let color := mandelbrotColor iter maxIter
      bmp := bmp.setPixel px py color
  bmp

-- Save Mandelbrot to PNG file
#eval do
  let bmp := mandelbrotBitmap 800 600 100
  PNG.writePNG "mandelbrot_ga.png" bmp
  IO.println "Saved Mandelbrot set to mandelbrot_ga.png (800×600, 100 iterations)"

-- Save boundary scatter plot to SVG
#eval do
  let pts : Array (Float × Float) := Id.run do
    let mut result := #[]
    for yi in [:100] do
      for xi in [:140] do
        let cx := (xi.toFloat / 140.0) * 3.5 - 2.5
        let cy := (yi.toFloat / 100.0) * 2.4 - 1.2
        let iter := mandelbrotIterate cx cy 100
        -- Only plot points near the boundary (20-80 iterations)
        if iter > 20 && iter < 80 then
          result := result.push (cx, cy)
    result
  let g := scatter pts |>.title "Mandelbrot Set Boundary"
  -- Use absolute path to ensure it's written in the right place
  let svgPath := "/Users/alokbeniwal/Grassmann/Grassmann4/mandelbrot_boundary.svg"
  g.saveSVG svgPath
  IO.println s!"Saved {pts.size} boundary points to {svgPath}"

-- Quaternion Mandelbrot computation using actual Cl(0,2) algebra
#eval Cl(0,2) {
  -- Sample a single point: c = -0.4 + 0.6i
  let cx := -0.4
  let cy := 0.6
  let c := MultivectorS.scalar cx + e₁.smul cy

  -- Simple iteration without recursion (loop unroll for #eval)
  let z0 : MultivectorS _ Float := MultivectorS.scalar 0.0
  let z1 := z0 * z0 + c
  let z2 := z1 * z1 + c
  let z3 := z2 * z2 + c
  let z4 := z3 * z3 + c
  let z5 := z4 * z4 + c

  let mag2 := (z5 * z5.reverse).scalarPart
  let escaped := if mag2 > 4.0 then "true" else "false"

  s!"Mandelbrot at c=(-0.4+0.6i): 5 iterations, |z|²={mag2}, escaped={escaped}"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    PGA2D GEOMETRY - Cl(2,0,1)
    Points, lines, and their operations in 2D projective space
═══════════════════════════════════════════════════════════════════════════ -/

-- In PGA2D: point P = x·e₂₀ + y·e₀₁ + e₁₂ (homogeneous)
-- Line L = a·e₁ + b·e₂ + c·e₀ represents ax + by + c = 0

#eval PGA2 {
  -- Create two points
  let p1_x := 1.0
  let p1_y := 0.0
  let p2_x := 0.0
  let p2_y := 1.0

  -- Points as dual representation: P = x·e₂₀ + y·e₀₁ + e₁₂
  -- Using our basis: e₁, e₂, e₃ where e₃² = 0
  let e0 := e₃  -- degenerate direction
  let e20 := e₂ ⋀ₛ e0
  let e01 := e0 ⋀ₛ e₁
  let e12 := e₁ ⋀ₛ e₂

  let P1 := e20.smul p1_x + e01.smul p1_y + e12
  let P2 := e20.smul p2_x + e01.smul p2_y + e12

  -- Line through two points: L = P1 ∨ P2 (regressive product)
  -- In PGA, this is the join operation
  let L := P1 ∨ₛ P2

  s!"Line through (1,0) and (0,1): L = scalar:{L.scalarPart}, e₁:{L.coeff 1}, e₂:{L.coeff 2}"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    LORENTZ BOOST - Spacetime Algebra Cl(1,3)
    Port of Ganja.js timespace_lorentz example
═══════════════════════════════════════════════════════════════════════════ -/

-- Lorentz boost in spacetime algebra
#eval STA {
  -- In STA: e₁²=+1 (time), e₂²=e₃²=e₄²=-1 (space)
  let et := e₁  -- timelike
  let ex := e₂  -- spacelike x

  -- Rapidity parameter (related to velocity by v = c·tanh(φ))
  let phi := 0.5  -- rapidity

  -- Lorentz boost bivector: B = et ∧ ex
  let B := et ⋀ₛ ex

  -- Boost rotor: L = exp(φ/2 · B) = cosh(φ/2) + sinh(φ/2)·B
  let c := Float.cosh (phi / 2.0)
  let s := Float.sinh (phi / 2.0)
  let L := MultivectorS.scalar c + B.smul s

  -- Boost a time-like vector (1,0,0,0)
  let Lrev := MultivectorS.scalar c + B.smul (-s)
  let boosted := L * et * Lrev

  let t_comp := boosted.coeff 1  -- time component
  let x_comp := boosted.coeff 2  -- x component

  -- γ = cosh(φ), βγ = sinh(φ)
  let gamma := Float.cosh phi
  let beta_gamma := Float.sinh phi

  s!"Lorentz boost (φ={phi}): (1,0,0,0) → (t'={t_comp}, x'={x_comp})  \
     (expect: γ={gamma}, βγ={beta_gamma})"
}

/-! ═══════════════════════════════════════════════════════════════════════════
    INVERSE KINEMATICS (simplified) - PGA2D
    Move end-effector to target using rotor interpolation
═══════════════════════════════════════════════════════════════════════════ -/

-- Simple 2-joint arm: compute angles to reach target
#eval do
  -- Arm segment lengths
  let l1 := 1.0
  let l2 := 1.0

  -- Target position
  let tx := 1.5
  let ty := 0.5

  -- Distance to target
  let d := Float.sqrt (tx * tx + ty * ty)

  -- Check reachability
  if d > l1 + l2 then
    IO.println "Target unreachable!"
  else if d < Float.abs (l1 - l2) then
    IO.println "Target too close!"
  else
    -- Law of cosines for elbow angle
    let cosTheta2 := (d * d - l1 * l1 - l2 * l2) / (2.0 * l1 * l2)
    let theta2 := Float.acos cosTheta2

    -- Shoulder angle
    let alpha := Float.atan2 ty tx
    let beta := Float.acos ((l1 * l1 + d * d - l2 * l2) / (2.0 * l1 * d))
    let theta1 := alpha - beta

    IO.println s!"2-Joint IK to ({tx}, {ty}):"
    IO.println s!"  Joint 1 angle: {theta1 * 180.0 / pi}°"
    IO.println s!"  Joint 2 angle: {theta2 * 180.0 / pi}°"

    -- Verify forward kinematics
    let j1_x := l1 * Float.cos theta1
    let j1_y := l1 * Float.sin theta1
    let end_x := j1_x + l2 * Float.cos (theta1 + theta2)
    let end_y := j1_y + l2 * Float.sin (theta1 + theta2)
    IO.println s!"  End effector: ({end_x}, {end_y}) ≈ ({tx}, {ty})"

/-! ═══════════════════════════════════════════════════════════════════════════
    SUMMARY
═══════════════════════════════════════════════════════════════════════════ -/

#eval IO.println "
╔══════════════════════════════════════════════════════════════╗
║      Ganja.js Coffeeshop Examples in Lean 4 GA DSL          ║
╠══════════════════════════════════════════════════════════════╣
║ Algebras demonstrated:                                       ║
║   • Cl(0,1)   - Complex numbers (i²=-1)                     ║
║   • Cl(0,0,1) - Dual numbers (ε²=0, autodiff)               ║
║   • Cl(0,2)   - Quaternions (i²=j²=k²=ijk=-1)               ║
║   • Cl(1,0)   - Split-complex (j²=+1)                       ║
║   • R3        - 3D Euclidean (rotations, reflections)       ║
║   • PGA3      - 3D Projective GA (points, lines, planes)    ║
║   • STA       - Spacetime Algebra Cl(1,3)                   ║
║   • CGA3      - Conformal GA Cl(4,1)                        ║
╠══════════════════════════════════════════════════════════════╣
║ Key operations:                                              ║
║   • Geometric product (*)                                    ║
║   • Wedge product (⋀ₛ)                                       ║
║   • Rotors: R = cos(θ/2) + sin(θ/2)·B                       ║
║   • Sandwich: R * v * R†                                     ║
║   • Null vectors in PGA (e₀²=0) and CGA                     ║
╚══════════════════════════════════════════════════════════════╝
"
-- Force rebuild $(date)
