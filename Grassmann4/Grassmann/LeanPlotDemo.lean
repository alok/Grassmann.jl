/-
  Grassmann/LeanPlotDemo.lean - ProofWidgets visualization with LeanPlot

  Demonstrates interactive plotting of:
  - Rotor rotation trajectories
  - Vector field displacements
  - CGA circle/sphere data

  Usage: Open in VS Code with lean4 extension to see plots in infoview
-/
import LeanPlot.API
import Grassmann.SparseMultivector
import Grassmann.RotorExp

namespace Grassmann.LeanPlotDemo

open Grassmann LeanPlot

/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-! ## Rotor Rotation Trajectory

Plot the trajectory of a vector under rotation by varying angles.
-/

/-- R2 signature for 2D examples -/
def R2 : Signature 2 := Signature.euclidean 2

/-- Create basis vectors for R2 -/
def e1_2D : MultivectorS R2 Float := MultivectorS.basis ⟨0, by omega⟩
def e2_2D : MultivectorS R2 Float := MultivectorS.basis ⟨1, by omega⟩
def e12_2D : MultivectorS R2 Float := e1_2D * e2_2D

/-- Apply a 2D rotor to rotate a vector -/
def rotate2D (angle : Float) (v : MultivectorS R2 Float) : MultivectorS R2 Float :=
  let halfAngle := angle / 2.0
  let c := Float.cos halfAngle
  let s := Float.sin halfAngle
  let R := MultivectorS.scalar c + e12_2D.smul (-s)  -- R = cos(θ/2) - sin(θ/2)e₁₂
  let Rrev := MultivectorS.scalar c + e12_2D.smul s
  R * v * Rrev

/-- Extract x component from 2D multivector -/
def getX (v : MultivectorS R2 Float) : Float := v.coeff 1
/-- Extract y component from 2D multivector -/
def getY (v : MultivectorS R2 Float) : Float := v.coeff 2

/-- Generate rotation trajectory data: (angle, x, y) for unit vector rotated -/
def rotationTrajectory (numPoints : Nat := 100) : Array (Float × Float × Float) :=
  let v0 := e1_2D  -- Start with e₁ = (1, 0)
  (Array.range numPoints).map fun i =>
    let angle := (i.toFloat / numPoints.toFloat) * 2 * pi
    let rotated := rotate2D angle v0
    (angle, getX rotated, getY rotated)

/-- Plot the x and y coordinates as functions of angle -/
#html do
  let data := rotationTrajectory 50
  let xData := data.map fun (θ, x, _) => (θ, x)
  let yData := data.map fun (θ, _, y) => (θ, y)
  return plotMany #[
    ("x = cos(θ)", fun θ => Float.cos θ),
    ("y = sin(θ)", fun θ => Float.sin θ)
  ] |>.withDomain 0 (2 * pi)
    |>.withTitle "Rotor Rotation: e₁ rotated by θ"

/-! ## Parametric Circle Plot

Show the actual (x,y) trajectory as a circle.
-/

/-- Generate circle points from rotation -/
def circlePoints (n : Nat := 50) : Array (Float × Float) :=
  let v0 := e1_2D
  (Array.range n).map fun i =>
    let angle := (i.toFloat / n.toFloat) * 2 * pi
    let rotated := rotate2D angle v0
    (getX rotated, getY rotated)

#html do
  let pts := circlePoints 50
  return scatter pts |>.withTitle "Rotor creates unit circle"

/-! ## Bivector Exponential Components

Plot components of exp(θ·e₁₂) as θ varies.
-/

/-- Components of rotor R = exp(θ·e₁₂/2) = cos(θ/2) + sin(θ/2)·e₁₂ -/
#html do
  return plotMany #[
    ("scalar = cos(θ/2)", fun θ => Float.cos (θ / 2)),
    ("e₁₂ coeff = sin(θ/2)", fun θ => Float.sin (θ / 2))
  ] |>.withDomain 0 (4 * pi)
    |>.withTitle "Rotor components: R = cos(θ/2) + sin(θ/2)·e₁₂"

/-! ## Vector Field Magnitude

Plot the displacement magnitude in a 2D rotor vector field.
-/

/-- Compute displacement magnitude at a point under rotation -/
def displacementMagnitude (angle : Float) (x y : Float) : Float :=
  let v := e1_2D.smul x + e2_2D.smul y
  let rotated := rotate2D angle v
  let dx := getX rotated - x
  let dy := getY rotated - y
  Float.sqrt (dx * dx + dy * dy)

/-- Plot displacement magnitude along x-axis for fixed y=0 -/
#html do
  let angle := pi / 4  -- 45 degree rotation
  return plot (fun x => displacementMagnitude angle x 0)
    |>.withDomain (-2) 2
    |>.withTitle "Displacement magnitude: 45° rotation, y=0"

/-! ## Exponential Growth/Decay

Compare elliptic (cos/sin) vs hyperbolic (cosh/sinh) bivector exponentials.
-/

#html do
  return plotMany #[
    ("cos (elliptic)", Float.cos),
    ("cosh (hyperbolic)", Float.cosh),
    ("sin (elliptic)", Float.sin),
    ("sinh (hyperbolic)", Float.sinh)
  ] |>.withDomain (-2) 2
    |>.withTitle "Elliptic vs Hyperbolic: e^(±B)"

end Grassmann.LeanPlotDemo
