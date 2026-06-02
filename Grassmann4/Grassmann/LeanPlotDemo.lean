/-
  Grassmann/LeanPlotDemo.lean - LeanPlot demos for the native Vector backend

  Open this file in VS Code with the Lean extension and place the cursor on a
  `#html` command to render the chart in the infoview.
-/
import ProofWidgets.Component.HtmlDisplay
import LeanPlot.API
import Grassmann.NativeVector

set_option linter.hashCommand false

namespace Grassmann.LeanPlotDemo

open Grassmann
open LeanPlot.API

abbrev R2Plot : Signature 2 := Grassmann.R2

def pi : Float := 3.14159265358979323846

def e1_2D : NativeMV R2Plot := NativeMV.vec2 R2Plot 1.0 0.0
def e2_2D : NativeMV R2Plot := NativeMV.vec2 R2Plot 0.0 1.0
def e12_2D : NativeMV R2Plot := NativeMV.blade R2Plot 3

def rotor2D (angle : Float) : NativeMV R2Plot :=
  let halfAngle := angle / 2.0
  NativeMV.scalar R2Plot (Float.cos halfAngle) +
    ((-Float.sin halfAngle) • e12_2D)

def rotate2D (angle : Float) (v : NativeMV R2Plot) : NativeMV R2Plot :=
  let r := rotor2D angle
  r.sandwich v

def getX (v : NativeMV R2Plot) : Float := (v.toVector.get ⟨0, by omega⟩)
def getY (v : NativeMV R2Plot) : Float := (v.toVector.get ⟨1, by omega⟩)

def rotatedX (angle : Float) : Float := getX (rotate2D angle e1_2D)
def rotatedY (angle : Float) : Float := getY (rotate2D angle e1_2D)

def circlePoints (samples : Nat := 96) : Array (Float × Float) :=
  (Array.range samples).map fun i =>
    let angle := (i.toFloat / samples.toFloat) * 2.0 * pi
    let v := rotate2D angle e1_2D
    (getX v, getY v)

def displacementMagnitude (angle : Float) (x y : Float) : Float :=
  let v := NativeMV.vec2 R2Plot x y
  let rotated := rotate2D angle v
  let dx := getX rotated - x
  let dy := getY rotated - y
  Float.sqrt (dx * dx + dy * dy)

def rotorComponentsPlot : ProofWidgets.Html :=
  plotMany #[
    ("x component", rotatedX),
    ("y component", rotatedY)
  ] (steps := 160) (domain := (0.0, 2.0 * pi))

#html rotorComponentsPlot

def rotorCirclePlot : ProofWidgets.Html :=
  scatterChart (circlePoints 128)

#html rotorCirclePlot

def displacementMagnitudePlot : ProofWidgets.Html :=
  let angle := pi / 4.0
  plot (fun x : Float => displacementMagnitude angle x 0.0)
    (steps := 160) (domain := some (-2.0, 2.0))

#html displacementMagnitudePlot

def rotorCoordinateCheck : Array Float :=
  (rotate2D (pi / 2.0) e1_2D).toVector.toArray

#eval rotorCoordinateCheck

def nativeCoefficientCheck : Array Float :=
  (e1_2D * e2_2D).toArray

#eval nativeCoefficientCheck

end Grassmann.LeanPlotDemo
