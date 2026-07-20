import GrassmannViz.Scene

/-!
# Static SVG fallback

This renderer deliberately has no interaction and makes no new field values.
It projects the first validated Lean scene frame into a checked-in stage backup.
-/

namespace GrassmannViz

open GrassmannFields

-- SVG tag literals are clearer when kept intact, and the generated artifact is
-- checked byte-for-byte by `MultivectorFallbackCheck.lean`.
set_option linter.style.longLine false

private def clamp (value low high : Float) : Float :=
  if value < low then low else if value > high then high else value

private def fmt (value : Float) : String :=
  toString ((value * 100.0).round / 100.0)

private structure Point2 where
  x : Float
  y : Float

private def project (point : Vec3) : Point2 :=
  {
    x := 390.0 + 210.0 * (0.866 * point.x - 0.5 * point.y)
    y := 385.0 + 120.0 * (0.5 * point.x + 0.866 * point.y) - 150.0 * point.z
  }

private def signColor (value : Float) : String :=
  if value < 0.0 then "#38bdf8" else "#f59e0b"

private def dominantSignedComponent (vector : Vec3) : Float :=
  let best := if Float.abs vector.x >= Float.abs vector.y then vector.x else vector.y
  if Float.abs best >= Float.abs vector.z then best else vector.z

private def normalized (vector : Vec3) : Vec3 :=
  let length := vector.norm
  if length < 1e-8 then default else Vec3.smul (1.0 / length) vector

private def line (className : String) (start finish : Point2) (color : String)
    (width : Float) (marker : String := "") : String :=
  let markerAttr := if marker.isEmpty then "" else s!" marker-end=\"url(#{marker})\""
  s!"<line class=\"{className}\" x1=\"{fmt start.x}\" y1=\"{fmt start.y}\" " ++
    s!"x2=\"{fmt finish.x}\" y2=\"{fmt finish.y}\" stroke=\"{color}\" " ++
    s!"stroke-width=\"{fmt width}\" stroke-linecap=\"round\"{markerAttr}/>"

private def sampleGlyph (index : Nat) (sample : Sample3) : String :=
  let center := project sample.position
  let value := sample.value
  let vectorMagnitude := value.vector.norm
  let vectorLength := 0.11 + 0.22 * clamp (vectorMagnitude / 1.8) 0.0 1.0
  let vectorTip :=
    project (sample.position.add (Vec3.smul vectorLength (normalized value.vector)))
  let bivectorMagnitude := value.bivectorNormal.norm
  let normalLength := 0.09 + 0.16 * clamp (bivectorMagnitude / 2.4) 0.0 1.0
  let normalTip :=
    project (sample.position.add (Vec3.smul normalLength (normalized value.bivectorNormal)))
  let scalarRadius := 2.8 + 5.0 * clamp (Float.abs value.scalar / 0.35) 0.0 1.0
  let planeRadius := 5.0 + 9.0 * clamp (bivectorMagnitude / 2.4) 0.0 1.0
  let planeAngle :=
    Float.atan2 value.bivectorNormal.y value.bivectorNormal.x * 57.295779513
  let volumeRadius :=
    7.0 + 10.0 * clamp (Float.abs value.pseudoscalar / 0.2) 0.0 1.0
  let title :=
    s!"sample {index}: g0={value.scalar}; " ++
      s!"g1=({value.vector.x},{value.vector.y},{value.vector.z}); " ++
      s!"g2=({value.bivectorNormal.x},{value.bivectorNormal.y},{value.bivectorNormal.z}); " ++
      s!"g3={value.pseudoscalar}"
  let volume :=
    if Float.abs value.pseudoscalar < 1e-8 then "" else
      s!"<circle cx=\"{fmt center.x}\" cy=\"{fmt center.y}\" r=\"{fmt volumeRadius}\" " ++
        s!"fill=\"none\" stroke=\"{signColor value.pseudoscalar}\" stroke-width=\"2\" " ++
        "stroke-opacity=\"0.62\" stroke-dasharray=\"4 3\"/>"
  let plane :=
    if bivectorMagnitude < 1e-8 then "" else
      let color := signColor (dominantSignedComponent value.bivectorNormal)
      s!"<ellipse cx=\"{fmt center.x}\" cy=\"{fmt center.y}\" rx=\"{fmt planeRadius}\" " ++
        s!"ry=\"4\" transform=\"rotate({fmt planeAngle} {fmt center.x} {fmt center.y})\" " ++
        s!"fill=\"{color}\" fill-opacity=\"0.22\" stroke=\"{color}\"/>" ++
        line "grade-two-normal" center normalTip color 1.3 "arrow-orange"
  let vector :=
    if vectorMagnitude < 1e-8 then "" else
      line "grade-one-vector" center vectorTip "#a78bfa" 2.1 "arrow-purple"
  let scalar :=
    if Float.abs value.scalar < 1e-8 then "" else
      s!"<circle cx=\"{fmt center.x}\" cy=\"{fmt center.y}\" r=\"{fmt scalarRadius}\" " ++
        s!"fill=\"{signColor value.scalar}\" stroke=\"#f8fafc\" stroke-width=\"0.8\"/>"
  s!"<g><title>{title}</title>{volume}{plane}{vector}{scalar}</g>"

private def gridSvg : String :=
  let values : List Float := [-1.0, -0.5, 0.0, 0.5, 1.0]
  let vertical := values.map fun x =>
    line "grid" (project { x, y := -1.0, z := 0.0 })
      (project { x, y := 1.0, z := 0.0 })
      (if Float.abs x < 1e-8 then "#64748b" else "#334155")
      (if Float.abs x < 1e-8 then 1.5 else 1.0)
  let horizontal := values.map fun y =>
    line "grid" (project { x := -1.0, y, z := 0.0 })
      (project { x := 1.0, y, z := 0.0 })
      (if Float.abs y < 1e-8 then "#64748b" else "#334155")
      (if Float.abs y < 1e-8 then 1.5 else 1.0)
  String.intercalate "\n" (vertical ++ horizontal)

private def legendItem (y : Nat) (color label detail : String) : String :=
  s!"<circle cx=\"846\" cy=\"{y}\" r=\"7\" fill=\"{color}\"/>" ++
    s!"<text x=\"864\" y=\"{y + 5}\" class=\"legend-label\">{label}</text>" ++
    s!"<text x=\"846\" y=\"{y + 25}\" class=\"legend-detail\">{detail}</text>"

/-- Render the first frame of a validated scene as an offline SVG backup. -/
def fallbackSvg (props : MultivectorFieldProps) : Except String String := do
  props.validate
  let frame := props.frames[0]!
  let glyphs := String.intercalate "\n" <|
    (Array.range frame.samples.size).toList.map fun index =>
      sampleGlyph index frame.samples[index]!
  return s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1100\" height=\"760\" " ++
    "viewBox=\"0 0 1100 760\">\n" ++
    "<defs>\n" ++
    "<marker id=\"arrow-purple\" markerWidth=\"7\" markerHeight=\"7\" refX=\"6\" refY=\"3.5\" orient=\"auto\"><path d=\"M0,0 L0,7 L7,3.5 z\" fill=\"#a78bfa\"/></marker>\n" ++
    "<marker id=\"arrow-orange\" markerWidth=\"6\" markerHeight=\"6\" refX=\"5\" refY=\"3\" orient=\"auto\"><path d=\"M0,0 L0,6 L6,3 z\" fill=\"#f59e0b\"/></marker>\n" ++
    "<style>.title{font:700 27px system-ui,sans-serif;fill:#f8fafc}.subtitle{font:16px system-ui,sans-serif;fill:#94a3b8}.formula{font:15px ui-monospace,monospace;fill:#c4b5fd}.legend-label{font:700 16px system-ui,sans-serif;fill:#f8fafc}.legend-detail{font:14px system-ui,sans-serif;fill:#94a3b8}.footer{font:14px system-ui,sans-serif;fill:#94a3b8}</style>\n" ++
    "</defs>\n" ++
    "<rect width=\"1100\" height=\"760\" rx=\"18\" fill=\"#0f172a\"/>\n" ++
    "<rect x=\"24\" y=\"126\" width=\"760\" height=\"560\" rx=\"13\" fill=\"#0b1120\" stroke=\"#334155\"/>\n" ++
    s!"<text x=\"30\" y=\"45\" class=\"title\">{props.title}</text>\n" ++
    "<text x=\"30\" y=\"72\" class=\"subtitle\">offline fallback · frame 1 / 24 · 25 Lean-computed samples</text>\n" ++
    s!"<text x=\"30\" y=\"103\" class=\"formula\">{props.formula}</text>\n" ++
    gridSvg ++ "\n" ++ glyphs ++ "\n" ++
    "<text x=\"822\" y=\"155\" class=\"legend-label\">Four grades, one value</text>\n" ++
    legendItem 195 "#f59e0b" "grade 0 · scalar" "signed dot contribution" ++ "\n" ++
    legendItem 270 "#a78bfa" "grade 1 · vector" "direction arrow" ++ "\n" ++
    legendItem 345 "#f59e0b" "grade 2 · plane" "disk + dual normal" ++ "\n" ++
    legendItem 420 "#38bdf8" "grade 3 · volume" "signed pseudoscalar halo" ++ "\n" ++
    "<rect x=\"812\" y=\"492\" width=\"260\" height=\"145\" rx=\"11\" fill=\"#111827\" stroke=\"#334155\"/>\n" ++
    "<text x=\"832\" y=\"523\" class=\"legend-label\">Ownership</text>\n" ++
    "<text x=\"832\" y=\"552\" class=\"legend-detail\">Lean computed every position,</text>\n" ++
    "<text x=\"832\" y=\"575\" class=\"legend-detail\">Clifford product, rotor frame,</text>\n" ++
    "<text x=\"832\" y=\"598\" class=\"legend-detail\">and grade coefficient.</text>\n" ++
    "<text x=\"30\" y=\"724\" class=\"footer\">Lean Float runtime evidence, not a formal proof. Interactive orbit, toggles, scrubbing, and inspection live in the InfoView version.</text>\n" ++
    "</svg>\n"

/-- Generate the checked-in backup from the same default scene as the widget. -/
def defaultFallbackSvg : Except String String :=
  defaultScene >>= fallbackSvg

end GrassmannViz
