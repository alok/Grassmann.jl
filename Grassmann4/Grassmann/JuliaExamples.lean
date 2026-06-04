/-
  Grassmann/JuliaExamples.lean

  Standalone visual generators for the plot-producing Grassmann.jl examples in
  docs/src/algebra.md. These emit deterministic SVG artifacts that are easy to
  compare against the canonical Julia/Makie reference images.
-/

namespace Grassmann.JuliaExamples

def pi : Float := 3.14159265358979323846

abbrev Vec2 := Prod Float Float

structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

namespace Vec2

@[inline] def add (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)
@[inline] def smul (s : Float) (v : Vec2) : Vec2 := (s * v.1, s * v.2)
@[inline] def norm (v : Vec2) : Float := Float.sqrt (v.1 * v.1 + v.2 * v.2)

@[inline] def normalized (v : Vec2) : Vec2 :=
  let n := norm v
  if n < 1e-9 then (0.0, 0.0) else smul (1.0 / n) v

end Vec2

namespace Vec3

@[inline] def add (a b : Vec3) : Vec3 := { x := a.x + b.x, y := a.y + b.y, z := a.z + b.z }
@[inline] def smul (s : Float) (v : Vec3) : Vec3 := { x := s * v.x, y := s * v.y, z := s * v.z }

@[inline] def norm (v : Vec3) : Float :=
  Float.sqrt (v.x * v.x + v.y * v.y + v.z * v.z)

@[inline] def normalized (v : Vec3) : Vec3 :=
  let n := norm v
  if n < 1e-9 then { x := 0.0, y := 0.0, z := 0.0 } else smul (1.0 / n) v

end Vec3

@[inline] def fmin (a b : Float) : Float := if a <= b then a else b
@[inline] def fmax (a b : Float) : Float := if a >= b then a else b

def fmt (x : Float) : String :=
  let y := (x * 1000.0).round / 1000.0
  let y := if Float.abs y < 0.0005 then 0.0 else y
  toString y

def cosh (x : Float) : Float := (Float.exp x + Float.exp (-x)) / 2.0
def sinh (x : Float) : Float := (Float.exp x - Float.exp (-x)) / 2.0

def svgOpen (width height : Nat) : String :=
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" viewBox=\"0 0 {width} {height}\">\n" ++
  "  <rect width=\"100%\" height=\"100%\" fill=\"#ffffff\"/>\n"

def arrowDef : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow\" markerWidth=\"6\" markerHeight=\"6\" refX=\"5\" refY=\"3\" orient=\"auto\" markerUnits=\"strokeWidth\">\n" ++
  "      <path d=\"M0,0 L0,6 L5,3 z\" fill=\"#8a8a8a\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def map2D (width height : Nat) (range : Float) (p : Vec2) : Vec2 :=
  let margin := 20.0
  let w := width.toFloat - 2.0 * margin
  let h := height.toFloat - 2.0 * margin
  (margin + ((p.1 + range) / (2.0 * range)) * w,
   margin + ((range - p.2) / (2.0 * range)) * h)

def inRange2D (range : Float) (p : Vec2) : Bool :=
  Float.abs p.1 <= range && Float.abs p.2 <= range

partial def integrate2D (field : Vec2 -> Vec2) (range h : Float) (steps : Nat) (p : Vec2) :
    List Vec2 :=
  match steps with
  | 0 => [p]
  | Nat.succ n =>
      let v := Vec2.normalized (field p)
      let p' := Vec2.add p (Vec2.smul h v)
      if inRange2D range p' && Vec2.norm v > 1e-9 then
        p :: integrate2D field range h n p'
      else
        [p]

def path2D (width height : Nat) (range : Float) (pts : List Vec2) : String :=
  match pts with
  | [] => ""
  | p :: rest =>
      let p0 := map2D width height range p
      let start := s!"M {fmt p0.1} {fmt p0.2}"
      rest.foldl
        (fun acc q =>
          let qp := map2D width height range q
          acc ++ s!" L {fmt qp.1} {fmt qp.2}")
        start

def streamPath2D (field : Vec2 -> Vec2) (width height : Nat) (range : Float) (seed : Vec2) :
    String :=
  let backward := (integrate2D field range (-0.055) 58 seed).reverse
  let forward := integrate2D field range 0.055 58 seed
  let pts := backward ++ forward.drop 1
  let d := path2D width height range pts
  if d.isEmpty then ""
  else
    s!"  <path d=\"{d}\" fill=\"none\" stroke=\"#6f6f6f\" stroke-width=\"0.82\" stroke-opacity=\"0.38\"/>\n"

def arrowGlyph2D (field : Vec2 -> Vec2) (width height : Nat) (range : Float) (seed : Vec2) :
    String :=
  let v := Vec2.normalized (field seed)
  if Vec2.norm v < 1e-9 then ""
  else
    let p := map2D width height range seed
    let len := 8.0
    let dx := len * v.1
    let dy := -len * v.2
    let x1 := p.1 - 0.5 * dx
    let y1 := p.2 - 0.5 * dy
    let x2 := p.1 + 0.5 * dx
    let y2 := p.2 + 0.5 * dy
    s!"  <line x1=\"{fmt x1}\" y1=\"{fmt y1}\" x2=\"{fmt x2}\" y2=\"{fmt y2}\" stroke=\"#808080\" stroke-width=\"0.65\" stroke-opacity=\"0.34\" marker-end=\"url(#arrow)\"/>\n"

def seeds2D (count : Nat) (range : Float) : List Vec2 :=
  let step := 2.0 * range / (count.toFloat - 1.0)
  (List.range count).flatMap fun i =>
    (List.range count).map fun j =>
      (-range + i.toFloat * step, -range + j.toFloat * step)

def streamPlot2D (field : Vec2 -> Vec2) : String :=
  let width := 410
  let height := 410
  let range := 1.5
  let lines := String.join ((seeds2D 13 range).map (streamPath2D field width height range))
  let arrows := String.join ((seeds2D 17 range).map (arrowGlyph2D field width height range))
  svgOpen width height ++ arrowDef ++ lines ++ arrows ++ "</svg>\n"

def rotateField (theta : Float) (p : Vec2) : Vec2 :=
  let c := Float.cos theta
  let s := Float.sin theta
  (c * p.1 - s * p.2, s * p.1 + c * p.2)

def reflectAfterRotateField (theta : Float) (p : Vec2) : Vec2 :=
  let q := rotateField theta p
  (q.1, -q.2)

def boostField (beta : Float) (p : Vec2) : Vec2 :=
  let c := cosh beta
  let s := sinh beta
  (c * p.1 + s * p.2, s * p.1 + c * p.2)

def reflectAfterBoostField (beta : Float) (p : Vec2) : Vec2 :=
  let q := boostField beta p
  (q.1, -q.2)

def planeExamples : List (Prod String String) :=
  [ ("plane-1.svg", streamPlot2D (rotateField pi)),
    ("plane-2.svg", streamPlot2D (rotateField (pi / 2.0))),
    ("plane-3.svg", streamPlot2D (rotateField (pi / 4.0))),
    ("plane-4.svg", streamPlot2D (reflectAfterRotateField (pi / 4.0))),
    ("plane-5.svg", streamPlot2D (boostField (pi / 8.0))),
    ("plane-6.svg", streamPlot2D (reflectAfterBoostField (pi / 4.0))) ]

def project3D (p : Vec3) : Vec2 :=
  let u := 0.86 * p.x - 0.42 * p.y
  let v := -0.24 * p.x - 0.20 * p.y - 0.72 * p.z
  (u, v)

def mapProjected (width height : Nat) (scale : Float) (offset : Vec2) (p : Vec3) : Vec2 :=
  let q := project3D p
  (width.toFloat / 2.0 + offset.1 + scale * q.1,
   height.toFloat / 2.0 + offset.2 + scale * q.2)

def path3D (width height : Nat) (scale : Float) (offset : Vec2) (pts : List Vec3) : String :=
  match pts with
  | [] => ""
  | p :: rest =>
      let p0 := mapProjected width height scale offset p
      let start := s!"M {fmt p0.1} {fmt p0.2}"
      rest.foldl
        (fun acc q =>
          let qp := mapProjected width height scale offset q
          acc ++ s!" L {fmt qp.1} {fmt qp.2}")
        start

def grid3D (width height : Nat) (scale : Float) (offset : Vec2) (range : Float := 2.0) : String :=
  let ticks := [-range, -range / 2.0, 0.0, range / 2.0, range]
  let planeLines := ticks.foldl (init := "") fun acc t =>
    let xLine := path3D width height scale offset
      [{ x := -range, y := t, z := -range }, { x := range, y := t, z := -range }]
    let yLine := path3D width height scale offset
      [{ x := t, y := -range, z := -range }, { x := t, y := range, z := -range }]
    acc ++ s!"  <path d=\"{xLine}\" fill=\"none\" stroke=\"#eeeeee\" stroke-width=\"0.85\"/>\n" ++
      s!"  <path d=\"{yLine}\" fill=\"none\" stroke=\"#eeeeee\" stroke-width=\"0.85\"/>\n"
  let xAxis := path3D width height scale offset
    [{ x := -range, y := 0.0, z := -range }, { x := range, y := 0.0, z := -range }]
  let yAxis := path3D width height scale offset
    [{ x := 0.0, y := -range, z := -range }, { x := 0.0, y := range, z := -range }]
  let zAxis := path3D width height scale offset
    [{ x := 0.0, y := 0.0, z := -range }, { x := 0.0, y := 0.0, z := range }]
  planeLines ++
    s!"  <path d=\"{xAxis}\" fill=\"none\" stroke=\"#8c8c8c\" stroke-width=\"0.9\"/>\n" ++
    s!"  <path d=\"{yAxis}\" fill=\"none\" stroke=\"#8c8c8c\" stroke-width=\"0.9\"/>\n" ++
    s!"  <path d=\"{zAxis}\" fill=\"none\" stroke=\"#8c8c8c\" stroke-width=\"0.9\"/>\n"

def curveSvg3D (pts : List Vec3) (width height : Nat) (scale : Float) (offset : Vec2)
    (gridRange : Float := 2.0) : String :=
  let curve := path3D width height scale offset pts
  svgOpen width height ++
    grid3D width height scale offset gridRange ++
    s!"  <path d=\"{curve}\" fill=\"none\" stroke=\"#6b6b6b\" stroke-width=\"1.15\" stroke-opacity=\"0.78\" stroke-linecap=\"round\" stroke-linejoin=\"round\"/>\n" ++
    "</svg>\n"

def sampleCurve (samples : Nat) (t0 t1 : Float) (f : Float -> Vec3) : List Vec3 :=
  (List.range samples).map fun i =>
    let denom := fmax 1.0 (samples - 1).toFloat
    let t := t0 + (t1 - t0) * i.toFloat / denom
    f t

def torusPoint (t : Float) : Vec3 :=
  let major := 1.05
  let minor := 0.55
  let p := 3.0 * t
  let q := 7.0 * t
  { x := (major + minor * Float.cos q) * Float.cos p,
    y := (major + minor * Float.cos q) * Float.sin p,
    z := minor * Float.sin q }

def helixPoint (t : Float) : Vec3 :=
  { x := Float.cos (3.0 * t), y := Float.sin (3.0 * t), z := 0.16 * t }

def translationVector (t : Float) : Vec3 :=
  { x := 3.0 * Float.sin (3.0 * t),
    y := 7.0 * Float.cos (2.0 * t),
    z := -4.0 * Float.sin (5.0 * t) }

def orbit2Point (t : Float) : Vec3 :=
  let a := translationVector t
  { x := 1.0 + t * a.x, y := 1.0 + t * a.y, z := -1.0 + t * a.z }

def rotateZ (theta : Float) (p : Vec3) : Vec3 :=
  let c := Float.cos theta
  let s := Float.sin theta
  { x := c * p.x - s * p.y, y := s * p.x + c * p.y, z := p.z }

def orbit4Point (t : Float) : Vec3 :=
  let a := translationVector t
  let translated := { x := 1.0 + 0.07 * t * a.x,
                      y := 1.0 + 0.07 * t * a.y,
                      z := -1.0 + 0.07 * t * a.z }
  rotateZ t translated

def curveExamples : List (Prod String String) :=
  [ ("torus.svg", curveSvg3D (sampleCurve 1800 (-2.0 * pi) (2.0 * pi) torusPoint) 360 250 86.0 (0.0, 0.0) 1.8),
    ("helix.svg", curveSvg3D (sampleCurve 1200 (-2.0 * pi) (2.0 * pi) helixPoint) 360 250 84.0 (0.0, 0.0) 1.8),
    ("orbit-2.svg", curveSvg3D (sampleCurve 1800 (-2.0 * pi) (2.0 * pi) orbit2Point) 510 550 14.0 (20.0, 15.0) 8.0),
    ("orbit-4.svg", curveSvg3D (sampleCurve 1600 (-2.0 * pi) (2.0 * pi) orbit4Point) 680 395 78.0 (0.0, 10.0) 2.0) ]

def inRange3D (range : Float) (p : Vec3) : Bool :=
  Float.abs p.x <= range && Float.abs p.y <= range && Float.abs p.z <= range

partial def integrate3D (field : Vec3 -> Vec3) (range h : Float) (steps : Nat) (p : Vec3) :
    List Vec3 :=
  match steps with
  | 0 => [p]
  | Nat.succ n =>
      let v := Vec3.normalized (field p)
      let p' := Vec3.add p (Vec3.smul h v)
      if inRange3D range p' && Vec3.norm v > 1e-9 then
        p :: integrate3D field range h n p'
      else
        [p]

def streamPath3D (field : Vec3 -> Vec3) (width height : Nat) (scale : Float) (offset : Vec2)
    (range : Float) (seed : Vec3) : String :=
  let backward := (integrate3D field range (-0.085) 60 seed).reverse
  let forward := integrate3D field range 0.085 60 seed
  let pts := backward ++ forward.drop 1
  let d := path3D width height scale offset pts
  if d.isEmpty then ""
  else
    s!"  <path d=\"{d}\" fill=\"none\" stroke=\"#595959\" stroke-width=\"0.8\" stroke-opacity=\"0.36\" stroke-linecap=\"round\"/>\n"

def seeds3D (countXY countZ : Nat) (range : Float) : List Vec3 :=
  let stepXY := 2.0 * range / (countXY.toFloat - 1.0)
  let stepZ := 2.0 * range / (countZ.toFloat - 1.0)
  (List.range countXY).flatMap fun i =>
    (List.range countXY).flatMap fun j =>
      (List.range countZ).map fun k =>
        { x := -range + i.toFloat * stepXY,
          y := -range + j.toFloat * stepXY,
          z := -range + k.toFloat * stepZ }

def orbField (p : Vec3) : Vec3 :=
  { x := -0.85 * p.y + 0.28 * p.z,
    y := 0.85 * p.x + 0.18 * Float.sin (2.0 * p.z),
    z := 0.42 + 0.22 * p.x - 0.10 * p.z }

def waveField (p : Vec3) : Vec3 :=
  { x := -0.55 * p.y + 0.42 * Float.sin (p.z + p.x),
    y := 0.72 * p.x + 0.28 * Float.cos (p.z - p.y),
    z := 0.52 * Float.sin p.x + 0.36 * Float.cos p.y }

def streamSvg3D (field : Vec3 -> Vec3) (width height : Nat) (scale : Float) (offset : Vec2)
    (range gridRange : Float) : String :=
  let paths := String.join ((seeds3D 7 5 range).map
    (streamPath3D field width height scale offset range))
  svgOpen width height ++
    grid3D width height scale offset gridRange ++
    paths ++
    "</svg>\n"

def vectorFieldExamples : List (Prod String String) :=
  [ ("orb.svg", streamSvg3D orbField 515 515 92.0 (0.0, 35.0) 1.5 1.7),
    ("wave.svg", streamSvg3D waveField 515 515 92.0 (0.0, 35.0) 1.5 1.7) ]

def allExamples : List (Prod String String) :=
  planeExamples ++ curveExamples ++ vectorFieldExamples

def comparisonRoot : System.FilePath := ".generated" / "julia-examples"

def outputDir : System.FilePath := comparisonRoot / "lean"

def juliaReferenceBase : String :=
  "https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/"

def referenceName (filename : String) : String :=
  match filename with
  | "plane-1.svg" => "plane-1"
  | "plane-2.svg" => "plane-2"
  | "plane-3.svg" => "plane-3"
  | "plane-4.svg" => "plane-4"
  | "plane-5.svg" => "plane-5"
  | "plane-6.svg" => "plane-6"
  | "torus.svg" => "torus"
  | "helix.svg" => "helix"
  | "orbit-2.svg" => "orbit-2"
  | "orbit-4.svg" => "orbit-4"
  | "orb.svg" => "orb"
  | "wave.svg" => "wave"
  | other => other

def juliaReferenceUrl (filename : String) : String :=
  juliaReferenceBase ++ referenceName filename ++ ".png"

def joinWith (sep : String) : List String -> String
  | [] => ""
  | x :: xs => xs.foldl (fun acc y => acc ++ sep ++ y) x

def manifestEntry (ex : Prod String String) : String :=
  let name := ex.1
  "    {\"name\":\"" ++ referenceName name ++
    "\",\"lean\":\"lean/" ++ name ++
    "\",\"julia\":\"" ++ juliaReferenceUrl name ++ "\"}"

def manifestJson : String :=
  "{\n" ++
  "  \"source\":\"Grassmann.jl docs/src/algebra.md plot examples\",\n" ++
  "  \"examples\":[\n" ++
  joinWith ",\n" (allExamples.map manifestEntry) ++ "\n" ++
  "  ]\n" ++
  "}\n"

def comparisonCard (ex : Prod String String) : String :=
  let name := ex.1
  let label := referenceName name
  let leanPath := "lean/" ++ name
  let juliaUrl := juliaReferenceUrl name
  "    <section class=\"example\">\n" ++
  s!"      <h2>{label}</h2>\n" ++
  "      <div class=\"frames\">\n" ++
  "        <figure>\n" ++
  s!"          <img src=\"{leanPath}\" alt=\"Lean generated {label}\" />\n" ++
  "          <figcaption>Lean SVG</figcaption>\n" ++
  "        </figure>\n" ++
  "        <figure>\n" ++
  s!"          <img src=\"{juliaUrl}\" alt=\"Julia reference {label}\" />\n" ++
  "          <figcaption>Julia/Makie PNG</figcaption>\n" ++
  "        </figure>\n" ++
  "      </div>\n" ++
  "    </section>\n"

def comparisonHtml : String :=
  "<!doctype html>\n" ++
  "<html lang=\"en\">\n" ++
  "<head>\n" ++
  "  <meta charset=\"utf-8\" />\n" ++
  "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />\n" ++
  "  <link rel=\"icon\" href=\"data:,\" />\n" ++
  "  <title>Grassmann.jl Examples: Lean Comparison</title>\n" ++
  "  <style>\n" ++
  "    :root { color-scheme: light; font-family: Inter, Helvetica, Arial, sans-serif; }\n" ++
  "    body { margin: 0; background: #f5f5f4; color: #202020; }\n" ++
  "    main { max-width: 1180px; margin: 0 auto; padding: 24px; }\n" ++
  "    h1 { font-size: 24px; font-weight: 650; margin: 0 0 6px; }\n" ++
  "    p { margin: 0 0 18px; color: #555; line-height: 1.45; }\n" ++
  "    .example { border-top: 1px solid #d7d7d4; padding: 18px 0 24px; }\n" ++
  "    h2 { font-size: 16px; font-weight: 650; margin: 0 0 12px; }\n" ++
  "    .frames { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 16px; }\n" ++
  "    figure { margin: 0; background: #fff; border: 1px solid #d8d8d5; padding: 10px; }\n" ++
  "    img { display: block; width: 100%; height: 360px; object-fit: contain; background: #fff; }\n" ++
  "    figcaption { margin-top: 8px; font-size: 12px; color: #666; }\n" ++
  "    @media (max-width: 760px) { .frames { grid-template-columns: 1fr; } }\n" ++
  "  </style>\n" ++
  "</head>\n" ++
  "<body>\n" ++
  "  <main>\n" ++
  "    <h1>Grassmann.jl Plot Examples: Lean Comparison</h1>\n" ++
  "    <p>Lean-generated SVGs are paired with canonical Grassmann.jl/Makie PNGs.</p>\n" ++
  joinWith "" (allExamples.map comparisonCard) ++
  "  </main>\n" ++
  "</body>\n" ++
  "</html>\n"

def writeAll : IO Unit := do
  let manifestPath := comparisonRoot / "manifest.json"
  let indexPath := comparisonRoot / "index.html"
  IO.FS.createDirAll outputDir
  for (name, body) in allExamples do
    IO.FS.writeFile (outputDir / name) body
  IO.FS.writeFile manifestPath manifestJson
  IO.FS.writeFile indexPath comparisonHtml
  IO.println s!"wrote {allExamples.length} Lean visualizations to {outputDir}"
  IO.println s!"wrote comparison index to {indexPath}"

end Grassmann.JuliaExamples
