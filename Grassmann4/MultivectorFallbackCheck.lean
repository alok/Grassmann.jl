import GrassmannViz.FallbackSvg

open GrassmannViz

#eval do
  let expected ← IO.ofExcept defaultFallbackSvg
  let actual ← IO.FS.readFile "Grassmann4/docs/MultivectorFieldFallback.svg"
  if actual == expected then
    IO.println "checked-in fallback SVG matches the default Lean scene"
  else
    throw <| IO.userError
      "stale fallback SVG: run `lake exe multivectorfallback` before presenting"

  let smallGrid : GrassmannFields.PlanarGrid := {
    GrassmannFields.Examples.MixedRotor.defaultGrid with
    xCount := 3
    yCount := 2
  }
  let smallScene ← IO.ofExcept (defaultScene smallGrid 1)
  let escapedScene := {
    smallScene with
    title := "A < B & C"
    formula := "x > 0 & y < 1"
  }
  let smallSvg ← IO.ofExcept (fallbackSvg escapedScene)
  unless smallSvg.contains "frame 1 / 1 · 6 Lean-computed samples" do
    throw <| IO.userError "fallback SVG did not derive frame/sample counts from props"
  unless smallSvg.contains "A &lt; B &amp; C" &&
      smallSvg.contains "x &gt; 0 &amp; y &lt; 1" do
    throw <| IO.userError "fallback SVG did not XML-escape scene text"
  unless smallSvg.contains "<polygon points=" && smallSvg.contains "arrow-cool" do
    throw <| IO.userError "fallback SVG is missing projected planes or signed markers"
  IO.println "fallback SVG derives metadata, escapes text, and projects bivector planes"
