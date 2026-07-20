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
