import GrassmannViz.FallbackSvg

open GrassmannViz

def main : IO Unit := do
  let svg ← IO.ofExcept defaultFallbackSvg
  let output := "Grassmann4/docs/MultivectorFieldFallback.svg"
  IO.FS.writeFile output svg
  IO.println s!"wrote {output}"
