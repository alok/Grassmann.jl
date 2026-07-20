import GrassmannViz.FallbackSvg

open GrassmannViz

private def sourceRoot : IO System.FilePath := do
  if ← System.FilePath.pathExists "GrassmannViz" then
    return "."
  if ← System.FilePath.pathExists "Grassmann4/GrassmannViz" then
    return "Grassmann4"
  throw <| IO.userError "run this executable from the outer or Grassmann4 package root"

def main : IO Unit := do
  let svg ← IO.ofExcept defaultFallbackSvg
  let output := (← sourceRoot) / "docs" / "MultivectorFieldFallback.svg"
  IO.FS.writeFile output svg
  IO.println s!"wrote {output}"
