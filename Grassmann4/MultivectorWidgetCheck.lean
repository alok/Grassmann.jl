import GrassmannViz.InfoView

/-!
# Embedded renderer freshness check

The `GrassmannViz` Lake target tracks the JavaScript asset as an input. This
independent executable check still detects an OLean built from stale renderer
source before a live demonstration.
-/

open GrassmannViz

#eval do
  let localPath : System.FilePath := "GrassmannViz/multivectorField.js"
  let outerPath : System.FilePath := "Grassmann4/GrassmannViz/multivectorField.js"
  let localExists ← (System.FilePath.pathExists localPath).toIO
  let rendererPath ←
    if localExists then pure localPath else pure outerPath
  let renderer ← IO.FS.readFile rendererPath
  if renderer == MultivectorFieldWidget.javascript then
    IO.println "embedded multivector renderer matches its JavaScript source"
  else
    throw <| IO.userError
      "stale multivector renderer: from Grassmann4 run \
      `LAKE_ARTIFACT_CACHE=false lake build +GrassmannViz.InfoView`, then rerun this check"
