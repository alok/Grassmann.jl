import GrassmannViz.InfoView

/-!
# Embedded renderer freshness check

Lake does not track an `include_str` JavaScript asset as a Lean module input.
This executable check detects an OLean built from stale renderer source.
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
      "stale multivector renderer: from Grassmann4 run `sleep 1 && touch GrassmannViz/InfoView.lean && \
      LAKE_ARTIFACT_CACHE=false lake build +GrassmannViz.InfoView`, then rerun this check"
