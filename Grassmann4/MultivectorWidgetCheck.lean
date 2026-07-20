import GrassmannViz.InfoView

/-!
# Embedded renderer freshness check

Lake does not track an `include_str` JavaScript asset as a Lean module input.
This executable check detects an OLean built from stale renderer source.
-/

open GrassmannViz

#eval do
  let renderer ← IO.FS.readFile "Grassmann4/GrassmannViz/multivectorField.js"
  if renderer == MultivectorFieldWidget.javascript then
    IO.println "embedded multivector renderer matches its JavaScript source"
  else
    throw <| IO.userError
      "stale multivector renderer: run `touch Grassmann4/GrassmannViz/InfoView.lean && \
      LAKE_ARTIFACT_CACHE=false lake build +GrassmannViz.InfoView`, then rerun this check"
