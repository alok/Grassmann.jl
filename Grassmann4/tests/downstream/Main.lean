import Grassmann
import GrassmannReference
import GrassmannFields
import GrassmannViz
import GrassmannTests

/-!
This executable deliberately imports only the five public library roots. It is
compiled as a separate Lake package, so a passing build detects accidental
reliance on the Grassmann repository's private source layout.
-/

def main : IO Unit := do
  match GrassmannViz.defaultScene with
  | .error message => throw <| IO.userError message
  | .ok scene =>
      match scene.summary with
      | .error message => throw <| IO.userError message
      | .ok summary => IO.println s!"Grassmann downstream smoke: {summary}"
