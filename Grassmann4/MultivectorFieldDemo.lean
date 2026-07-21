import GrassmannViz
set_option linter.hashCommand false
/-!
# SF Lean meetup stage anchor

Move the cursor between the executable summary and `#html` command. The safe
live edit is `xCount := 5` to `xCount := 6`; Lean recomputes every sample.
-/

open GrassmannFields GrassmannViz
open GrassmannFields.Examples.MixedRotor

-- The minimal dependent-typing story for the demo:
--   fieldAt : Float → Vec3 → MV R3 .full
--   rotor   : Float → MV R3 .even
#check fieldAt
#check rotor

/-- Small enough to recompute live, large enough to read from the room. -/
def stageGrid : PlanarGrid := {
  defaultGrid with
  xCount := 5
  yCount := 5
}

/-- Twenty-four Lean-computed frames over one rotor turn. -/
def stageScene : Except String MultivectorFieldProps :=
  defaultScene stageGrid 24

#eval stageScene.bind MultivectorFieldProps.summary

#html sceneResultHtml stageScene
