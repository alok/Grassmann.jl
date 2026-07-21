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

-- Two small points to explain before the full field.
def originExample : Vec3 := { x := 0.0, y := 0.0, z := 0.0 }
def e1Example : Vec3 := { x := 1.0, y := 0.0, z := 0.0 }

-- At the origin, p*v and tau*I vanish: only the vector v remains.
#eval R3Grades.ofMV (fieldAt 0.0 originExample)

-- At p=e1, e1*e1 contributes a scalar and e1*e2 contributes the e12 plane.
#eval R3Grades.ofMV (fieldAt 0.0 e1Example)

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
