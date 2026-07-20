import GrassmannFields
set_option linter.hashCommand false

/-!
# Lean as an ordinary programming language

This is the beginner-safe half of the SF Lean demo. Move the cursor through
the commands from top to bottom. The only live edit is `xCount := 3` to
`xCount := 4`; the successful result changes from 9 samples to 12.
-/

open GrassmannFields

/-- An ordinary configuration record for a small rectangular grid. -/
def tinyGrid : PlanarGrid := {
  xMin := -1.0
  xMax := 1.0
  yMin := -1.0
  yMax := 1.0
  z := 0.0
  xCount := 3
  yCount := 3
}

#eval tinyGrid

/-- An ordinary function from a point to four semantic grade values. -/
def swirlField (point : Vec3) : R3Grades := {
  scalar := point.x * point.y
  vector := { x := -point.y, y := point.x, z := 0.25 }
  bivectorNormal := { x := 0.0, y := 0.0, z := point.x - point.y }
  pseudoscalar := 0.1 * (point.x + point.y)
}

#check swirlField

#eval swirlField { x := 1.0, y := 0.5, z := 0.0 }

/-- Sampling is an ordinary array-producing program with explicit errors. -/
def sampleCount (grid : PlanarGrid) : Except String Nat := do
  let samples ← samplePlanar grid swirlField
  return samples.size

#eval sampleCount tinyGrid

-- Invalid input is data too: no exception escapes and no widget is involved.
#eval sampleCount { tinyGrid with xCount := 1 }
