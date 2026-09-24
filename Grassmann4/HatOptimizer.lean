-- HatOptimizer.lean - Cowboy hat optimization executable
--
-- Runs the variational optimization and emits a JSON animation sequence.
--
-- Usage:
--   cd ~/grassmann && lake exe hat > hat_animation.json
--   cd ~/grassmann && lake exe hat -- dress > hat_animation_dress.json
--   cd ~/grassmann && lake exe hat -- working > hat_animation_working.json

import Grassmann.CowboyHatOpt

def main (args : List String) : IO Unit := do
  -- Select parameter set from command-line argument
  let params : CowboyHatOpt.HatParams :=
    match args with
    | ["dress"]   => CowboyHatOpt.dressParams
    | ["working"] => CowboyHatOpt.workingParams
    | _           => CowboyHatOpt.defaultParams
  -- Run optimization (progress printed to stderr)
  let frames ← CowboyHatOpt.runOptimization params
  -- Emit JSON animation to stdout
  IO.println (CowboyHatOpt.animationJson params frames)
