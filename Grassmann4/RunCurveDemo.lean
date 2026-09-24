-- RunCurveDemo.lean - Entry point for curve shortening demo executable
-- Uses standalone implementation to avoid SciLean build issues

import Grassmann.CurveShorteningStandalone

def main : IO Unit := CurveShortening.runAllDemos
