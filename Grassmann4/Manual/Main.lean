/-
  Manual/Main.lean - Documentation generator using Verso

  This generates the HTML documentation for the Grassmann library.
-/
import VersoManual
import Manual.Basic

open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := true
  emitHtmlMulti := true
  htmlDepth := 2

def main := manualMain (%doc Manual.Basic) (config := config)
