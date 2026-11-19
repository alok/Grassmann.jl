/-
  Grassmann/Server/Main.lean — CLI entry point for `lake exe ga-server`
-/
import Grassmann.Server

open Grassmann.Server

private def parseArgs (args : List String) (cfg : ServerConfig) : IO (ServerConfig × Bool) := do
  match args with
  | [] => return (cfg, false)
  | "--self-test" :: _ => return (cfg, true)
  | "--host" :: h :: rest => parseArgs rest { cfg with host := h }
  | "--port" :: p :: rest =>
    match p.toNat? with
    | some n => parseArgs rest { cfg with port := n.toUInt16 }
    | none => throw (IO.userError s!"invalid --port value: {p}")
  | "--static" :: d :: rest => parseArgs rest { cfg with staticDir := some d }
  | "--help" :: _ | "-h" :: _ =>
    IO.println "Usage: ga-server [--host 127.0.0.1] [--port 8787] [--static <dir>] [--self-test]"
    IO.Process.exit 0
  | unknown :: _ =>
    throw (IO.userError s!"unknown argument: {unknown}")

def main (args : List String) : IO UInt32 := do
  let defaultStatic : Option String ← do
    if ← (System.FilePath.mk "web/dist").pathExists then pure (some "web/dist")
    else pure none
  let (cfg, selfTest) ← parseArgs args { staticDir := defaultStatic }
  if selfTest then
    runSelfTest
  else
    serve cfg
