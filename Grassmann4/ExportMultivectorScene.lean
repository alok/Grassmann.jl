import GrassmannViz

/-!
# Export the validated meetup scene

This small executable is the bridge from the reusable Lean visualization
library to a static web host. The browser receives the same JSON value as the
InfoView widget; it does not recompute the field or the Clifford products.
-/

open GrassmannViz Lean

private def usage : String :=
  "usage: lake exe multivectorscenejson -- OUTPUT.json"

def main (args : List String) : IO UInt32 := do
  let output? :=
    match args with
    | [output] => some output
    | ["--", output] => some output
    | _ => none
  match output? with
  | some output =>
      let props ← IO.ofExcept defaultScene
      let props ← IO.ofExcept props.prepareForWidget
      let path : System.FilePath := output
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path ((toJson props).pretty ++ "\n")
      IO.println s!"wrote {path}: {(← IO.ofExcept props.summary)}"
      return 0
  | none =>
      IO.eprintln usage
      return 2
