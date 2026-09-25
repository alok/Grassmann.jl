import Gallery.Check

/-! `lake test` driver of the gallery package: the figure data checks of `Gallery.Check`. -/

/-- Run `Gallery.Check.run` (repository root `..` or `--root DIR`); exit 1 on a failure. -/
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := match args with
    | "--root" :: r :: _ => r
    | _ => ".."
  let (pass, fail) ← Gallery.Check.run root
  IO.println s!"gallery: {pass} checks passed, {fail} failed"
  return if fail == 0 then 0 else 1
