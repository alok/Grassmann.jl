# Downstream package smoke test

This fixture is an independent Lake package. It depends on the repository root
through Lake's public package boundary and imports all five supported library
roots without adding `Grassmann4` to `LEAN_PATH` or importing private files.

From this directory, run:

```bash
lake update
lake build
lake exe grassmann-downstream-smoke
```

The executable validates and summarizes the default Lean-computed multivector
scene. Its output should report 24 frames and 25 samples per frame.
