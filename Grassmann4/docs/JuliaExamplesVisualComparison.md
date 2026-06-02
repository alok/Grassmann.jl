# Grassmann.jl Plot Examples Visual Comparison

This note records the comparison harness for the plot-producing Julia examples in
`docs/src/algebra.md`.

## Regeneration

From the repository root:

```bash
lake exe jlexamples
```

This writes Lean-generated SVGs to:

```text
.generated/julia-examples/lean/
```

The same executable is also available from the nested Lean package:

```bash
cd Grassmann4
lake exe jlexamples
```

Nested runs write to `Grassmann4/.generated/`, which is ignored by
`Grassmann4/.gitignore`.

## Julia Reference Images

The local Julia project can load `Grassmann` with automatic precompile disabled:

```bash
JULIA_PKG_PRECOMPILE_AUTO=0 julia --project=. --startup-file=no -e 'using Grassmann'
```

Local Makie rendering is not available in this checkout because `Makie`,
`CairoMakie`, `GLMakie`, and `GeometryBasics` are not installed in the project.
For visual comparison, use the canonical images already linked from the Julia
docs:

```text
https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/<name>.png
```

The comparison run used these reference names:

```text
plane-1 plane-2 plane-3 plane-4 plane-5 plane-6
torus helix orb wave orbit-2 orbit-4
```

## Current Match

The Lean generator emits twelve visualizations with the same grayscale/white
plot palette as the Julia/Makie references.

| Example set | Lean status | Notes |
| --- | --- | --- |
| `plane-1` through `plane-6` | Direct linear-field counterparts | Euclidean rotations/reflections and hyperbolic boosts match the reference topology. Arrow glyphs and line density are approximate Makie-style matches. |
| `torus`, `helix` | Parametric counterparts | Captures the same 3D line-plot style and broad geometry, but not a proof of identical Grassmann.jl conformal motor output. |
| `orb`, `wave` | Qualitative vector-field counterparts | Uses deterministic Lean vector fields styled to match Makie. Exact CGA streamplot parity remains future work. |
| `orbit-2`, `orbit-4` | Qualitative orbit counterparts | Mirrors the documented translation/rotation intent with explicit parametric curves. Exact pointwise parity against Grassmann.jl CGA output remains future work. |

## Verified Commands

These commands were run successfully from the repository root:

```bash
lake exe jlexamples
JULIA_PKG_PRECOMPILE_AUTO=0 julia --project=. --startup-file=no -e 'using Grassmann; basis"2"; println(exp(pi*v12/2)); @basis S"+-"; println(exp((pi/8)*v12/2))'
```

The CGA smoke check also ran using the exact conformal basis syntax from
`docs/src/algebra.md`; the command is not repeated here because it contains the
non-ASCII infinity basis character.
