# Exact OBJ mesh ingress

Import `MeshTopology.Obj` explicitly. `MeshTopology.Obj.parse source` returns
`Except Error Mesh`. This optional module adds a narrow ASCII Wavefront OBJ
boundary using the existing `Values Rat 3`, fixed-length `Vector` connectivity
and `SimplexTopology 3`. It adds no dependency or Julia-oracle claim.

Format attribution: Wavefront Technologies, *Advanced Visualizer manual*,
appendix B1, [original specification text mirrored by Martin Reddy](https://www.martinreddy.net/gfx/3d/OBJ.spec),
accessed 2026-10-06. Its geometric vertices use `v`, polygon faces use `f`,
indices begin at 1, and negative indices count backward from the element's
position in the vertex list. The restrictions below are this importer's profile.
Topology attribution: the independent Lean port of Michael Reed/chakravala's
MeshTopology/StaticVectors ecosystem; see the pinned package port notes.

## Supported profile

| Record | Accepted meaning |
| --- | --- |
| Blank line or `#` comment | Ignored geometrically; full source text retained |
| `v x y z` | Exactly three Cartesian coordinates, in original units and axes |
| `f i j k` | Triangle in original vertex order |
| `f i j k l` | Strictly convex planar quad, split as `(i,j,k)` and `(i,k,l)` |

Records use spaces/tabs and LF or CRLF. Inline `#` starts a comment. Input must
be ASCII; tabs and printable characters are allowed in a record. Backslash
continuations are rejected. A backslash inside a comment is harmless.

Coordinates follow `[+-]` plus a decimal mantissa with at least one digit,
optionally a dot and an `e`/`E` signed integer exponent. Examples: `1`, `-.5`,
`1.`, `+.5e+1`, `1.e-19`. Values are exact normalized `Rat`, using the existing
JuliaBase decimal scanners without passing through Float. The effective power
of ten, after fractional digits, must have absolute value at most 4096. NaN,
infinity, hexadecimal numbers, underscores and rational `1/2` syntax reject.
Tokens are retained verbatim, so the spelling of negative zero is preserved
even though its rational value is zero.

Indices are arbitrary-precision signed ASCII decimal integers. Leading zeros
and `+` are accepted; underscores and slash texture/normal indices reject.
A positive id must name a vertex already defined at that face record.
Negative `-1` names the latest vertex at that record, not at end of file.
Zero, forward references and out-of-range values reject. `resolveIndex?` checks
the original `Int` before converting to `Nat`: a huge id such as `2^64+1` cannot
wrap to node 1. No UInt64/USize conversion occurs. `Grassmann.MaskIngress`
checks blade masks, so its dimensional bit-width contract does not apply to
these node ids.

Every other record rejects explicitly, including `o`, `g`, `s`, `vt`, `vn`,
`vp`, materials, free-form geometry, lines and points. Vertex weights/colors
and polygons with more than four corners also reject. No geometry is silently
dropped, welded, reordered, rescaled or projected.

## Errors and returned properties

`Error` carries `line` (1-based physical line), `kind` (an `ErrorKind` constructor)
and `detail` (original token or diagnostic text). Parsing returns the first error
and no partial mesh. The categories are `syntax`, `unsupportedRecord`,
`unsupportedIndex`, `unsupportedVertex`, `unsupportedFace`,
`unsupportedContinuation`, `nonAscii`, `coordinate`, `coordinateRange`,
`indexRange`, `degenerate`, `nonPlanarQuad`, `nonConvexQuad`, `emptyMesh`, and
the defensive `connectivity` final check. Empty/vertex-only input is `emptyMesh`
at line 1; defensive final checks also report line 1. Face tokens are validated
left to right before the 3/4-corner arity check. Vertex arity is checked before
coordinate parsing. Unsupported keywords report their own physical line.

`parse` returns a `Mesh` retaining complete input `source`, all `vertices` (including unused
ones), and original `faces`. Each vertex keeps its exact point, three coordinate
tokens and source line. Each face keeps resolved ids, original signed tokens,
source line and original triangle/quad kind. `top` is the existing triangle
topology, with 1-based ids and zero-based storage positions. Quad splitting is
explicit: `SimplexTopology 4` denotes four-vertex simplices, not an arbitrary
quad surface. The existing `BilinearTopology` belongs to quotient grids.

The return type carries `nodes_match : top.totalNodes = vertices.size`,
`connectivity : top.valid = true`, and `geometry_checked`, certifying that each
original face passed the exact predicate. It additionally carries
`triangles_checked : top.fulltopology.all (fun t => geometryValid vertices (.triangle t)) = true`:
every actual emitted topology triangle passes the exact predicate independently
of the original face array. `Mesh.triangle_checked m e` gives this property for
`m.top.fullElem e`, with `e : Fin m.top.totalElements`. The constructor is private;
external callers obtain certified meshes from `parse` and cannot directly use
record, named-constructor or anonymous-constructor syntax. Existing
`top.vertexFin` uses connectivity
to give proof-bounded node gathers. `Mesh.corner` returns an exact original
coordinate via that API; its access needs no fallback value.

`resolveIndex?_sound` proves every successful resolution has nonzero original
index, `1 ≤ id ≤ count`, and the exact positive/negative-index interpretation.
Triangles reject a zero exact cross product. Quads additionally require zero
scalar triple product (planarity), and strict positive corner turns against
the first triangle's normal. This rejects repeated/coincident/collinear
triangles and nonplanar, concave, crossed or straight-turn quads.
The checked predicate is not a formally proved general geometry refinement.

Connectivity, the face predicate, and solid validity are separate contracts.
An accepted mesh can be open, disconnected, globally inconsistently oriented,
have duplicate faces, intersect itself, or fail manifoldness. No solid,
volume, closure, CSG or Float field-law certificate follows from parse success.
Cartan PointCloud stores FloatArray; exact source coordinates remain here.
Any consumer creating a Float bundle must explicitly choose that rounding step.

## Consumer and fixture provenance

Run from the repository:

```sh
lake env lean --run examples/ObjMesh.lean docs/fixtures/obj/quad.obj
```

The example emits exact numerator/denominator strings, the existing topology's
triangle connectivity and coordinates gathered by `Mesh.corner`. It reports
`solid_certified: false`. The valid quad produces `[[1,2,3],[1,3,4]]`.

`docs/fixtures/obj/manifest.json` identifies 65 new authored fixture files,
their SHA-256 hashes, exact expectations and source attribution. Nine accepted
fixtures cover triangles, quads, both windings, mixed/unused points,
interleaved relative indexing, a tilted plane, exact large/tiny coordinates,
CRLF/comments and duplicate faces. Fifty-six rejected fixtures cover malformed
numbers, original huge indices, forward/zero ids, unsupported records and face
degeneracy. Expected valid coordinates were computed independently with
Python `fractions.Fraction` and unbounded integer indexing. These are additive
boundary fixtures, separate from the existing pinned Julia goldens.

Validation at baseline `023a5388`: 682 focused checks and 46,540 native
MeshTopology checks passed; the warning-free full build completed 1,272 jobs;
the full suite passed 3,481,812 checks with zero failures. The existing 186
MeshTopology entries that throw in both upstream and fixed Julia remain skipped
by the unchanged golden harness.

The 611-declaration audit retains all 555 prior declarations and adds 56 API,
type/constructor/proof-field and consumer declarations. It found only
`propext`, `Classical.choice`, and `Quot.sound`, with no admitted/custom axioms.
Six isolated executed mutations were killed: early word narrowing, wrong
relative-index base, Float coordinate loss, omitted planarity, allowed concavity,
and silently dropped unsupported records. Six false certificates were rejected
directly by the kernel with `declTypeMismatch`; three type/elaboration negatives
also passed. Draft parser/control failures are excluded from these counts.

An independent Python Fraction check verified all 65 fixture hashes, 102 exact
coordinates, 12 accepted face screens using projection/orientation, eight
geometric rejection expectations and the exact consumer output. The precision
triangle has two distinct rational vertices that coincide after Float conversion.
The module does not use Float arithmetic to parse or screen geometry. Compiler
and test phases ran serially at nice >=10 with `LEAN_NUM_THREADS=2`.

Preservation review found 1,628 previous tracked files byte-identical, with only
the two-line test registration changed. All 377 existing oracle golden files,
source pins, prior proof modules, mask ingress, legacy kernels and the 2,100-ref
set remain intact. New authored fixtures are additive. Remaining gaps include a
parser/refinement proof for exact decimal geometry, formal convex-quad geometry
lemmas, explicit rounded Cartan bundle adapters, broader OBJ records/polygons,
and independent manifold/solid/CSG validation.


## Certified topology correction (review of 023a5388)

The original public `Mesh` constructor certified bounds and `faces` geometry,
but did not certify `top` geometry. A kernel-checked counterexample supplied an
empty face array and the bounds-valid repeated triangle `[1,1,1]`; all old fields
held and `Mesh.corner` could gather it. This was a typed-interface gap: the
parser's accepted outputs were not shown defective.

The correction makes the constructor private, adds the actual-topology
certificate above and checks it before `parse` returns. No dependent equality
between two topology objects is added. The original point-count/bounds and
face certificates, exact coordinates, source data and fixture bytes remain
unchanged. Callers manually constructing `Mesh` must now use checked parsing;
the parser and existing bounded coordinate consumer keep their interfaces.

Persistent kernel regression proofs establish positive triangle and split-quad
checks, exact repeated-triangle rejection, and impossibility of any `Mesh` with
the reviewed actual topology and coordinates—even though connectivity and empty
face geometry still pass. Three external-construction syntax regressions are
also checked. This adds no provenance/refinement or general Euclidean geometry
theorem, and grants no manifold, solid or Float law certificate.

The review also observed the already documented comment-final backslash
behaviour. Cross-tool interoperability was not validated; that profile and all
65 fixture pins are preserved in this narrowly scoped correction.


Correction validation: 691 focused checks and 46,549 native MeshTopology checks
passed, including all 65 original fixture files. The warning-free full build
completed 1,272 jobs; the full suite passed 3,481,821 checks with zero failures.
The retained axiom audit covers 617 declarations (the old public constructor is
audited by its private kernel name, plus six new declarations) and finds only
`propext`, `Classical.choice` and `Quot.sound`.

The exact reviewed counterexample compiled before the correction and is now
rejected at construction. Two additional false actual-topology certificates
(repeated ids and distinct collinear points) were synchronously rejected by the
kernel with `declTypeMismatch`. Positive/rejection regression proofs use
`decide +kernel`; no native reduction or admitted axioms are introduced. The
existing exact quad consumer output also matches its baseline byte for byte.
Draft setup/elaboration failures are excluded from all validation counts.

Only this guide, `MeshTopology/Obj.lean` and `Tests/MeshTopology/Obj.lean` changed.
The other 1,696 tracked files, all 377 goldens, all 65 OBJ files and their manifest,
rotor/mask proof modules and all existing fixture/source pins are byte-identical.
All 65 OBJ SHA-256 pins were checked. Validation ran serially at nice >=10 with
`LEAN_NUM_THREADS=2`. Local receipts are `/tmp/obj-certificate-evidence.json` and
`/tmp/obj-certificate-local-commit-receipt.json`; these remain local evidence,
not a claim of automatic CI or an external CAD/parser run.
