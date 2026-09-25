# Element oracle: golden file schema (normative)

This is the complete specification of the element-level goldens under `oracle/golden/`. It is
written so that the Lean consumer (`Tests/Golden/*.lean`, DESIGN.md §7) can be implemented from
this file alone, without reading the Julia generator. Where this file and the generator disagree,
the generator has a bug. `uv run oracle/validate.py` is an independent reader built from this
document; it checks every rule marked **(checked)** below against the committed files.

How to regenerate, pinned versions and the generator layout are in
[`oracle/README.md`](../../oracle/README.md). The Julia semantics behind each op are in the other
port notes (grassmann-types.md, grassmann-products.md, grassmann-algebra.md, grassmann-docs.md).

Schema version: **1** (`meta.schema` in every file).

## Contents

1. [Files](#1-files)
2. [JSON conventions](#2-json-conventions)
3. [Suite manifests](#3-suite-manifests)
4. [Shard files](#4-shard-files)
5. [Spaces](#5-spaces)
6. [Scalars](#6-scalars)
7. [Element objects](#7-element-objects)
8. [Suites and case records](#8-suites-and-case-records)
9. [References, flags and defects](#9-references-flags-and-defects)
10. [The defect table (`defects.json`)](#10-the-defect-table-defectsjson)
11. [Consumer algorithm and comparison rules](#11-consumer-algorithm-and-comparison-rules)
12. [Op keys](#12-op-keys)
13. [Known gaps](#13-known-gaps)

## 1. Files

| path | content |
|---|---|
| `oracle/golden/<suite>.json` | suite manifest (§3) for each suite in `construct arith products unary composite floats docs` |
| `oracle/golden/<suite>/<shard>.json` | one shard (§4); the manifest lists every shard file, and there are no others **(checked)** |
| `oracle/golden/defects.json` | the defect table (§10), a JSON copy of `oracle/defects.toml` |
| `oracle/golden/blades/*.jsonl` | older blade-level (Cayley table) goldens, format in grassmann-parity.md §9; not described here, but the defect table's match patterns apply to them (§10) |
| `oracle/golden/<other>/` | goldens of other packages (`dendriform/`, `demorgan/`, `primitivebits/`, ...), written by their own generators; not part of this schema |

Every shard file is at most 4 MiB **(checked)**. The largest is about 2.6 MB.

## 2. JSON conventions

* Files are UTF-8 JSON (RFC 8259); `Lean.Json.parse` reads them. Strings contain arbitrary
  Unicode (`⟨∞∅111⟩`, `v₁₂`, `w¹`, `∂₁`, `𝟎` = U+1D7CE outside the BMP). Control characters are
  escaped (`\n`, `\t`, `\r`, `\u00XX`).
* **Integers** are JSON numbers without fraction or exponent. Bitmasks (`bits`, `basis`,
  `terms[i][0]`) can reach 2⁶² − 1 in the docs suite, beyond 2⁵³: read them as `Nat`
  (`Json.getNat?`), never through `Float`.
* **Coefficients are JSON strings** (§6), never JSON numbers, so every value is exact.
* **JSON floats** occur only in the composite `tolerance` table (`1.0e-7`) and are plain
  tolerances.
* Object keys are written in a fixed order and the layout puts one array element per line, so
  regenerated files diff cleanly. Consumers must not depend on key order or whitespace.
* An optional key is **absent** when not applicable. `null` appears only where this document
  says so (`space.Isq`, docs `display`, `str`/`compact_str` of `Other`/`Space`/`Number` objects
  whose `show` threw).
* Input references are **0-based** indices into the shard's `inputs` array.

## 3. Suite manifests

`oracle/golden/<suite>.json`:

```json
{
  "meta": {"schema": 1, "suite": "products", "julia": "1.13.0",
           "packages": {"Grassmann": "0.8.46", "AbstractTensors": "0.8.11", "DirectSum": "0.8.21",
                        "Leibniz": "0.3.0", "StaticVectors": "1.0.9"},
           "generator": "oracle/suites/products.jl"},
  "totals": {"cases": 74536, "errors": 1792, "ref_mismatch": 2815, "unexplained": 0,
             "defects": {"chain0-times-mixed": 408, "...": 0}},
  "shards": [
    {"shard": "E2", "file": "products/E2.json", "cases": 4536, "bytes": 621070,
     "errors": 116, "ref_mismatch": 153, "unexplained": 0, "space": "E2"}
  ]
}
```

* `shards[*].file` is relative to `oracle/golden/`. `bytes` is the file size **(checked)**.
* `space` is present for per-space suites (the shard's `space.name`).
* `totals` are the sums of the shard `stats` (§4) **(checked)**; `totals.unexplained` is 0 for
  every committed suite **(checked)**.

## 4. Shard files

A shard is one JSON object. Its top-level keys, in this order **(checked)**:

| suite | keys |
|---|---|
| construct | `meta` `space` `cases` `stats` |
| arith, products, unary | `meta` `space` `ops` `reference` `inputs` `cases` `stats` |
| composite | `meta` `space` `ops` `tolerance` `inputs` `cases` `stats` |
| floats | `meta` `encoding` `fields` `cases` `stats` |
| docs | `meta` `sandbox` `cases` `stats` |

| key | content |
|---|---|
| `meta` | `schema` (1), `suite`, `shard`, `julia`, `packages` (as in the manifest), `generator`; per-space and floats shards add `seed_key` (`"grassmann-oracle/<suite>/<shard>"`) and `seed` (decimal string of the 64-bit FNV-1a hash of the key, the `Xoshiro` seed); docs shards add `source` (`oracle/docs/<file>.txt`) |
| `space` | the space descriptor (§5) |
| `ops` | op key → Julia expression template over `a`, `b` (§12); every case `op` is one of its keys **(checked)** |
| `reference` | prose: what the per-case `ref` means (§9) |
| `tolerance` | composite only: op key → `{"rtol": float, "atol": float}` |
| `inputs` | the input pool: element objects (§7) extended with `label` (string, unique in the shard) and `src` (the Julia source that built the value, evaluated with `V` bound to the space) |
| `cases` | the case records (§8) |
| `stats` | `{"cases", "errors", "ref_mismatch", "unexplained", "defects": {id: count}}`, recomputable from `cases` (§9) **(checked)** |
| `encoding`, `fields`, `sandbox` | prose documentation (floats, docs) |

## 5. Spaces

Every per-space shard has a `space` object with exactly these keys, in this order **(checked)**:

| key | type | meaning |
|---|---|---|
| `name` | string | registry name (§5.1); equals the shard name |
| `julia` | string | Julia source of the bundle, e.g. `S"∞∅+++"` |
| `description` | string | prose |
| `show` | string | `string(Submanifold(bundle))`: the space that elements print with, e.g. `⟨∞∅111⟩` |
| `show_bundle` | string | `show` of the bundle itself, e.g. `⟨∞∅+++⟩` (`4` for the Int manifold) |
| `n` | int | `mdims`: number of generators, counting ∞/∅ and tangent (∂) variables |
| `grade` | int | `grade(V)` = `n − diffvars` **(checked)**: the pseudoscalar grade used by Julia's `+` lattice |
| `metric` | object | see below |
| `options` | int | raw DirectSum option word; its decoding is given by the next fields, so consumers need not decode it |
| `hasinf`, `hasorigin` | bool | generator 1 is ∞ / the ∅ generator is present (bit 0 is ∞ when `hasinf`; ∅ is bit 1 when both are present, else bit 0) |
| `conformal` | bool | `hasinf ∧ hasorigin`: bits 0, 1 are the null pair ∞, ∅ |
| `isdiag` | bool | the metric is diagonal (false exactly for conformal spaces here) |
| `dyadmode` | int | 0 plain, 1 dual (covector) space, −1 mixed V⊕V′ |
| `isdual` | bool | the space is a dual (covector) space |
| `diffvars`, `diffmode` | int | number of tangent variables (the last `diffvars` generators) and the tangent order |
| `Isq` | string or null | the scalar part of I·I for the top blade I, as an Int64 coefficient string (§6); null if not computable |
| `basis` | int array | the bitmask of every basis blade **in dense order** (§5.2); `[]` when n > 8 |
| `names` | string array | the printed name of every basis blade, same order (`v`, `v₁`, `v∞∅₁`, `w¹`, `∂₁v₁`); `[]` when n > 8 |

**`metric`** is one of:

* `{"kind": "signature", "neg": <int>}`: a DirectSum `Signature`. Bit k of `neg` is set iff
  generator k+1 is marked negative, so e_{k+1}² = −1 for a non-conformal space and +1 otherwise.
  This is DirectSum's raw metric word: a dual space of `S"+++"` has `neg = 7` (it prints
  `⟨---⟩'`), and a mixed space sets the bits of its dual half. For **conformal** spaces the
  metric is not diagonal: generators ∞, ∅ (bits 0, 1) form the null block of the Gram matrix,
  g(∞,∞) = g(∅,∅) = 0 and g(∞,∅) = g(∅,∞) = −1, on the wedge basis v∞∅ = v∞∧v∅, so
  v∞·v∅ = −1 + v∞∅ (grassmann-products.md §4.2). Their `neg` still has the ∅ bit set (a
  DirectSum encoding detail that the products do not use). A space with only ∞ (`INF3`) is
  diagonal with v∞² = +1; one with only ∅ (`ORG3`) is diagonal with v∅² = −1.
* `{"kind": "diagonal", "diag": [<string>, ...]}`: a DirectSum `DiagonalForm`: e_k² = diag[k−1],
  `n` Int64 coefficient strings **(checked: length n)**. Zero entries are degenerate
  (projective) generators.
* `{"kind": "euclidean"}`: the Int manifold `n` (all squares +1).

Products in dual, mixed and tangent spaces are not exercised by the products suite (§13).

### 5.1 Registry

| name | Julia bundle | n | notes |
|---|---|---|---|
| `E2` … `E5` | `S"++"` … `S"+++++"` | 2–5 | Euclidean Signature |
| `I4` | `4` | 4 | Int manifold, prints `⟨1111⟩` |
| `M4` | `S"-+++"` | 4 | spacetime algebra |
| `S4` | `S"+-+-"` | 4 | split signature |
| `D3` | `D"1,2,-3"` | 3 | DiagonalForm with non-unit entries |
| `PGA2`, `PGA3` | `D"0,1,1"`, `D"0,1,1,1"` | 3, 4 | degenerate DiagonalForm, e₁² = 0 |
| `INF3`, `ORG3` | `S"∞+++"`, `S"∅+++"` | 4 | one projective point, diagonal |
| `CGA2`, `CGA3` | `S"∞∅++"`, `S"∞∅+++"` | 4, 5 | conformal null basis |
| `DUAL3` | `(S"+++")'` | 3 | covector space, labels `w¹…` |
| `DYAD2` | `S"++"⊕(S"++")'` | 4 | mixed space (construct only) |
| `TAN2`, `TAN22` | `tangent(S"++")`, `tangent(S"++",2,2)` | 3, 4 | tangent bundles (∂ generators last) |

Elements always live on `Submanifold(bundle)`, whose `show` is `space.show`.

### 5.2 Blades and dense order

A basis blade is a bitmask B: bit k set means generator k+1 is present. Its grade is
`popcount(B)`.

**Dense order** is Julia's `Multivector` order: grade-major, and lexicographic within a grade on
the increasing index tuple. Index `i` of a `dense` vector is the blade `space.basis[i]`
**(checked)**. It is not numeric bitmask order. A generator of the order:

```
dense_basis(n) = [0] ++ [ Σ_{i ∈ idx} 2^i  for g in 1..n, for idx in combinations(0..n-1, g) (lexicographic) ]
```

For n = 4 the order is `1, e1, e2, e3, e4, e12, e13, e14, e23, e24, e34, e123, e124, e134, e234,
e1234`, i.e. the masks `0,1,2,4,8,3,5,9,6,10,12,7,11,13,14,15`. This is Leibniz's
`indexbasis`/`basisindex` (the Lean `Leibniz.indexBasis` tables must agree).

The pseudoscalar I has mask 2ⁿ − 1 and is the last dense entry.

## 6. Scalars

A coefficient is a JSON string, or a 2-array of strings for complex types. The element's `T`
(the Julia `valuetype`) says how to parse it:

| `T` | encoding | examples |
|---|---|---|
| `Int64` | decimal integer in [−2⁶³, 2⁶³) | `"-3"`, `"-9223372036854775808"` |
| `Bool` | `"true"` / `"false"` | |
| `Rational{Int64}` | `"<num>//<den>"`, reduced, den > 0, sign on the numerator | `"-1//3"`, `"0//1"`, `"5//1"` |
| `Float64` | Julia `repr` (below) | `"0.3333333333333333"`, `"1.0e-5"`, `"2.0"`, `"-0.0"`, `"NaN"`, `"-Inf"` |
| `Complex{T}` for T above | `[re, im]`, each encoded as T | `["1","2"]`, `["1.5","-2.5"]`, `["NaN","Inf"]` |

**Float64 grammar** (every Float64 coefficient matches it **(checked)**):

```
float := "-"? ( "NaN" | "Inf" | digits "." digits ( "e" "-"? digits )? )
```

There is no `+` in exponents, integers print with `.0`, and the digits are the shortest that
round-trip (Ryu, Julia `Base.Ryu.writeshortest`). To parse: split the sign, mantissa digits,
the position of `.` and the exponent into an exact decimal m·10^e and round it to nearest even,
e.g. with `Float.ofScientific` (correctly rounded in Lean core); map `NaN`, `Inf`, `-Inf`, `-0.0`
directly. Any correctly rounding parser recovers the exact bits, because the strings are
round-trip representations. Julia prints every NaN as `NaN`, so a NaN's payload and sign are not
recorded here (the floats suite has exact bits).

**Other `T`.** Values outside the table above occur only in the docs suite (`Any`,
`Irrational{:π}`, nested `Chain{...}` coefficients of a dyadic tensor). Their coefficients are
`string(c)` and are not parseable (a zero of `Irrational{:π}` prints `"false"`): treat such
elements as display-only and compare `str` only.

## 7. Element objects

An element object ("E") describes one Julia value. Its `kind` is one of:

| `kind` | Julia value | Lean `TA` constructor (DESIGN.md §4.3) |
|---|---|---|
| `Zero` | `Zero{V}` (prints `𝟎`) | `zero` |
| `One` | `One{V}` = `Submanifold{V,0,0x0}` (prints `v`) | `one` |
| `Infinity` | `DirectSum.Infinity{V}` (prints `∞`) | `infinity` |
| `Submanifold` | a basis blade `Submanifold{V,G,B}` of grade ≥ 1 | `blade b` |
| `Single` | `Single{V,G,B,T}`: one coefficient on one blade; may be 0 (`0v₁` is not `Zero`) | `single b x` |
| `Chain` | `Chain{V,G,T}`: all blades of one grade | `chain g c` |
| `Spinor` | even-grade part (`Quaternion` etc. are aliases) | `spinor` |
| `CoSpinor` | odd-grade part | `cospinor` |
| `Multivector` | `Multivector{V,T}`: all 2ⁿ blades | `multi` |
| `Couple` | `Couple{V,B,T}` = re + im·B | `couple b re im` |
| `PseudoCouple` | `PseudoCouple{V,B,T}` = re·B + im·I | `pseudo b re im` |
| `Phasor` | `Phasor{V,B,T}` = amplitude ∠ angle | `phasor` |
| `Number`, `Bool` | a plain Julia number (e.g. the result of `norm`) | not an element |
| `Space` | a non-basis `Submanifold` used as a space (docs) | none |
| `Other` | anything else (tuples, operators, `Values`, `Basis`, ...) | none; compare `str` only |
| `Error` | Julia threw an exception | none |

Fields (present exactly as listed **(checked)**):

| field | present for | meaning |
|---|---|---|
| `kind` | all | as above |
| `T` | every element kind, Number, Bool | coefficient type (§6), Julia's `valuetype`; for Number/Bool the value's own type. For Zero, One, Submanifold (`Int64`) and Infinity (`Float64`) it is nominal |
| `V` | element kinds, optional | `show` of the element's space, **only when it differs from the shard's `space.show`** (`adjoint` moves to the dual space `⟨---⟩'`; `Phasor(2.0, π/3)` lives in `⟨11⟩`; docs values). When `V` is present, `dense` is relative to that space (length 2^n′ for its own n′) |
| `grade` | Zero, One, Infinity, Submanifold, Single, Chain | the **storage** grade: Julia's type parameter G. For One/Submanifold/Single it equals `popcount(bits)` **(checked)**; for Zero/Infinity it is 0. In tangent spaces it counts ∂ generators, unlike Leibniz `grade(x)` |
| `bits` | One (always 0), Submanifold, Single, Couple, PseudoCouple | the blade B |
| `dense` | every element kind except Infinity and Phasor, when the space has n ≤ 10 | the 2ⁿ coefficients in dense order (§5.2) |
| `terms` | instead of `dense` when n > 10 (docs only), when cheaply available | sparse `[[bits, coef], ...]`: Zero `[]`; One/Submanifold `[[B, "1"]]`; Single `[[B, x]]`; Couple `[[0, re], [B, im]]`; PseudoCouple `[[B, re], [2ⁿ−1, im]]`; Chain the nonzero entries in lexicographic order. Other kinds of large n carry neither |
| `native` | construct suite; Single, Chain, Multivector, Spinor, CoSpinor, Couple, PseudoCouple | `value(x)` in the kind's storage order (§7.1) |
| `value` | Number, Bool | the scalar (§6) |
| `amp`, `angle` | Phasor | nested element objects (amplitude, usually a Number; angle, a Number or an element) |
| `str` | all except Error | `sprint(show, x)` = `repr(x)` = what the Julia REPL prints inline. For Number/Other/Space it is `null` if `show` threw |
| `str_error` | elements, instead of `str` | `true` when `show` itself threw (a Julia bug); exactly one of `str`/`str_error` is present **(checked)** |
| `compact_str` | construct and docs outputs (not the nested `amp`/`angle`) | `sprint(show, x; context = :compact => true)` |
| `type` | construct outputs, Other, Space | `string(typeof(x))`, e.g. `Quaternion{⟨+++⟩, Int64}` (informational) |
| `error`, `msg` | Error | the exception type name (`MethodError`, `UndefVarError`, `BoundsError`, ...) and the first line of its message, at most 200 characters |

### 7.1 Storage layouts and dense support

The value of an element is its dense vector. Its kind fixes which dense entries can be nonzero
**(checked)**, and `native` is the gather of `dense` at these indices **(checked)**:

| kind | support (dense indices) | `native` order |
|---|---|---|
| Zero | none | (no `native`) |
| One, Submanifold | the entry of `bits`, whose value is 1 | (no `native`) |
| Single | the entry of `bits` | `[x]` |
| Chain | the blades of grade `grade` | those blades in dense order, i.e. `Leibniz.indexbasis(n, G)` |
| Spinor | the even-grade blades | the even-grade blades in dense order (grade 0, grade 2, grade 4, ...) |
| CoSpinor | the odd-grade blades | the odd-grade blades in dense order (grade 1, grade 3, ...) |
| Multivector | all | dense order |
| Couple | 1 and B | `[re, im]` = the scalar coefficient, then the B coefficient |
| PseudoCouple | B and I | `[re, im]` = the B coefficient, then the I coefficient |

A **degenerate** Couple with B = 0 (`Couple{V,One(V)}`) or PseudoCouple with B = I puts both
parts on one blade: that dense entry holds re + im, and `native` still gives the two parts.

To build a Lean value from an element object: select the constructor from `kind` (+ `grade`,
`bits`) and take its coefficients from `dense` at the support indices (or from `native` when
present). A Chain or Multivector may have zero coefficients; they are kept (Julia prints them,
e.g. `3v₁ - 3v₂ + 0v₃`).

## 8. Suites and case records

### 8.1 `construct`

Shards: every registry space. Cases `{"label", "src", "out"}`, no `inputs`. `out` carries
`native`, `compact_str` and `type` in addition to the usual fields. Samples: every basis blade
(`label` = `blade:<name>`), the lattice sample of §8.7 with Int coefficients, Float variants of
every container, zero-valued containers (`MultivectorZero` prints `0v⃖`), scalar-only
Multivectors, Phasors, and in `E3`, `M4`, `CGA2` also Rational/Complex/Bool coefficients,
NaN/±Inf/−0.0, values that exercise compact rounding and `typemin(Int)`.

What to test: build the element from `(kind, grade, bits, T, native)`, then compare `dense`,
`str` and `compact_str`. This checks constructors, the storage-order maps and display.

### 8.2 `arith`

Shards: `E2 E3 E4 M4 D3 PGA3 INF3 CGA2 CGA3 DUAL3 TAN2`. Inputs: the lattice sample (§8.7) with
Infinity and `Single1z` (0·v₁), plus three numbers labelled `n:2`, `n:0`, `n:0.5` (kind Number,
`T` Int64/Int64/Float64). In `TAN2` there are no Couple/PseudoCouple inputs.

Ops (`ops`): `add` `a + b`, `sub` `a - b`, `mul` `a * b`, `div` `a / b`, `rdiv` `a // b`, `neg` `-a`.

Cases `{"op", "a", "b"?, "out", "flags"?, "ref"?, "defects"?}`:

* `add`, `sub` over **every ordered pair** of element inputs: the representation lattice of
  grassmann-types.md §4.5 (which kind `x + y` returns);
* for every element input x: `neg` x (no `b`); `x ± s` and `s ± x` for each number s; `2*x`,
  `x*2`, `0.5*x`; `x/2`; and `x//2` when x has exact coefficients.

`ref`: the exact linear combination of the inputs' dense vectors (a number s counts as s·One).

### 8.3 `products`

Shards: `E2 E3 E4 E5 M4 D3 PGA3 INF3 CGA2 CGA3`. Inputs: the lattice sample without Infinity and
without `Single1b`/`Single2b`; the Float inputs `Chain1F`, `MultivectorF` only when n ≤ 4.
Cases `{"op", "a", "b", "out", ...}` for each of the 14 ops of §12 over **every ordered pair**
of inputs.

`ref`: the same op applied to both inputs converted to Multivector (Julia's Multivector kernels
are the bilinear extension of the blade tables). For `sandwich` (x ⊘ y with x = `a`) and
`tsandwich` (y >>> x with x = `b`) the reference follows Julia's projection rule
(grassmann-products.md §4.6): let y′ be Multivector if y is a Multivector, a Couple with odd
grade B, or a PseudoCouple whose B parity differs from n's parity, else y's kind. Then

* x graded (Zero/One/Submanifold/Single/Chain): project the Multivector-path result onto grade(x),
  unless y′ is Multivector, or both x and y′ are terms (Zero/One/Infinity/Submanifold/Single);
* x a Couple/PseudoCouple: sandwich each part (scalar and B, resp. B and I) separately as a
  term, apply the rule above to each part, and add;
* otherwise: the unprojected Multivector-path result.

### 8.4 `unary`

Shards: `E2 E3 E4 E5 I4 M4 S4 D3 PGA2 PGA3 INF3 ORG3 CGA2 CGA3 DUAL3` (no tangent space: see
defect `tangent-generated-crash`). Inputs: as products, plus Infinity, with the Float inputs for
every n. Cases `{"op", "a", "out", ...}` for each of the 24 unary ops of §12 and `grade:k` for
k = 0 … n (template `grade(a, k)`).

`ref`: for the linear maps (every op except `abs2`, `norm`, `adjoint`) the same map applied to
the input converted to Multivector; for `Multivector`, the input's own dense vector; for
`grade:k`, `grade(Multivector(a), k)`. `norm` returns a Number; `adjoint` returns an element of
the dual space (`V` = the dual's `show`).

### 8.5 `composite`

Shards: `E2 E3 E4 M4 CGA3`. Inputs (Float64 coefficients): scalars 0.3 and 1.2, a vector 0.7v₁,
a random vector, bivectors θ·v₁₂ for θ ∈ {0.1, 0.5, 1.0}, a random bivector, 0.4·I, a rotor
`exp(0.3v₁₂)`, Couples on v₁₂ and v₁, Spinors near 0 and near 1, Multivectors near 0 and near 1,
the versor 1 + ½I, and in CGA3 the null bivector ½v∞₁ and the Minkowski-plane bivector ½v∞∅.
Each input has a subset of the ops (the `ops` table lists them all).

Cases `{"op", "a", "b"?, "k"?, "out", "defects"?}`: `exp`, `log`, `sqrt`, `sin`, `cos`, `tan`,
`sinh`, `cosh`, `inv` of `a`; `pow` = `a ^ k` for k ∈ {0, 1, 2, 3, 5, 8, 9}; `div` = `a / b`
over the ordered pairs of the division inputs. There is no `ref`.

Compare dense vectors with the op's tolerance: `‖out − expect‖₂ ≤ atol + rtol·max(‖out‖₂,
‖expect‖₂)`. Julia evaluates most of these with power series that stop when the running norm
changes by less than √eps, so independent implementations agree only to about 1e-8. Result
kinds and `str` are informational here.

### 8.6 `floats`

One shard `all`. Cases `{"T", "value", "show", "compact"}`, where `show` = `sprint(show, x)` and
`compact` = `sprint(show, x; context = :compact => true)`:

| `T` | `value` |
|---|---|
| `Float64` | 16 lowercase hex digits of the IEEE-754 bit pattern (`Float.ofBits`) |
| `Int64` | decimal string |
| `Rational{Int64}` | `[num, den]` decimal strings |
| `Complex{Int64}` | `[re, im]` decimal strings |
| `Complex{Float64}` | `[re, im]` hex bit patterns |
| `Bool` | `"true"` / `"false"` |

About 20 000 Float64 values: specials, NaN payloads, powers of 10 and 2 with their neighbours,
the decimal/exponent switch boundaries, 7-digit halfway cases for the 6-digit compact rounding,
short user-style decimals, random bit patterns, subnormals, log-uniform magnitudes. Every
Float64 `show` round-trips to the exact bits (NaN to some NaN) **(checked)**. The Lean side
compares `show` with `JuliaBase.F64.showString` and `compact` with `JuliaBase.F64.showCompact`,
and the other types with the `JuliaBase.JuliaShow` instances (`showString`/`showCompact`).

### 8.7 The lattice sample

Per space with n generators and I = 2ⁿ − 1, coefficients are small integers in ±{1, 2, 3}, with
about 30% zeros inside containers (to exercise zero skipping in `show`). Labels:

* `Zero`, `One`, `Infinity` (not in products);
* `Single0` (c·v), `Sub1` (v₁), `SubI` (the pseudoscalar blade);
* `Single<g>` on the first blade of each grade g; `Single1b`, `Single2b` on the second blade of
  grades 1, 2 (arith and construct only); `Single1z` = 0·v₁ (arith, construct);
* `Chain<g>` for every g = 0 … n;
* `Couple:<name>` for B ∈ {v₁, v₁₂ (n ≥ 3), I}; `PseudoCouple:<name>` for B ∈ {v₁, v₁₂ (n ≥ 3)};
* `Spinor`, `CoSpinor` (n ≥ 2), `Multivector`;
* `Chain1F`, `MultivectorF`: Float64 coefficients k/4 with k ∈ −12 … 12 (dyadic, so every sum
  and product is exact in binary).

`src` is Julia source evaluated with `V = Submanifold(bundle)`, e.g.
`Couple{V,Λ(V).b[5]}(-3, 2)`, where `Λ(V).b[k]` is the k-th blade in dense order (1-based).

### 8.8 `docs`

One shard per "fresh group" of `oracle/docs/*.txt` (the README/docs examples of
grassmann-docs.md §6 and the §6.8 probes); `meta.source` names the file. Statements are
evaluated REPL-style in a sandbox with `using Grassmann; import DirectSum, LinearAlgebra`
(`sandbox`); blocks of a group share it, and `ans` is bound as in the REPL.

Cases `{"block", "input", "display"?, "out"?, "stdout"?, "defects"?}`:

| field | meaning |
|---|---|
| `block` | the source block label, e.g. `algebra.md:1116` |
| `input` | the statement source |
| `display` | the REPL `text/plain` rendering (`:limit => true`, 40×200); `null` when the statement ends in `;` or returns `nothing`; **absent** when evaluation threw |
| `out` | the value as an element object (§7) with `compact_str`; absent when the value is `nothing`; kind `Error` when evaluation threw. Its `V` is always present (docs shards have no `space`) |
| `stdout` | text the statement printed (`dump`, `DirectSum.printindices`), when non-empty |

The representable cases for Lean are those whose `out.kind` is an element kind with a
parseable `T`; the rest are display-only goldens (`display`/`str`).

## 9. References, flags and defects

Arith, products and unary cases are recomputed along an independent path (the `ref` rules of
§8.2–8.4). When the reference is computable and either Julia threw or the result's `dense`
differs from it (exactly for exact types; for floats with rtol = atol = 1e-12, NaN equal to
NaN), the case gets

```json
"flags": ["ref_mismatch"], "ref": [<dense coefficient strings>]
```

`ref` has 2ⁿ entries in dense order, with the coefficient type of the promoted inputs. `flags`
has no other values **(checked)**; `ref` is present iff the flag is **(checked)**.

Cases that match an entry of the defect table (§10) get `"defects": [id, ...]` (ids in table
order). Shard `stats` (**checked** by recount):

* `errors` = cases whose `out.kind` is `Error`;
* `ref_mismatch` = cases with the flag;
* `unexplained` = cases that are an error or a mismatch and have no `defects` tag;
* `defects` = id → number of tagged cases.

Every committed suite has `unexplained` = 0: every Julia error and every mismatch is attributed
to a documented cause. A nonzero count after regeneration means a new Julia defect or a
generator bug; fix that before relying on the cases.

## 10. The defect table (`defects.json`)

```json
{
  "meta": {"schema": 1, "generator": "oracle/defects.toml"},
  "defects": [
    {"id": "pseudocouple-addsub", "policy": "ref",
     "title": "...", "source": "Grassmann.jl src/products.jl:558", "notes": "...", "correct": "...",
     "match": [{"suite": "arith", "op": "add|sub", "kinds": ["PseudoCouple", "PseudoCouple"]}]}
  ]
}
```

`id` is unique **(checked)**. `title`, `source` (Julia file:line), `notes` (port-note
references) and `correct` (what the port does instead) are prose. `policy` is one of:

| policy | consumer action for a tagged case |
|---|---|
| `ref` | if the case has `ref`, compare the Lean dense result with `ref` (kind and `str` are not checked: Julia's are wrong). Otherwise, if `out` is an Error, skip; otherwise the case was not actually affected: compare with `out` as usual |
| `skip` | skip: the golden has no trustworthy expected value |
| `replicate` | Julia's value is the intended one: compare with `out` |

A case with several tags takes the strongest policy, `skip` > `ref` > `replicate`.

Entries with an empty `match` document defects that no golden exercises (several crash or hang
Julia and are avoided by the generators). Tags are already applied to the element suites, so
their consumers never evaluate `match`. It is given for consumers of `golden/blades/*.jsonl`,
which carry no tags: there, use `suite` = `blades`, `space` = the dump's space name and `file` =
the file name.

**Match language.** A case is tagged with an entry if **any** of its `match` tables matches. A
table matches when **all** its fields match:

| field | matched against |
|---|---|
| `suite`, `space`, `op` | the suite name, the shard's `space.name`, the case `op` (for construct/docs, `op` is the suite name) |
| `out` | the output kind (`out.kind`; `Nothing` when `out` is absent) |
| `msg` | the Error message (`out.msg`); a table with `msg` never matches a non-Error case |
| `block`, `input`, `file` | construct: the case `label` and `src`; docs: `block`, `input` and the `meta.source` file name without directory and `.txt` |
| `kinds` | an array with one pattern per operand (`a`, then `b`); the number of operands must equal the array length. A pattern is `*`, or `|`-separated alternatives `Kind` or `Kind:g`, where g is an integer or `n` (= `space.grade`) and must equal the operand's `grade` |
| `when` | a named predicate over the operands and the space (below) |

The string fields are **globs**: `|` separates alternatives, `*` matches any run of characters
(including none), every other character is literal, and the whole string must match.

| `when` | true when |
|---|---|
| `same_bits` | two operands, both have `bits`, and they are equal |
| `diff_bits` | two operands, both have `bits`, and they differ |
| `couple_rev_plus` | some operand is a Couple whose `popcount(bits) mod 4 ∈ {0, 1}` (B² = +‖B‖²) |
| `null_blade` | `space.conformal`, and some operand's `bits` contains exactly one of bit 0 (∞), bit 1 (∅) |
| `mixed_parity_first` | the first operand is a Couple with odd `popcount(bits)`, or a PseudoCouple with `popcount(bits) mod 2 ≠ space.n mod 2` (not parity-homogeneous) |
| `Isq_plus` | `space.Isq` parses to a positive number |

## 11. Consumer algorithm and comparison rules

```
defects := load golden/defects.json                     -- id ↦ policy
for suite in [construct, arith, products, unary, composite, floats, docs]:
  manifest := load golden/<suite>.json
  for shard in manifest.shards:
    s := load golden/<shard.file>
    V := build the Lean space from s.space (§5); check s.space.basis against the Lean index tables
    X := s.inputs.map decode                           -- §6, §7
    for case in s.cases:
      policy := strongest policy of case.defects (none if untagged)
      if policy = skip: count skipped; continue
      expect := if policy = ref ∧ case.ref present then Dense(case.ref)      -- values only
                else if case.out.kind = Error then skip-or-expect-rejection (rule 5)
                else case.out
      got := run the Lean op for case.op on X[case.a], X[case.b] (and case.k)
      compare got with expect (rules 2-4)
```

1. **Coverage.** Report pass/fail/skip counts per suite and per defect id. Ops the port does not
   implement yet count as skipped, not failed.
2. **Kind.** Compare the Lean result's constructor with `out.kind`, and `grade`/`bits` where
   present: this checks Julia's result-type narrowing. Not for composite, and not when comparing
   against `ref`.
3. **Values.**
   * Int64, Rational, Bool coefficients: exact.
   * Float64 coefficients in construct/arith/products/unary: bitwise after parsing (§6), all NaNs
     equal, the sign of zero kept. Where the Lean kernel sums in a different order, rtol = atol =
     1e-12 is acceptable and must be documented.
   * composite: the op's `tolerance` (§8.5).
4. **Strings.** Compare `str` and `compact_str` exactly. Coefficients print with Julia's number
   formatting: use `JuliaBase.F64.showString`/`showCompact` and the `JuliaBase.JuliaShow` class
   (`showValue`, `showTerm`, which implement Leibniz `showvalue` and Grassmann `showterm`), not a
   separate float printer. Element printing rules are in grassmann-types.md §5.
5. **Errors.** An `Error` output with no defect tag means Julia rejects the operation (e.g.
   `inv` of a non-invertible element). The port may reject it too (type error, `none`, or an
   exception) or implement it; either way there is no value to compare, so count it separately
   rather than failing.

## 12. Op keys

Each shard's `ops` table maps op keys to the Julia expression (as a user writes it after
`using Grassmann`); `a`, `b` are the case inputs.

| op key | Julia | suggested Lean (DESIGN.md §4.4) |
|---|---|---|
| `add` `sub` `neg` | `a + b`, `a - b`, `-a` | `+ - -` on `TA`; a Number is `TA.single 0 x` or a scalar action |
| `mul` | `a * b` (geometric product ⟑) | `*` |
| `div` | `a / b` | `/` (arith: by the number 2; composite: element / element) |
| `rdiv` | `a // b` | exact division by a `Rat` scalar |
| `wedge` `vee` | `a ∧ b`, `a ∨ b` | `∧ ∨` (scoped notation) |
| `contraction` | `contraction(a, b)` (= `a ⋅ b` = `a ⨽ b`) | `⋅` |
| `lcontraction` | `a ⨼ b` | `⨼` |
| `lshift` `rshift` | `a << b`, `a >> b` | named functions |
| `revmul` | `a ∗ b` (reverse product) | `∗` |
| `scalarprod` | `a ⊛ b` | `⊛` |
| `cross` | `a × b` | `×` |
| `sandwich` | `a ⊘ b` | `⊘` |
| `tsandwich` | `a >>> b` | named function |
| `veedot` `antidot` | `veedot(a, b)` (⟇), `antidot(a, b)` | `⟇`, `antidot` |
| `reverse` `involute` `clifford` `antireverse` | `reverse(a)` (= `~a`), ... | the same names (`~` = reverse) |
| `complementright` `complementleft` `hodge` `complementlefthodge` | `complementright(a)` (= `!a`), ..., `hodge(a)` (= `⋆a`) | the same names |
| `metric` `antimetric` | `metric(a)`, `antimetric(a)` | the same names |
| `even` `odd` `real` `imag` | parity parts; `real`/`imag` of Couples | the same names |
| `scalar` `vector` `bivector` `trivector` `volume` | grade projections (`volume` = `AbstractTensors.volume`) | the same names |
| `grade:k` | `grade(a, k)` | `TA.grade k` |
| `abs2` `norm` | `abs2(a)`, `norm(a)` (a Number) | the same names |
| `adjoint` | `a'` (moves to the dual space) | `adjoint` |
| `Multivector` | `Multivector(a)` | conversion to `multi` |
| `exp` `log` `sqrt` `sin` `cos` `tan` `sinh` `cosh` `inv` | as named | the `Analytic`-style functions |
| `pow` | `a ^ k`, k from the case | `^` with a `Nat` exponent |

`⊗` is not generated: for graded operands it builds a `Dyadic` operator, outside the element
model.

## 13. Known gaps

* Equality and `isapprox`: the `Multivector == term` crash makes blind pair sweeps unsafe
  (grassmann-types.md §9 item 8).
* Index tables, label parsing (`Λ(V).v32`), `@basis` tuples and larger-n spot checks
  (grassmann-types.md §9 items 1–3); the blade goldens and the docs suite cover part of this.
* Products in tangent, dual and mixed spaces (skipped in v1, grassmann-products.md §4.14); the
  construct suite covers their display and the unary suite `DUAL3`.
* Complex coefficients in products (the conjugation quirks of grassmann-products.md §4.12).
* The StaticVectors/AbstractTensors scalar suites (abstracttensors-staticvectors.md §9) live with
  those packages' own goldens.
