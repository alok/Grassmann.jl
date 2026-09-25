# Grassmann.jl element types: porting spec (scope: `src/Grassmann.jl`, `src/multivectors.jl`, README)

Target: a Lean 4 port (v4.35-era core: `Vector`, `FloatArray`, `BitVec`, `grind`, `omega`, `bv_decide`, `Std.HashMap`).
Source: `/Users/alokbeniwal/chakravala/Grassmann.jl` (master, `Project.toml` version 0.8.47).
Oracle: registered Grassmann 0.8.46 in the scratch Julia 1.13 env. I diffed it against master. `src/Grassmann.jl`, `src/multivectors.jl`, `algebra.jl`, `products.jl`, `parity.jl` and `composite.jl` are byte-identical (only `forms.jl` differs). DirectSum 0.8.21 is identical. Leibniz and AbstractTensors differ from master by one import line and two `angle` methods, so every file:line citation below matches the oracle.

Every output string in this document (things like `=> ...`, tables, goldens) was produced by running the Julia oracle, unless it is marked "doc claim".
Oracle scripts: `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad/jl_types/t*.jl` (outputs in `t*.out`).

Path abbreviations used for citations:

| abbrev | path |
|---|---|
| `GJ` | `Grassmann.jl/src/Grassmann.jl` |
| `MV` | `Grassmann.jl/src/multivectors.jl` |
| `PR` | `Grassmann.jl/src/products.jl` |
| `AL` | `Grassmann.jl/src/algebra.jl` |
| `CO` | `Grassmann.jl/src/composite.jl` |
| `DS` | `DirectSum.jl/src/DirectSum.jl` |
| `DSb` | `DirectSum.jl/src/basis.jl` |
| `DSg` | `DirectSum.jl/src/generic.jl` |
| `DSo` | `DirectSum.jl/src/operations.jl` |
| `LZ` | `Leibniz.jl/src/Leibniz.jl` |
| `LZu` | `Leibniz.jl/src/utilities.jl` |
| `LZi` | `Leibniz.jl/src/indices.jl` |
| `LZg` | `Leibniz.jl/src/generic.jl` |
| `AT` | `AbstractTensors.jl/src/AbstractTensors.jl` |

(all under `/Users/alokbeniwal/chakravala/`)

---

## 1. Purpose & scope

Grassmann.jl implements Grassmann–Clifford–Hodge (geometric) algebra on a compile-time generating space `V`. The README defines it at README.md:18-24 and README.md:156-179.

This report specifies:

* **The element type zoo** and how each type is stored:
  * `Submanifold` (basis blades and subspaces, from DirectSum), `Single`, `Zero`, `One`, `Infinity`
  * `Chain`, `Multivector`
  * `AbstractSpinor` with `Spinor`, `CoSpinor` (= `AntiSpinor`), `Couple`, `PseudoCouple`, `Phasor`
  * the aliases `Simplex`, `Multiplex`, `Imaginary`, `Quaternion`, `AntiQuaternion`, `GaussianInteger`, `LipschitzInteger`, `AbstractReal` and siblings
  * `ChainBundle` (legacy)
* How elements are built, converted, indexed and printed.
* The **representation-selection lattice**, i.e. which concrete type `a+b` produces. Julia computes this through types, and it is the de facto "promotion".
* Equality semantics.
* The basis-generation machinery Grassmann re-exports from DirectSum and Leibniz: `@basis`, `Λ`, `getbasis`, label parsing.
* The top-level Grassmann.jl functions: `hyperplanes`, the `∇` operator from `V`, `∂/d/δ`, `project/reject (↑/↓)`, `betti`, `skeleton`, `chain/path`, `column(s)`, the field helpers and the FFT glue.

Out of scope here: the product and complement kernels themselves (`⟑ ∧ ∨ ⋅ ⋆ !`, `exp`, `inv`). They live in `algebra.jl`, `products.jl`, `parity.jl` and `composite.jl`, and other reports cover them. I only reference them where the type layer depends on them (for example `adder` for `+`).

---

## 2. Public API inventory

`names(Grassmann)` returns 315 exported symbols, not counting the module itself. Most of them are re-exports from AbstractTensors, DirectSum, Leibniz and LinearAlgebra, and 8 are stale.

* The full list, with defining module and source file, is in `scratchpad/jl_types/t9.out`.
* The tables below cover what `GJ` and `MV` declare, plus the re-exports that belong to the type layer.
* Product, complement and operator exports (`forms.jl`, `algebra.jl`, `composite.jl`, `parity.jl`) belong to other reports.

### 2.1 Exports declared in `GJ`

| symbol | kind | origin (defined in) | semantics | line |
|---|---|---|---|---|
| `⊕` | fn | DirectSum (`DSo:36-74`) | direct sum of spaces; ASCII alias `+` on bundles | GJ:26 |
| `ℝ` | const | `DS:443` = `Signature(1)` (prints `⟨+⟩`) | real line | GJ:26 |
| `@V_str` `@S_str` `@D_str` | macro | `DS:428-438` | `V"..."` → `TensorBundle(str)`, `S"..."` → `Signature(str)`, `D"..."` → `DiagonalForm(str)` | GJ:26 |
| `Manifold` | abstract type + fn | AT:49, DS:376 | `Manifold(x)` returns the `V` of an element | GJ:26 |
| `Submanifold`, `Signature`, `DiagonalForm` | types | DS:252, DS:131, DS:193 | see §3 | GJ:26 |
| `value` | fn | AT:213; methods MV:1093-1098, DSg:70-72 | returns the internal `Values` or scalar | GJ:26 |
| `@basis @basis_str @dualbasis @dualbasis_str @mixedbasis @mixedbasis_str` | macro | DSb:88-132 | bind basis names into scope | GJ:27 |
| `Λ` | const alias | `DSb:206` `const Λ = Basis` | basis container / algebra accessor | GJ:27 |
| `ℝ0 … ℝ9` | const | `DS:444-450`, `ℝn = Submanifold(n)` | Euclidean Int-metric spaces (print `⟨111⟩` etc.) | GJ:28 |
| `mdims tangent metric antimetric cometric` | fn | AT / DSg:128 / LZg | dimension; tangent bundle; metric ops | GJ:28 |
| `hodge wedge vee complement dot antidot istangent Values divergence grad` | re-exports | AT/AbstractLattices/StaticVectors/CO | product layer (not this report) | GJ:29 |
| `cayley` | fn | forms.jl:807 | product table | GJ:60 |
| `hyperplanes(V)` | fn | GJ:62 | `[I ⟑ v_k for k in 1:rank(V)-diffvars(V)]` (§4.10) | GJ:60,62 |
| `points(f, r=-2π:0.0001:2π)` | fn | GJ:68 | `vector.(f.(r))` (also MV:221-223 legacy methods) | GJ:60,68 |
| `TensorAlgebra` | abstract type | AT:32 | root type (`<: Number`) | GJ:60 |
| `𝕚, 𝕛, 𝕜` | const | GJ:71 `= hyperplanes(ℝ3)` | `(1v₂₃, -1v₁₃, 1v₁₂)` | GJ:70-71 |
| `∇ Δ ∂ d δ` | const/fn | LZ:154-161 | `∇ = Derivation(I)`, `Δ = ∇^2`, `d = differential`, `δ = codifferential`, `∂ = boundary` | GJ:75 |
| `↑ ↓` | const alias | GJ:212 `const ↑,↓ = project,reject` | ASCII aliases `project`, `reject` | GJ:75 |
| `differential codifferential boundary project reject` | fn | GJ:109-112, GJ:164-210 | see §4.10 | GJ:75 |
| `nabla Nabla Laplacian` | const/type | LZ:156,162-163 | `nabla = ∇`; `Nabla = Derivation{Bool,1}`; `Laplacian = Derivation{Bool,2}` | GJ:76 |
| `skeleton 𝒫 collapse subcomplex chain path` | fn | GJ:232-287 | simplicial complex utilities (`𝒫` and `subcomplex` are currently broken, §4.12) | GJ:232 |
| `column columns` | fn | GJ:293-294 | component extraction | GJ:291 |
| `scalarfield vectorfield pointfield chainfield rectanglefield` | fn | GJ:311-348 | field samplers; `pointfield`/`vectorfield` have 0 methods in core (extensions add them) | GJ:309 |

### 2.2 Exports declared in `MV`

| symbol | kind | semantics | line |
|---|---|---|---|
| `TensorTerm TensorGraded TensorMixed Scalar GradedVector Bivector Trivector` | abstract types/aliases from AT (AT:64-124) | hierarchy (§3.1) | MV:15 |
| `Submanifold Single Multivector Spinor ChainBundle` | types | §3 | MV:16 |
| `SparseChain MultiGrade` | **stale** | exported but undefined (`getfield` fails) | MV:16 |
| `Zero One Chain Phasor Quaternion GaussianInteger AbstractSpinor AntiSpinor` | types/aliases | §3 | MV:17 |
| `AbstractReal AbstractComplex AbstractRational ScalarFloat ScalarIrrational AbstractInteger AbstractBool AbstractSigned AbstractUnsigned` | `Union` aliases | "scalar-like" unions (MV:979-987) | MV:18-19 |
| `CoSpinor Simplex` | type, alias | odd spinor; `Simplex{V,T<:GradedVector,N} = Chain{V,1,T,N}` | MV:19, MV:94 |
| `UniformScaling I isdiag det tr ⋅ cross × contraction points` | re-exports (LinearAlgebra/AT) | `I` = universal pseudoscalar | MV:27 |
| `Multiplex` | alias | `Multiplex{V,T<:Multivector,N} = Multivector{V,T,N}` | MV:277-278 |
| `Couple PseudoCouple` | types | exported inside loop | MV:826 |
| `gdims tdims betti χ unit ∠ radius istensor isgraded isterm pseudoscalar` | fn/alias | `∠ = Phasor` (MV:871) | MV:965 |
| `basis grade pseudograde antigrade hasinf hasorigin scalar norm unitnorm` | fn | | MV:966 |
| `valuetype scalar isscalar vector isvector indices imaginary unitize geomabs` | fn | | MV:967 |
| `bivector isbivector trivector istrivector isvolume antiabs antiabs2` | fn | | MV:968 |
| `realvalue imagvalue unitangle phase amplitude complexify vectorize polarize` | fn | §4.8 | MV:969 |
| `quaternion quatvalue quatvalues` | fn | `const quatvalues = quatvalue` (MV:1090) | MV:1079 |

Other files also export names that are defined nowhere, so they are **stale exports**: `angular`, `radial` (parity.jl:28), `coscalar` (CO:18), `eigprods` (forms.jl:6), `pseudodot` (CO:15) and `⟂` (AL:23). Do not port them.

### 2.3 Unicode operators and their ASCII aliases (type-layer relevant)

| unicode | ASCII | where |
|---|---|---|
| `∠` | `Phasor` | MV:871 |
| `↑` / `↓` | `project` / `reject` | GJ:212 |
| `Λ` | `DirectSum.Basis` | DSb:206 |
| `∂`, `d`, `δ` | `boundary`, `differential`, `codifferential` | LZ:161 |
| `∇`, `Δ` | `nabla`, `laplacian` | LZ:154-156 |
| `𝒫` | none (power-set skeleton; broken) | GJ:259 |
| `AntiSpinor` | `CoSpinor` | MV:456 |
| `quatvalues` | `quatvalue` | MV:1090 |
| `𝕚 𝕛 𝕜` | `hyperplanes(ℝ3)` | GJ:71 |
| `⊗` on types | `Chain{V}⊗Chain{W}` gives a nested chain type | MV:197-199 |
| `~x` | `reverse`/`conj` | DSg:187 |
| `v⃖` (bound by `@basis`) | the *String* `"v"` (see §4.11) | DSb:73 |
| `𝟎`, `∞` (bound by `@basis`) | `Zero(V)`, `Infinity(V)` | DSb:74-75 |

`Infinity` is **not exported** by Grassmann; reach it as `DirectSum.Infinity`.

### 2.4 Important unexported internals in scope

| name | line | purpose |
|---|---|---|
| `compact` (closure toggle), `compactio(io)` | MV:39-44 | global "compact element display" flag (default `true`) |
| `showterm(io,V,B::UInt,i,compact)` | MV:46-58 | prints ` + x` / ` - x` terms |
| `isnum`, `numtype(T,S=Int)` | MV:60-64 | coefficient-type sanitation for generated constructors |
| `chain_src(N,G,T,grades,type)` | MV:247-259 | code generator: embed a grade-G chain into Multivector/Spinor/CoSpinor |
| `log2sub(N)`, `log2sub2(N)` | MV:261-267, MV:418 | infer `V = Submanifold(log2 N)` from tuple length |
| `grade_src`, `grade_src_chain`, `*_next` | MV:280-298 | code generator for grade extraction by runtime `Int` |
| `single(t::Chain)` | MV:201-204 | collapse a chain with exactly one nonzero term |
| `realvalue/imagvalue(::Complex)` | MV:822-823 | `.re`/`.im` |
| `multispin(t)` | MV:999-1014 | smallest spinor-family container |
| `_phasor_type(B)` | MV:1021 | "simple phasor" predicate |
| `_subspace(V,B)` | MV:1076-1077 | subspace spanned by B's indices |
| `value_diff` | MV:1100-1101 | unwrap tensor-valued grade-0 chains |
| `maxgrade/mingrade/nextgrade/nextmingrade/nextmaxgrade/maxpseudograde/nextmaxpseudograde` | MV:1156-1197 | grade range metadata used by product generators |
| `count_gdims`, `χ` overloads | MV:1199-1233 | graded counts for meshes/multivectors |
| `absym` | GJ:234-238 | coefficient-wise `abs` |
| `boundary_rank`, `boundary_null` | GJ:121-146 | homology helpers |
| `rows`, `pointset`, `rectangle` | GJ:296-307, GJ:341-347 | mesh helpers |
| `generate_derivation`, `generate_algebra`, `generate_symbolic_methods`, `check_parsym`, `extend_parsym` | GJ:368-414 | code generation for extra scalar fields |
| `parsym = (Symbol, parval...)` | MV:32 | print-type registry |

---

## 3. Data representations

### 3.1 Type hierarchy (verified by `typeof`)

```
Number
└─ TensorAlgebra{V,T}                                   AT:32   (V = space value, T = scalar field)
   ├─ Manifold{V,T}                                     AT:49
   │  ├─ TensorGraded{V,G,T}                            AT:64   (Scalar/GradedVector/Bivector/Trivector = G 0..3, AT:80-101)
   │  │  ├─ TensorTerm{V,G,T}                           AT:108  (single coefficient)
   │  │  │  ├─ Submanifold{V,G,B}  <: TensorTerm{V,G,Int}   DS:252  (fieldless; also used AS a space)
   │  │  │  │    One{V} = Submanifold{V,0,UInt(0)}           DS:552
   │  │  │  ├─ Single{V,G,B,T}  <: TensorTerm{V,G,T}         DS:457  (field v::T)
   │  │  │  ├─ Zero{V}          <: TensorTerm{V,0,Int}       DS:563  (fieldless)
   │  │  │  └─ Infinity{V}      <: TensorTerm{V,0,Float64}   DS:636  (fieldless)
   │  │  └─ Chain{V,G,T,X}  (X = binomial(N,G))          MV:68   (field v::Values{X,T})
   │  │       Simplex{V,T<:GradedVector,N} = Chain{V,1,T,N}  MV:94
   │  └─ ChainBundle{V,G,T,Points}  (fieldless, legacy)  MV:211
   └─ TensorMixed{V,T}                                  AT:124
      ├─ Multivector{V,T,X} (X = 2^N)                   MV:229  (field v::Values{X,T})
      │    Multiplex{V,T<:Multivector,N}                 MV:277
      └─ AbstractSpinor{V,T}                            MV:414
         ├─ Spinor{V,T,X}   (X = 2^(N-1))               MV:422  (v::Values{X,T})   even grades
         │    Imaginary{V,T} = Spinor{V,T,2}  (N=2)     MV:971
         │    Quaternion{V,T} = Spinor{V,T,4} (N=3)     MV:972
         │    LipschitzInteger{V,T<:Integer} = Quaternion{V,T}  MV:974
         ├─ CoSpinor{V,T,X} (X = 2^(N-1))  = AntiSpinor  MV:422,456  odd grades
         │    AntiQuaternion{V,T} = CoSpinor{V,T,4}      MV:973
         ├─ Couple{V,B,T}        (v::Values{2,T})        MV:656   scalar + B-blade
         │    GaussianInteger{V,B,T<:Integer} = Couple{V,B,T}   MV:975
         ├─ PseudoCouple{V,B,T}  (v::Values{2,T})        MV:677   B-blade + pseudoscalar
         └─ Phasor{V,B,T}        (v::T, ω::B)            MV:852   amplitude ∠ angle
```

Scalar-like unions (MV:979-987) are used for dispatch only:

* `AbstractReal = Union{Real, Single{..,<:Real}, Chain{V,G,<:Real,1}}`
* `AbstractComplex{T} = Union{Complex{T}, Phasor{V,<:TensorTerm,T}, Couple{V,B,T}, Single{..,Complex{T}}, Chain{V,G,Complex{T},1}}`
* `AbstractBool`, `AbstractInteger`, `AbstractSigned`, `AbstractUnsigned`, `AbstractRational{T}`, `ScalarFloat` and `ScalarIrrational` follow the same "scalar or one-component graded" pattern.

### 3.2 The space parameter `V`

* **`TensorBundle{n,Options,Metrics,Vars,Diff,Name}`** (DS:64) has two concrete forms:
  * `Signature{N,M,S,F,D,L}` (DS:131). `S::UInt` is the metric bit mask: bit `k-1` set means `v_k² = −1`. `M` is the options hash: `tensorhash` at DS:83; decoders `_hasinf`, `_hasorigin`, `_dyadmode`, `_polymode` at DSg:37-40.
  * `DiagonalForm{N,M,S,F,D,L}` (DS:193). `S` is an index into the global `diagonalform_cache` of `Values` (DS:207-217).
  * An `Int n` means a Euclidean space. It prints as `n` inside Submanifold displays, as `⟨111⟩`.
* **`Submanifold{M,N,S}`** (DS:252) plays two roles, distinguished by the type of `M`:
  1. **Space.** `M` is a `TensorBundle` or an `Int`, `N` is the dimension and `S` is the mask of the ambient indices it spans. `Submanifold(V)` = `Submanifold{V,rank(V)}(2^rank−1)`. `V(i...)` gives a sub-space with mask `S` (DS:256-267, DSg:23-35). Example: `(ℝ^5)(3,5)` is `Submanifold{⟨+++++⟩,2,0x14}` and prints `⟨__+_+⟩`.
  2. **Basis blade.** `M` is itself a `Submanifold` space, `N` = grade `G`, and `S = B` is the blade's bit mask *relative to the space's own index list*.

  `isbasis(x)` is true iff `M isa Submanifold` (DSg:77-80). Example: for `G42 = collect(Submanifold(4)(1,4))`, `G42.v14` has relative bits `0x3` and `G42[3]` (= `v₄`) has bits `0x2`. Labels are printed with absolute indices through `shift_indices` (DS:404).
* **Normalization.** Every element's inner constructor rewrites `V ↦ DirectSum.submanifold(V)` (DS:392-394):
  * `Int n` ↦ `Submanifold(n)` = `Submanifold{n,n,2^n−1}`
  * `TensorBundle` ↦ `Submanifold(bundle)`
  * a basis blade ↦ its space

  So the stored `V` of every `Chain`, `Single`, etc. is a *space-Submanifold* (MV:70, MV:231, MV:424-425, MV:658, MV:679; DS:459-460, DS:564, DS:637). **`Phasor` is the exception**: its inner constructor stores `V` verbatim (MV:855).
* Derived quantities used everywhere:
  * `mdims(V)` = N (DSg:43)
  * `grade(V)` = `rank − (isdyadic ? 2 : 1)·diffvars` (LZg:12)
  * `hasinf(V)`, `hasorigin(V)` (DSg:115-120)
  * `istangent(V) = diffvars ≠ 0` (LZg:36)
  * `hasconformal = hasinf && hasorigin` (LZg:53)
  * `diffmode` (DSg:54)

  In conformal spaces (`S"∞∅…"`) index 1 is `∞` and index 2 is `∅`. In `S"∞…"` or `S"∅…"`, index 1 is the special one (DSg:116-119, LZi:122-131).

### 3.3 Per-type fields and invariants

| type | type params (compile-time) | runtime fields | invariants |
|---|---|---|---|
| `Submanifold{V,G,B}` | V space, G grade, B::UInt bits | none | `popcount(B)=G`, `B < 2^N` |
| `One{V}` | V | none | alias of `Submanifold{V,0,0}` |
| `Zero{V}` | V | none | `value = 0` (Int) (DS:602) |
| `Infinity{V}` | V | none | `value = Inf`; `valuetype = Float64` (DS:636, DS:661) |
| `Single{V,G,B,T}` | V, G, B (a basis `Submanifold`), T | `v::T` | stored `B = basis(C)` (DS:459); value 0 is allowed; **no** auto-collapse to `Zero` |
| `Chain{V,G,T,X}` | V, G, T, X=`binomial(N,G)` (computed via `@computed`, MV:68-71) | `v::Values{X,T}` | component `i` ↔ `indexbasis(N,G)[i]` (lex order, §3.4) |
| `Multivector{V,T,X}` | V, T, X=`2^N` | `v::Values{2^N,T}` | grade-major, then lex within a grade (`basisindex`) |
| `Spinor{V,T,X}` | V, T, X=`2^(N-1)` | `v::Values{2^(N-1),T}` | even grades 0,2,4,… concatenated, lex within a grade (`spinindex`) |
| `CoSpinor{V,T,X}` | V, T, X=`2^(N-1)` | same | odd grades 1,3,5,… concatenated (`antiindex`) |
| `Couple{V,B,T}` | V, B (basis Submanifold), T | `v::Values{2,T}` = (real, imag) | means `v[1]·1 + v[2]·B` |
| `PseudoCouple{V,B,T}` | V, B, T | `v::Values{2,T}` = (real, imag) | means `v[1]·B + v[2]·I` (I = pseudoscalar) |
| `Phasor{V,B,T}` | V (not normalized), B = *type of angle*, T = *type of amplitude* | `v::T` (amplitude), `ω::B` (angle) | `valuetype` is `T` |
| `ChainBundle{V,G,T,P}` | all params | none | legacy (Cartan); `isbundle` is undefined in this package |

`valuetype(x)` is the `T` of `TensorAlgebra{V,T}` (AT:221):

* `Int` for `Submanifold` and `Zero`, `Float64` for `Infinity`
* the coefficient type for the others

`Values{N,T}` (StaticVectors) is an immutable struct wrapping `NTuple{N,T}`. `realvalue(z)` reads `z.v.v.:1` (MV:827). `Variables` is the mutable counterpart and `FixedVector` wraps an `AbstractVector`.

### 3.4 Index orderings (the single most important invariant)

**Bits.** Basis vector `k` (1-based, counted after any ∞/∅ shift) is bit `k−1`. A blade is the OR of its vectors' bits.

**Within a grade: lexicographic order of the sorted index list, not numeric bit order.**

* `combo(n,g) = collect(combinations(1:n,g))` (LZu:111-133, Combinatorics.jl lex order)
* `indexbasis(n,g) = bit2int.(indexbits.(n, combo(n,g)))` (LZu:221-244; `indexbasis(n,0) = [0]`)

Example n=4, g=2: `[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]`, which is bits `3,5,9,6,10,12`. Numeric bit order would give `v12,v13,v23,v14,…`, which is **wrong**.

Index functions (all 1-based in Julia; `s==0 ↦ 1`), from LZu:181-219:

* `bladeindex(n,s)` = position of `indices(s)` in `combo(n,popcount s)`, i.e. the 1-based lex rank.
* `basisindex(n,s) = binomsum(n,g) + bladeindex(n,s)`
* `spinindex(n,s) = spinsum(n,g) + bladeindex(n,s)`
* `antiindex(n,s) = antisum(n,g) + bladeindex(n,s)`

Here `g = popcount(s)`, and the prefix sums come from LZu:135-179:

* `binomsum(n,i) = Σ_{q<i} C(n,q)`
* `spinsum(n,i) = Σ_{q<i, q even} C(n,q)`
* `antisum(n,i) = Σ_{q<i, q odd} C(n,q)`

`binomcumsum(n)` returns the full vector `Values(0, cumsum(C(n,0..n))...)` of length `n+2`. `spincumsum` and `anticumsum` are the analogues, and `binomsum_set` etc. are aliases of these.

Lex rank pseudocode (0-based result; add 1 for Julia):
```
rank(n, c[1..k] sorted ascending):   // c are 1-based indices
  r = 0; prev = 0
  for i in 1..k:
    for j in prev+1 .. c[i]-1:  r += C(n - j, k - i)
    prev = c[i]
  return r
```
Unrank walks the same sum. In Lean, prove `rank ∘ unrank = id` on `Fin (C n k)` (§8).

Layout tables (verified by display, `jl_types/t1.out` and `jl_types/t8.out`):

* N=3 Multivector: `[1, v1, v2, v3, v12, v13, v23, v123]`
* N=3 Spinor: `[1, v12, v13, v23]`
* N=3 CoSpinor: `[v1, v2, v3, v123]`
* N=4 Multivector: `[1, v1..v4, v12, v13, v14, v23, v24, v34, v123, v124, v134, v234, v1234]`
* N=4 Spinor: `[1, v12, v13, v14, v23, v24, v34, v1234]`
* N=4 CoSpinor: `[v1, v2, v3, v4, v123, v124, v134, v234]`
* Conformal `S"∞∅+++"` basis order: `v, v∞, v∅, v₁, v₂, v₃, v∞∅, v∞₁, v∞₂, v∞₃, v∅₁, v∅₂, v∅₃, v₁₂, v₁₃, v₂₃, v∞∅₁, …, v∞∅₁₂₃`. This is the same lex order with ∞ = index 1 and ∅ = index 2.

The Grassmann-side setters that write into these layouts are generated at PR:150-178: `setblade!`↔`bladeindex`, `setmulti!`↔`basisindex`, `setspin!`↔`spinindex`, `setanti!`↔`antiindex`. The `add*` variants accumulate.

### 3.5 Compile-time vs runtime

Julia puts **everything about shape** in type parameters. That includes `V` (with its metric, options and dimension), the grade `G`, the blade `B` of `Single`/`Couple`/`PseudoCouple`, and the lengths `X`. The only runtime data are the coefficient tuples.

Grade selection by runtime `Int` (`m[g]`, `m(g)`) is still compiled to an `if/elseif` chain over `0..N` by a `@generated` function (MV:300-309). `Val(g)` variants resolve at compile time (MV:310-314).

Caches and size limits (LZu:104-107):

| constant | value | effect |
|---|---|---|
| `algebra_limit` | 8 | full `Basis` container (with a `Values` of all blades) when `N ≤ 8`, otherwise `SparseBasis` |
| `sparse_limit` | 22 | `SparseBasis` for `N ≤ 22`, `ExtendedBasis` above that |
| `cache_limit` | 12 | generated constructors unroll into literal `Values(…)` tuples when `N < 12` (MV:135, MV:248, MV:388, MV:470, MV:489; AL:760, AL:784, AL:818). Otherwise they use `zeros(Variables)` plus `set*!` loops. Index tables are cached up to 12; above that they are computed lazily. |
| `index_limit` | 20 (LZi:70) | `digitsfast` cache |

The maximum space is N = 62 (labels exhaust `alphanumv`).

---

## 4. Algorithms

### 4.1 Constructors

#### `Chain` (MV:68-107, 131-160)

* `Chain{V,G,T}(v)` (inner): stores `Values{C(N,G),T}`. Wrong lengths raise `DimensionMismatch: No precise constructor for Values{3, Int64} found. Val of input was 2.`
* `Chain{V,G}(val::AbstractVector{𝕂})` gives `Chain{V,G,𝕂}`. `Chain{V,G}(::NTuple)` converts through `Values` (MV:78-80).
* `Chain{V}(tuple/Values)` means grade 1 (MV:81-83). `Chain(tuple)` means `V = Submanifold(N)` and grade 1 (MV:84-86): `Chain(4,5,6)` gives `Chain{⟨111⟩,1,Int64,3}`.
* The vararg sugar `(::Type{T})(x...) = T(x)` (MV:90-91) makes `Chain{V,1}(1,2,3)` work. `Chain(z::Couple)` hits it too: `Chain(Couple{V,v12}(1,2))` gives `(1+2v₁₂)v₁ ::Chain{⟨1⟩,1,Couple,1}`, a 1-D chain whose coefficient is a Couple (quirk).
* `Chain(v::Zero{V}) = zero(Chain{V,0})` (MV:88).
* Generated `Chain{V,G,𝕂}(val, v::Submanifold{V,G}, nothing)` (MV:131-140): a one-hot vector at `bladeindex(N,bits)`. The coefficient type is `numtype(𝕂,Any)`, i.e. `𝕂` if it is Real, Complex or TensorAlgebra and `Any` otherwise. Padding is `zero(numtype(𝕂))`, i.e. `Int(0)` for non-numbers. Example: a Symbol value gives `:x*v₁ + 0v₂ + 0v₃ ::Chain{…,Any}`.
* `Chain(val, v::Submanifold)`, `Chain(v::Submanifold)` (coefficient `1::Int`) and `Chain(v::Single)` (MV:141-145).
  * **Oracle:** `Chain(2.5, v13)` is a `MethodError: … is ambiguous` (MV:141 vs the vararg sugar at MV:91), so avoid it.
  * `Chain(v12)` gives `1v₁₂ + 0v₁₃ + 0v₂₃`.
* `Chain{V,G,T,X}(x::Single{V,0})` gives an **all-zero** grade-G chain (MV:146). For G=0 it gives the proper scalar (MV:147). Oracle: `Chain{V,2,Float64,3}(Single{V}(2.0))` gives `0.0v₁₂ + 0.0v₁₃ + 0.0v₂₃`.
* `Single(m::Chain{V,0,T,1}) = scalar(m)`; `Single(m::Chain{V,G,T,1}) = volume(m)` (MV:149-152).
* `ones(Chain{V,G,T,X})` (MV:195-196). `zero`/`one` are at MV:104-107: `one(chain)` is a **grade-0** chain `1v`.

#### `Multivector` (MV:229-275, 377-402)

* `Multivector{V}(AbstractVector)`; `Multivector{V}(tuple)`; `Multivector(tuple)` infers `V = Submanifold(log2 N)`. The error for a non-power-of-2 length is the thrown *String* `"Constructor for Multivector got 3 inputs, which is invalid."` (MV:261-274).
* `Multivector{V}(t::Chain)` (generated through `chain_src`, MV:240-259) places `t.v` at offset `binomsum(N,G)` with zeros elsewhere. `Multivector{V,Float64}(Chain{…,Int})` raises a MethodError (the `T` must match).
* `Multivector(val::𝕂, v::Submanifold)` (generated, MV:384-393) is one-hot at `basisindex`. `Multivector(v::Submanifold)` uses coefficient `1`; `Multivector{V,T}(v)` uses `one(T)`; `Multivector(v::Single)` (MV:394-402).
* `Multivector(::Zero{V})` is **broken**: it calls `zeros(::Expr)` because `tvec` returns an `Expr` (MV:269, PR:16).
* `Multivector{V}(a::Single, b::Single)` goes through `addermulti` (MV:711).
* From spinor types: `Multivector{V}(t::Spinor)` and `Multivector{V}(t::CoSpinor)` scatter by grade parity (MV:561-570).
* `Multivector{V,T}(z::Couple) = Multivector{V}(scalar(z), imaginary(z))` (MV:712).
* `Multivector{V,T}(z::PseudoCouple) = Multivector{V}(imaginary(z), volume(z))` (MV:713).
* `Multivector(z::Couple|PseudoCouple)` (MV:836-837); `Multivector(z::Phasor) = Multivector(complexify(z))` (MV:925-927).
* `zero`/`one` (MV:377-380): `one(m) = zero(m) + one(V)`, which prints as `1v⃖`.
* `Single(v, b::Multivector) = v*b` (MV:382).

#### `Spinor` and `CoSpinor` (MV:420-506)

Both are generated from one loop, so their API is symmetric:

* Inner constructor from `Values`; `{V}(AbstractVector)`; `{V,𝕂}(Single)`; `(TensorAlgebra)`; `{V}(tuple)`.
* `Spinor(tuple)` infers `V = log2sub2(N) = Submanifold(log2(2N))`. So `Spinor(1,2)` is 2-D and `Spinor(1,2,3,4)` is 3-D (`Quaternion`). A length-3 tuple gives the thrown String `"Constructor for Multivector got 6 inputs, which is invalid."`.
* Generated `Spinor{V,𝕂}(val, v::Submanifold{V,G})` (MV:465-475) errors with `"$v is not expressible as a Spinor"` for odd G. `CoSpinor` (MV:484-494) errors with `"… is not expressible as an CoSpinor"` for even G.
* `Spinor{V}(t::Chain{V,G})` (MV:496-507) through `chain_src` over `evens(0,N)` or `evens(1,N)`. It errors for the wrong parity with `"Grassmann.Chain{⟨111⟩, 1, Int64, 3} is not expressible as a Spinor"`.
* From Couple/PseudoCouple through `adderspin`/`adderanti` (MV:715-721): `Spinor(Couple{V,v1}(1,2))` errors `"v and v₁ are not expressible as Spinor"`.
* `Spinor{V}(val::Phasor) = Spinor(complexify(val))` (MV:929).
* `zero` is defined for both (MV:447-448). `one(::Spinor) = Spinor{V,T}(one(T), Submanifold{V}())` (MV:617-618).
* **`one(::CoSpinor)` is undefined and the fallback hangs the Julia compiler.** Never call it in the oracle.
* Identity conversions: `Spinor{V}(t::Spinor{V}) = t`, and likewise for CoSpinor and Multivector (MV:995-997).

#### `Couple` and `PseudoCouple` (MV:656-721)

* `Couple{V,B}(Complex)` gives `(re, im)`; `Couple{V,B}(AbstractVector | NTuple{2})`; vararg sugar.
* `Couple(ab)` with no parameters means `V = Submanifold(2)`, `B = pseudoscalar v₁₂` (MV:668). So `Couple(1,2)`, `Couple(1+2im)`, `Couple((1,2))` all give `1 + 2v₁₂ ::Couple{⟨11⟩,v₁₂,Int}`.
* From terms (MV:699-704):

  | call | result |
  |---|---|
  | `Couple(One)` | `Couple{V,One}(1,0)` (prints `1 + 0v`) |
  | `Couple(b::Submanifold)` | `(0,1)` with B = b |
  | `Couple(scalar Single)` | `Couple{V, Submanifold(V)}(val, 0)`: **B becomes the pseudoscalar** (`Couple(3v)` gives `3 + 0v₁₂₃`) |
  | `Couple(Single{G>0})` | `(0, val)` with B = its basis |
  | `PseudoCouple(b)` | if `grade(b) == grade(V)`: `PseudoCouple{V,One(V)}(0, val)` (prints `0v + 1v₁₂₃`); else `PseudoCouple{V,b}(val, 0)` |
  | `Couple{V,B}(One / Submanifold / Single)` (MV:706-709) | `(1,0)`, `(0,1)`, `(v,0)` for a scalar Single, `(0,v)` otherwise, **regardless of whether the term's basis equals B** (`Couple{V,v13}(v2)` gives `0 + 1v₁₃`) |

* `Couple(m::Imaginary{V}) = Couple{V,Submanifold(V)}(Complex(m))` (MV:993).
* `zero` is defined for both (MV:839-840). `one` is defined for `Couple` only (MV:768-769).

#### `Phasor` (MV:852-939)

* `Phasor{V}(v,ω)` (inner, no normalization).
* `Phasor(v, ω::TensorAlgebra{V}) = Phasor{V}(v,ω)`.
* `Phasor(a,b) = Phasor{Submanifold(2)}(a,b)`.
* `Phasor(m::TensorAlgebra) = polarize(m)`.
* `Phasor(r::TensorTerm{V,0}, iθ) = Phasor(value(r), iθ)`.
* `Phasor{V}(v::Complex) = Phasor(Couple{V}(v))` **hangs** (`Couple{V}(::Complex)` does not exist, and inference loops). Avoid it.
* `zero` and `one` keep the angle's *type* but zero it: `zero(Phasor(2.0,0.5v12))` gives `0.0 ∠ 0v`.

#### `Single` (DS:457-508)

| call | result |
|---|---|
| `Single(v::Real \| Complex)` | `Single{Submanifold(0)}` (prints `2v`, type `Single{⟨⟩,0,v,Int64}`) |
| `Single(b::Submanifold)` / `Single{V}(b)` | coefficient `1::Int` |
| `Single{V}(v)` | a scalar (grade 0) |
| `Single{V}(v::TensorTerm)` | `v` unchanged |
| `Single{V}((bits::UInt, v))` | `Single{V}(v, Submanifold{V}(bits))` |
| `Single{V}(v, b::TensorAlgebra)` | `v*b` |
| `Single{V,G}(v, b)` | `Zero(V)` if `order(v)+order(b) > diffmode(V)` (tangent truncation), else `Single{V,G,b,T}(v)` |
| `Single{V}(v, b::Single)` | `Single{V,G,basis(b)}(v*b.v)` (DS:489-493) |

Conversions (DS:496-508):

* `Real(m)`, `Float64(m)`, `Int(m)`, `Bool(m)`, `Rational(m)` all give `value(m)`.
* `Complex(grade-0) = (v, 0)`, `Complex(grade>0) = (0, v)`.

`Submanifold` conversions (DS:576-588): `Float64(b) = 1.0`, `Complex(v12) = 0+1im`, `Complex(One) = 1+0im`, `Complex(Zero) = 0+0im`. `Infinity` converts to `Inf` (DS:644-647).

### 4.2 Conversions between containers (verified)

| from → to | rule | example (N=3, `@basis 3`) |
|---|---|---|
| Chain{G} → Multivector | embed at `binomsum(N,G)` | `Multivector(Chain{V,1}(4,5,6))` = `0 + 4v₁ + 5v₂ + 6v₃` |
| Chain{G even} → Spinor | embed at `spinsum` | `Spinor(Chain{V,2}(1,2,3))` = `0 + 1v₁₂ + 2v₁₃ + 3v₂₃` |
| Chain{G odd} → CoSpinor | embed at `antisum` | `CoSpinor(Chain{V,1}(4,5,6))` = `4v₁ + 5v₂ + 6v₃ + 0v₁₂₃` |
| Spinor/CoSpinor → Multivector | scatter by parity | `Multivector(CoSpinor{V}(5,6,7,8))` = `0 + 5v₁ + 6v₂ + 7v₃ + 8v₁₂₃` |
| Couple → Multivector | scalar + imaginary | `Multivector(Couple{V,v12}(1,2))` = `1 + 2v₁₂` |
| PseudoCouple → Multivector | imaginary + volume | `Multivector(PseudoCouple{V,v1}(3,4))` = `0 + 3v₁ + 4v₁₂₃` |
| Couple{even B} → Spinor | adderspin | `Spinor(Couple{V,v12}(1,2))` = `1 + 2v₁₂ + 0v₁₃ + 0v₂₃` |
| PseudoCouple{odd B, odd N} → CoSpinor | adderanti | `CoSpinor(PseudoCouple{V,v1}(3,4))` = `3v₁ + 0v₂ + 0v₃ + 4v₁₂₃` |
| Couple → Complex | `(re, im)` | `Complex(Couple{V,v12}(1,2))` = `1 + 2im`; `Complex(PseudoCouple{V,v1}(3,4))` = `3 + 4im` |
| Imaginary (Spinor N=2) → Couple/Complex | `Complex(value(m)...)` | `Complex(Spinor(1,2))` = `1 + 2im` |
| Phasor → Couple | `complexify` | §4.8 |

`multispin(t)` (MV:999-1014) picks the smallest spinor-family container:

* Multivector, Spinor and CoSpinor are returned as-is.
* A graded element becomes `Spinor` if its grade is even, else `CoSpinor`.
* `Couple{V,B}` becomes `Spinor` if `grade(B)` is even, else `Multivector`.
* `PseudoCouple{V,B}` becomes `Spinor` if V and B are both even-graded, `CoSpinor` if both are odd, else `Multivector`.

Oracle: `multispin(Couple{V,v1}(1,2))` gives `1 + 2v₁ ::Multivector`, and `multispin(PseudoCouple{V,v12}(1,2))` gives `0 + 1v₁₂ + 2v₁₂₃ ::Multivector`.

### 4.3 Indexing semantics (verified; N=3, `c1=Chain{V,1}(4,5,6)`, `c2=Chain{V,2}(1,2,3)`, `m=Multivector{V}(1..8)`, `s=Spinor{V}(1,2,3,4)`, `a=CoSpinor{V}(5,6,7,8)`, `z=Couple{V,v12}(1,2)`, `p=PseudoCouple{V,v1}(3,4)`)

| expression | meaning | result |
|---|---|---|
| `c1[i::Int]` | component, 1-based (MV:96) | `c1[2]=5`; `c1[0]` or `c1[4]` give BoundsError |
| `c1[2:3]`, `c1[[3,1]]` | raw components | `[5,6]`, `[6,4]` |
| `c1[b::Submanifold{V,G}]` | component at `bladeindex` (MV:162) | `c1[v2]=5` |
| `c1[b::Submanifold{V,other G}]` | `zero(T)` (MV:163) | `c1[v12]=0` |
| `c1[[v1,v3]]` | broadcast | `[4,6]` |
| `c[i,j]` for a Chain of Chains | `c[j][i]` (MV:99) | |
| `c1(i::Int)`, `c1(Val(i))` | the i-th term as a `Single` (MV:165-170) | `c1(2)=5v₂` |
| `c1.v` | the field `Values` | `[4,5,6]` |
| `c1.v2` | `c1[bladeindex]*B` if the grade matches, else `zero(T)*B` (MV:172-179) | `5v₂`; `c1.v12=0v₁₂` |
| `c2.v21` | parsed with a reorder sign (DSb:134) | `-1v₁₂` |
| `firstindex`, `lastindex`, `length` of a Chain | `1`, `C(N,G)`, `C(N,G)` (MV:101-103) | `(1,3,3)` |
| `m[g::Int]` | **grade block as `Values`**, for `0 ≤ g ≤ N` (MV:305-309) | `m[0]=[1]`, `m[2]=[5,6,7]`; `m[4]` gives BoundsError |
| `m[Val(g)]` | grade block (MV:310-314) | |
| `m(g::Int)`, `m(Val(g))`, `grade(m,g)` | grade block as a `Chain{V,g}` (MV:300-304, 315-316, 325) | `m(2)=5v₁₂ + 6v₁₃ + 7v₂₃` |
| `m(g,i)` | the i-th term of grade g as a `Single` (MV:326-329) | `m(2,3)=7v₂₃` |
| `m[2:4]`, `m[[1,8]]` | **raw components** (1-based!) (MV:318-319) | `[2,3,4]`, `[1,8]` |
| `m[b::Submanifold]` | intended as the component at `basisindex`, but it calls `m[Int]`, i.e. the grade block. **Bug** (MV:405). | `m[v]=[2,3,4]`; `m[v13]` gives BoundsError |
| `m.v13` | **bug**: uses `bladeindex` instead of `basisindex` (MV:336) | `2v₁₃` (true coefficient: 6) |
| `firstindex`, `lastindex`, `length` of a Multivector | `0`, `N`, `2^N` (MV:321-323) | `(0,3,8)` |
| `s[g::Int]` | even g: block at `spinsum`; odd g: zeros (MV:521-530) | `s[1]=[0,0,0]`, `s[2]=[2,3,4]` |
| `s[Val(odd)]` | a zero `FixedVector` (MV:531-536) | |
| `s(g::Int)` | a Chain (a **zero Chain** for odd g) (MV:509-514) | `s(1)=0v₁ + 0v₂ + 0v₃` |
| `s(Val(odd))`, `s(odd,i)` | `Zero(V)` (MV:544-552) | `𝟎` |
| `s[v12]`, `s.v12` | **not defined** (getproperty commented out, MV:572-587) | MethodError / FieldError |
| `firstindex`, `lastindex`, `length` of a Spinor | `0`, `N`, `2^(N-1)` (MV:441-443) | `(0,3,4)` |
| CoSpinor indexing | mirror image of Spinor | `a[0]=[0]`, `a(0)=0v`, `a(Val(2))=𝟎` |
| `z(G)`, `z(Val(G))` | `imaginary` if `G = grade(B)`; `scalar` if `G = 0`; else `Zero` (MV:723-726) | `z(0)=1v`, `z(2)=2v₁₂`, `z(1)=𝟎` |
| `p(G)` | `imaginary` if `G = grade(B)`; `volume` if `G = N`; else `Zero` | `p(1)=3v₁`, `p(3)=4v₁₂₃` |
| `grade(z, Val(G))` | **raw value** (not a Single) (MV:670, MV:697) | `(1, 2, 𝟎)` |
| `z.v12`, `z.v13` | imag·b, else real·b for grade 0, else 0·b (MV:728-741) | `2v₁₂`, `0v₁₃`; `z.v21=-2v₁₂` |
| `p.v1`, `p.v123` | (MV:742-755) | `3v₁`, `4v₁₂₃` |
| `length(z)` | `2` (MV:841) | |
| Submanifold `v1[i]` | Bool: is index i in the mask? For a space `V[i]` gives metric values (DS:283-312) | `v1[1]=true`; `V[:]=[1,1,1]`; for `S"-++"`, `.v12[:]=[-1,1]` |
| `v12(g)`, `V(i...)` | grade filter `v12(1)=𝟎`; `V(1,3)=⟨1_1⟩` (DSg:23-35) | |

### 4.4 Grade projections (MV:1107-1144, DSg:94-103, AT:183-205)

| fn | Chain{G} | Multivector | Spinor | CoSpinor | Couple{B} | PseudoCouple{B} |
|---|---|---|---|---|---|---|
| `scalar` | self if G=0 (as `Single{V}(t.v[1])`), else `Zero` | `Single{V}(v[1])` | `Single{V}(v[1])` | `Zero` | `Single{V}(re)` | `Single(re)` if grade(B)=0, else `Zero` |
| `vector` | self or `Zero` | `t(Val(1))` (a Chain) | `Zero` | `t(Val(1))` | `imaginary` if grade(B)=1, else `Zero` | `imaginary` if grade(B)=1; `volume` if grade(V)=1; else `Zero` |
| `bivector` | | `t(Val(2))` | `t(Val(2))` | `Zero` | `imaginary` if grade 2 | analogous |
| `trivector` | | `t(Val(3))` | `Zero` | `t(Val(3))` | **bug**: `imaginarya` is undefined, so it throws `UndefVarError` (MV:1124) | analogous |
| `volume` / `pseudoscalar` | `Single{V,G,basis(V)}` when length 1 (MV:1130) | `Single{V,N,I}(v[end])` | `v[end]` if N is even, else `Zero` | `v[end]` if N is odd | `Single(im)` if grade(B)=grade(V) | `Single{V,N,I}(im)` |
| `imaginary` | | | `bivector` for Quaternion only (MV:1138) | `vector` for AntiQuaternion (MV:1139) | `Single{V,grade(B),B}(im)` | `Single{V,grade(B),B}(re)` (!) |

Predicates (MV:1140-1154):

* `isscalar(t) = norm(t) ≈ norm(scalar(t))`, and likewise `isvector`, `isbivector`, `istrivector`, `isvolume`. These are **approximate, norm-based** predicates: `isscalar(Chain{V,1}(0,0,0)) == true`.
* `isscalar(::Phasor{V,<:TensorGraded})`: if `B*B == -1`, test `Real(angle)%π ≈ 0`, else `isscalar(complexify)`. This errors for Irrational angles (`rem not defined for Irrational{:π}`).

### 4.5 The `+`/`-` representation lattice ("promotion")

Dispatch starts at `Base.:+(a::TensorAlgebra, b::TensorAlgebra) = plus(a,b)` (AT:294). If `V` differs, `interop` first maps both operands into `V∪W` (AT:246-265). Scalars (`NSE = Union{Symbol,Expr,Real,Complex}`, AL:740) combine as follows (PR:852-859):

* `x + 0 = x` (no type change)
* `x + n = x + n*One(V)`
* `0 + x = +x`
* `0 - x = -x`

With Zero (PR:379-398, PR:445-448):

* `Zero + x = x`
* `x - Zero = x`
* `Zero - x = -x`
* `Zero + number = Single{V}(number)`

Term + term (`adder`, AL:747-780). Here `a::TensorTerm{V,L}`, `b::TensorTerm{V,G}`, `ok = !istangent(V) && !hasconformal(V)`, and `±` is the operator applied to `b`:
```
if basis(a) == basis(b):         Single{V,L}(a ± b)            # e.g. v1-v1 → 0v₁  (NOT Zero)
elif ok && L == 0:               Couple{V,basis(b)}(a, ±b)
elif ok && G == 0:               Couple{V,basis(a)}(±b, a)
elif ok && L == grade(V):        PseudoCouple{V,basis(b)}(±b, a)
elif ok && G == grade(V):        PseudoCouple{V,basis(a)}(a, ±b)
elif L == G:                     Chain{V,L} one-hot pair
elif L even && G even:           Spinor{V}
elif L odd && G odd:             CoSpinor{V}
else:                            Multivector{V}
```
Coefficient type: `promote_type(valuetype(a), valuetype(b))`.

In generated code, `mvec`/`svec` pick `t = promote_type(...)`. If a type is "fixed" (`BigInt`, `BigFloat`, `Rational{BigInt}`, `Complex{Big*}`, or a non-Number, AL:731-738), the `Sym.∑`/`Sym.-` scalar ops are used instead.

Term + container (AL:831-1040) and container + container (PR:860-941):

* Adding into the **same-grade Chain** keeps a Chain.
* Chain{G} + term{L} with L≠G: a scalar term against a pseudoscalar Chain (or vice versa) gives Couple; against grade 0 gives Couple; against grade N gives PseudoCouple. Otherwise the result follows the parity rule into Spinor, CoSpinor or Multivector.
* Chain + Chain of different grades (PR:880-886):
  1. If either chain has grade 0 or N, it is first reduced with `Single(·)`.
  2. Same parity goes to `multispin`.
  3. Otherwise both become Multivector.

  Oracle: `Chain{V,1}+Chain{V,3}` gives CoSpinor, `Chain{V,0}+Chain{V,2}` gives Spinor (Quaternion), and `Chain{V,1}+Chain{V,2}` gives Multivector.
* Spinor + CoSpinor gives Multivector (PR:566-567). Anything + Multivector gives Multivector.
* Couple + Couple with the same B stays a Couple. With a different B it expands (PR:557-565).
* Couple/PseudoCouple + container splits into `scalar/volume` + `imaginary` (PR:530-553).
* TensorTerm + Couple (PR:632-665): if `basis(a) == B` (or `a` is a scalar), the result stays a Couple; otherwise `a + multispin(b)`.
* Phasor + x: `complexify` first. Phasor + Phasor gives `polarize(sum)` (PR:483-488).

Resulting **type table** (entry = kind of `row + col`). Oracle output from `jl_types/t5.out`, N=3, `V=⟨111⟩`. Notation: `Sub{G}` = Submanifold; `Single{G}`; `C{G}` = Chain; `Cpl{B}` = Couple; `PC{B}` = PseudoCouple; `Sp` = Spinor; `CoSp`; `MV`.

```
            Zero   One     s0      e1      2e1     2e2     2e12    2e13    e123     C1     C2     Cpl12   Cpl1    PC1    Sp     CoSp   MV
Zero      | Zero  One     S{0}    Sub{1}  S{1}    S{1}    S{2}    S{2}    Sub{3}   C{1}   C{2}   Cpl12   Cpl1    PC1    Sp     CoSp   MV
One       | One   S{0}    S{0}    Cpl1    Cpl1    Cpl2    Cpl12   Cpl13   Cpl123   MV     Sp     Cpl12   Cpl1    ERR*   Sp     MV     MV
s0        | S{0}  S{0}    S{0}    Cpl1    Cpl1    Cpl2    Cpl12   Cpl13   Cpl123   MV     Sp     Cpl12   Cpl1    ERR*   Sp     MV     MV
e1        | Sub1  Cpl1    Cpl1    S{1}    S{1}    C{1}    MV      MV      PC1      C{1}   MV     MV      Cpl1    PC1    MV     CoSp   MV
2e1       | S{1}  Cpl1    Cpl1    S{1}    S{1}    C{1}    MV      MV      PC1      C{1}   MV     MV      Cpl1    PC1    MV     CoSp   MV
2e2       | S{1}  Cpl2    Cpl2    C{1}    C{1}    S{1}    MV      MV      PC2      C{1}   MV     MV      MV      ERR*   MV     CoSp   MV
2e12      | S{2}  Cpl12   Cpl12   MV      MV      MV      S{2}    C{2}    PC12     MV     C{2}   Cpl12   MV      ERR*   Sp     MV     MV
2e13      | S{2}  Cpl13   Cpl13   MV      MV      MV      C{2}    S{2}    PC13     MV     C{2}   Sp      MV      ERR*   Sp     MV     MV
e123      | Sub3  Cpl123  Cpl123  PC1     PC1     PC2     PC12    PC13    S{3}     CoSp   MV     MV      MV      ERR*   MV     CoSp   MV
C1        | C{1}  MV      MV      C{1}    C{1}    C{1}    MV      MV      CoSp     C{1}   MV     MV      MV      CoSp   MV     CoSp   MV
C2        | C{2}  Sp      Sp      MV      MV      MV      C{2}    C{2}    MV       MV     C{2}   Sp      MV      MV     Sp     MV     MV
Cpl12     | Cpl12 Cpl12   Cpl12   MV      MV      MV      Cpl12   Sp      MV       MV     Sp     Cpl12   MV      MV     Sp     MV     MV
Cpl1      | Cpl1  Cpl1    Cpl1    Cpl1    Cpl1    MV      MV      MV      MV       MV     MV     MV      Cpl1    MV     MV     MV     MV
PC1       | PC1   MV      MV      PC1     PC1     CoSp    MV      MV      PC1      CoSp   MV     MV      MV      PC1    MV     CoSp   MV
Sp        | Sp    Sp      Sp      MV      MV      MV      Sp      Sp      MV       MV     Sp     Sp      MV      MV     Sp     MV     MV
CoSp      | CoSp  MV      MV      CoSp    CoSp    CoSp    MV      MV      CoSp     CoSp   MV     MV      MV      CoSp   MV     CoSp   MV
MV        | MV (all)
```
`ERR*` is the `Subamnifold` typo bug (PR:651), which fires for `term + PseudoCouple` whenever `basis(term) ≠ B`.

For N=4 (full table in `jl_types/t5.out`), note the differences: `e1 + e123` gives **CoSpinor** because e123 is no longer the pseudoscalar, and `e1234` behaves as the pseudoscalar (`One + e1234 → Couple{v1234}`, `e1 + e1234 → PC{v1}`, `C2 + e1234 → Spinor`).

Conformal and tangent spaces never form Couple/PseudoCouple:

* `@basis S"∞∅++"`: `1+v∞` gives `Multivector`; `v∞*v∅` and `1+v∞∅` give a `Spinor` of length 8 (prints all even terms).
* `@basis tangent(ℝ^2)`: `1+v1` gives Multivector; `v1+v2` gives `Chain` (`1v₁ + 1v₂ + 0∂₁`).

Value-level bug:

* `PseudoCouple{V,B}+PseudoCouple{V,B}` computes `(re_a ± im_b, im_a ± im_b)` (PR:558). Oracle: `PC{v1}(1,2)+PC{v1}(1,2)` gives `3v₁ + 4v₁₂₃` (correct: `2v₁ + 4v₁₂₃`).
* The `minus` sibling likewise gives `-6v₁ - 5v₁₂₃` for `(1,2)-(5,7)`.

Unary minus (PR:514-520): `-(v::Submanifold) = Single(-1, v)`, so `-v1` gives `-1v₁`. The container versions negate the `Values`.

### 4.6 Equality and approximate equality

* `==` on two TensorAlgebras calls `equal(a,b)` (AT:298), after `interop` to `V∪W`.
* Number vs graded (LZ:89-94, MV:118-125): `n == t` iff (G == 0 and `n == value`) or (G > 0 and `n == 0` and all components are 0). So `2 == 2v` is true, `2 == 2v1` is false, and `0 == Chain{V,1}(0,0,0)` is true.
* Term vs term (DS:510): same basis compares values; different bases require both values to be 0.
* Chain vs Chain (MV:126-129): the same grade compares elementwise (`1 == 1.0` is ok); different grades require both to be all-zero.
* Chain vs Term (MV:181-193): the term's component must match and every other component must be 0.
* Multivector vs Chain (MV:359-364): grade block equal, everything else 0.
* **Multivector vs Term** (MV:365-368) reads out of bounds, because the range ends at `2<<N` instead of `1<<N` under `@inbounds`. **This crashed the Julia process (SIGILL)**. Port it correctly.
* **Number vs Multivector/Spinor** (MV:370-375, MV:640-647) raises `UndefVarError: V not defined`, because the `where` clause binds `V` inside the parameter scope. Port the intent: `n == m ⇔ m[1] == n && all others == 0`. `n == CoSpinor` is `iszero(b)`.
* Couple vs Couple with **different** B (MV:771): `re_a == re_b && im_a == im_b == 0`. Same B (MV:787): componentwise. Oracle: `Couple{v1}(1,0) == Couple{v2}(1,0)` is true; with imaginary part 2 it is false.
* The PseudoCouple analogues sit at MV:773 and MV:792. **Bug** at MV:795: `$eq(imagvalue(b),value(b))` should read `imagvalue(a)`. Also MV:774 compares `realvalue(a)≈imagvalue(b)≈0`.
* Couple/PseudoCouple vs containers go through `multispin` (MV:808-819).
* Phasor vs Phasor: amplitude and angle equal (MV:953). Phasor vs Couple compares via `complexify`.
* `isapprox`:
  * Chain/Chain of the same grade: **componentwise** `≈` (MV:128), so `0 ≈ 1e-20` is false.
  * Multivector/Spinor/CoSpinor: `Manifold` equal and `value ≈ value` (vector norm ≈) (MV:1103-1105).
  * Generic TensorAlgebra: norm-based (AT:229-240); graded elements of different rank require both to be null.
* `iszero(t) = norm(t) ≈ 0` (AT:445), so it is effectively exact zero. `isone(t) = norm(t) ≈ value(scalar(t)) ≈ 1` (AT:446).
* `Zero == x ⇔ iszero(x)`; `Infinity == x ⇔ isinf(norm(x))` (DS:606-673).

### 4.7 zero / one summary

| type | `zero(x)` | `one(x)` |
|---|---|---|
| Submanifold | `Zero(V)` | `One(V)` (DSb:289-296) |
| Single | `Single{V}(0)` (scalar, prints `0v`) | `Single{V}(1)` (DSb:297-300) |
| Chain{V,G,T} | zero Chain of the same G | **grade-0** `Chain{V,0}(1)` (prints `1v`) |
| Multivector | zeros (prints `0v⃖`) | `zero + One` (prints `1v⃖`) |
| Spinor | zeros | `Spinor(1, One)` |
| CoSpinor | zeros | **undefined (hangs)** |
| Couple | `(0,0)` | `(1,0)` |
| PseudoCouple | `(0,0)` | undefined |
| Phasor | `Phasor{V}(zero(T), zero(B))` | `Phasor{V}(one(T), zero(B))` |

### 4.8 Complex-like types: Couple, PseudoCouple, Phasor, quaternions (MV:669-1090)

* `abs2(Couple{V,B}) = re² + im²·abs2_inv(B)`. `abs2_inv(B) = abs2(getbasis(V, grade_basis(V,B)))` (AL:473), i.e. `~B⟑B` as a scalar: +1 in Euclidean spaces, −1 for `S"-.."` vectors. Oracle: `abs2(Couple{V,v12}(1,2)) = 5v`.
* `abs2(PseudoCouple{V,B})` (MV:689-696): `out = re²·abs2_inv(B) + im²·abs2_inv(V)`. If `(~B)*I ≠ (~I)*B`, return `out`; otherwise add `2·complementrighthodge(B)·re·im`. Oracle: `PC{v12}(1,2)` gives `5 + 4v₃`; `PC{v1}(3,4)` gives `25v`.
* `radius(Couple) = sqrt(re² − im²·value(B*B))` (MV:912-913). `radius(Real|Complex) = abs`. `radius(TensorAlgebra) = Real(abs)`. `radius(Phasor) = radius(amplitude)`.
* Phasor accessors:
  * `amplitude(Phasor) = z.v`
  * `angle(Phasor) = z.ω`
  * `unitangle`: `basis(angle)` if the angle is a TensorTerm, `1` for Real, `1im` for Complex, else `unit(angle)` (MV:885-890)
  * `phase`: `0` for Real amplitudes, else `angle(amplitude)/unitangle` (MV:895-901)
  * `realvalue(Phasor) = Real(radius)`; `imagvalue = Real(angle + phase·unitangle)` (MV:868-869)
* `complexify(Phasor{V,B,T})` (MV:1031-1044) is "simple" if `T<:Real || B<:Real || T<:Scalar || B<:Scalar || (_phasor_type(B) && _phasor_type(T))`.
  * Simple: `amplitude * exp(angle)`.
  * Otherwise: `amplitude ⊘ exp(angle/2)` (sandwich).
  * Note the real-angle case: `complexify(Phasor(1.0,2.0)) = e² = 7.389…` (a real exponential, not a complex one).
* Other `complexify` methods (MV:1046-1052):
  * `Chain{V,1,T,2}` gives `Couple{V,Submanifold(V)}(x,y)`
  * `Couple`, `Complex` and `Spinor` are the identity
  * `PseudoCouple` gives `!t` (complement): `complexify(PC{v1}(3,4)) = 4 + 3v₂₃`
  * `TensorTerm` gives `Couple(t)`; `Real` gives `Complex(t)`
* `polarize` (MV:1054-1066):
  * `Chain{V,1,T,2}` gives `Phasor{V}(t[1], t[2]*I)`. **The chain is read as (amplitude, angle), not as x+iy**: `polarize(Chain(3.0,4.0)) = 3.0 ∠ 4.0v₁₂`.
  * `Complex` goes through `Couple`.
  * `One` gives `Phasor(1,0)`; a Submanifold `m` gives `Phasor(1,m)`; a scalar term gives `Phasor(value,0)`; any other term `m` gives `Phasor(1,m)`.
  * `Couple` and `Spinor` give `Phasor(radius, angle)`.
  * Oracle: `polarize(Couple{V,v12}(1.0,1.0)) = 1.4142135623730951 ∠ 0.7853981633974483v₁₂`.
* Phasor evaluation (MV:1016-1029):
  * `(z::Phasor)(t) = Phasor{V}(amplitude, angle*t)`
  * `(z)(t,θ) = Phasor{V}(amplitude*exp(θ*unitangle), angle*t)` in the simple case, else the sandwich form
  * `z((t,θ))` is also accepted
  * `z(::Chain{…,2})` references an undefined `θ` (bug)
* `vectorize` (MV:1068-1074):
  * `Couple{V,B}` gives `Chain{_subspace(V,B),1}(re,im)`. `_subspace(V,B)` returns V itself if `grade(V) == grade(B)`, else the subspace `Submanifold{V,G,B}()` spanned by B's indices (MV:1076-1077). Oracle: `vectorize(Couple{V,v13}(1,2)) = 1v₁ + 2v₃ ::Chain{⟨1_1⟩,1,Int64,2}`.
  * `Phasor` gives `(amplitude, angle)` on `_subspace(V, unitangle)`.
  * `PseudoCouple` gives `vectorize(!t)`; `Complex` gives `Chain(re,im)`; `Chain` is the identity.
  * A grade-1 term gives `Chain(t)`; any other term gives `vectorize(Couple(t))`.
* Quaternions (MV:1079-1090):
  * `quaternion(V=Submanifold(3), s, i=0, j=0, k=0) = Spinor{V}(Values(s, i, -j, k))`, so `i=v12`, `j=-v13`, `k=v23`. The overloads accept a 4-tuple, `(s, 3-tuple)`, or `Values`.
  * `quatvalue(q::Quaternion) = (q[1], q[2], -q[3], q[4])`.
  * `quatvalue(q::AntiQuaternion) = (q[4], q[3], q[2], q[1])`.
  * `quatvalue(q::TensorAlgebra) = quatvalues(Spinor(even(q)))`: `quatvalue(Multivector(1..8)) = [1,5,-6,7]`.
  * **Conflicting convention:** `𝕚,𝕛,𝕜 = hyperplanes(ℝ3) = (v23, -v13, v12)` (GJ:71). This is the reverse of `quaternion`'s `(v12, -v13, v23)`. Both have `i*j*k = 1v`.

### 4.9 Zero / One / Infinity arithmetic (DS:552-683, PR:379-477)

* `Zero*x = Zero` and `number*Zero = Zero`.
* `inv(Zero) = Infinity`; `inv(Infinity) = Zero`.
* `Zero^0 = One`, `Zero^-1 = ∞`, `Zero^2 = 𝟎`; `∞^0 = One`, `∞^-1 = 𝟎`, `∞^2 = ∞` (PR:463-477). Oracle: `(v, ∞, 𝟎)` and `(v, 𝟎, ∞)`.
* `Infinity + number` is **ambiguous** in Julia (MethodError). Port it as `Infinity`.
* `One*x = x`; `One+One = 2v` (a Single).
* `reverse`, `conj`, `involute`, `hodge` and the complements of `Zero`/`Infinity` return the element itself (DS:618-620, DS:677-679).

### 4.10 Top-level functions in `GJ`

* **`hyperplanes(V)`** (GJ:62) = `map(n -> UniformScaling{Bool}(false)*getbasis(V,1<<n), 0:rank(V)-1-diffvars(V))`.
  * `(V::Submanifold)(::UniformScaling{Bool})` returns the **positive** pseudoscalar regardless of λ (DS:533-536). So this is `[I⟑v_k]`.
  * Oracle: `ℝ2` gives `[-1v₂, 1v₁]`; `ℝ3` gives `[1v₂₃, -1v₁₃, 1v₁₂]`; `ℝ4` gives `[-1v₂₃₄, 1v₁₃₄, -1v₁₂₄, 1v₁₂₃]`.
* **`(::Signature|DiagonalForm)(::SubAlgebra{V})`** (GJ:64-66) = `Multivector{V,Int}(ones(2^N))`. Golden: `S"+++"(Λ(S"+++")) = 1 + 1v₁ + 1v₂ + 1v₃ + 1v₁₂ + 1v₁₃ + 1v₂₃ + 1v₁₂₃`.
* **`(V::Signature{N})(d::Derivation{T,O})`** and the Submanifold twin (GJ:88-107):
  ```
  if O < 1 || diffvars(V) == 0:  return Chain{V,1,Int}(λ * ones(N))   # ℝ3(∇) == ℝ3(Δ) == v1+v2+v3
  G = grade(V); D = diffvars(V)==1; C = isdyadic(V); G2 = (C ? G/2 : G) - 1
  ∇ = Σ_{k=0}^{G2} getbasis(V, 1<<(D ? G : k+G)) ⟑ getbasis(V, 1<<k)
  O == 1 → ∇
  x = (∇⋅∇)^((O even ? O : O-1)/2)
  O odd → Σ_k (x ⟑ getbasis(V,1<<(k+G))) ⟑ getbasis(V,1<<k)   else x
  ```
  Oracle: `tangent(ℝ^3)(∇) = 0v₁₂ + 0v₁₃ + 1∂₁v₁ + 0v₂₃ + 1∂₁v₂ + 1∂₁v₃`.
* Derivations times containers: `Derivation*Chain/Multivector = V(a)*b` (GJ:79-84); `⊘` likewise (GJ:85-86).
* Boundary and friends:
  * `∂(ω::Chain{V,1,<:Chain{W,1}}) = ∧(ω)⋅Λ(W).v1` (simplex boundary, GJ:109)
  * `∂(ω) = ω⋅Manifold(ω)(∇)`, `d(ω) = Manifold(ω)(∇)∧ω`, `δ(ω) = -∂(ω)` (GJ:110-112)
  * Oracle: `∂(Λ(ℝ5).v123) = 1v₁₂ - 1v₁₃ + 0v₁₄ + … + 1v₂₃ + …` and `∂(Λ(ℝ5).v12) = -1v₁ + 1v₂ + 0v₃ + 0v₄ + 0v₅`.
* **Homology helpers** (GJ:121-162), with `d = count_gdims(t)` (a vector of length N+1):
  * `boundary_rank(t, d)`: `out = count_gdims(∂t)`, then `out[1] = 0`, and `out[k] = min(out[k], d[k+1])` for `k = 2..len-1`.
  * `boundary_null`: `out[k] = d[k+1] - r[k]` for `k = 1..l-1`.
  * `betti`: `out[k] = d[k+1] - r[k] - r[k+1]` for `k = 1..l-1`.
  * These return `Values`. The oracle gives nonsense for the skeleton tests (`betti(skeleton(Λ(ℝ4).v1234)) = [0,-2,-1,0]`), because `skeleton` itself is quirky (next item). **Do not use them as goldens.**
* **`project` (↑)** (GJ:164-190), dispatched on `V`:
  * No ∞/∅: the identity.
  * Conformal: `↑ω = (v∞·½)·((~ω)⋅ω) + v∅ + ω`.
  * One of ∞/∅: with `ω2 = (~ω)⋅ω` and `iω2 = inv(ω2+1)`, `↑ω = b·((ω2−1)·iω2) + (2·iω2)·ω` where `b = v∞` or `v∅` (stereographic).
  * A non-basis Submanifold returns `supermanifold(V)`.
  * Variants: `project(ω,b)` and `project(ω,p,m)`.
  * Oracle, conformal: `↑(1.0v1+2.0v2) = 0.0 + 2.5v∞ + 1.0v∅ + 1.0v₁ + 2.0v₂` (a Multivector). ∞-only: `↑(1.0v2+2.0v3) = 0.666667v∞ + 0.0v₁ + 0.333333v₂ + 0.666667v₃`.
* **`reject` (↓)** (GJ:192-210):
  * Conformal: `((v∞∅∧ω)⋅inv(one·~v∞∅)) / (−ω⋅v∞)`.
  * Single-point: `(~(ω∧b)⋅b)/(1−b⋅ω)`.
  * No ∞/∅: the identity.
  * On spaces it returns `V(2:N)` or `V(3:N)`, which errors (no UnitRange method).
  * Also `reject(ω,b)` and `reject(ω,∞,∅)`.
* **Simplicial helpers**:
  * `absym` takes the coefficientwise `abs` (GJ:234-238).
  * `collapse(a,b) = a⋅absym(∂(b))` segfaulted the Julia compiler in the oracle.
  * `chain(t, Val(T)=Val(true))` (GJ:242-255): for a term with `G = popcount(symmetricmask)` ≥ 2, it builds the grade-2 chain of consecutive index pairs `(i_{k-1}, i_k)`, plus the closing pair `(i_1, i_G)` with sign `-v` (only if `T` or `G == 2`). `path(t) = chain(t, Val(false))`. Oracle: `chain(v1234) = 1v₁₂ + 0v₁₃ - 1v₁₄ + 1v₂₃ + 0v₂₄ + 1v₃₄`; `path(v1234) = 1v₁₂ + 0v₁₃ + 0v₁₄ + 1v₂₃ + 0v₂₄ + 1v₃₄`.
  * `skeleton` (GJ:261-287) recursively adds `absym(x) + skeleton(absym(∂x))`, accumulating into `g = 0`. Oracle: `skeleton(Λ(ℝ3).v123) = 0 + 2v₂ + 3v₃ + 1v₁₂ + 1v₁₃ + 1v₂₃ + 1v₁₂₃`, which is asymmetric in the vertices and so **suspect**.
  * `𝒫(t) = Δ(t,Val(false))` and `subcomplex` are **broken**: the call method on `Laplacian` is commented out (GJ:258), giving `MethodError: objects of type Laplacian are not callable`. The docs' `χ(Δ(ω))` example therefore fails.
* **Mesh helpers**:
  * `column(t,i=1) = getindex.(value(t),i)`; `columns(t,i,j)` (GJ:293-294)
  * `rows`, `pointset` (GJ:296-307)
  * `scalarfield(t,ϕ)`, `chainfield(t,ϕ)` do barycentric lookup over mesh elements (GJ:314-339)
  * `rectangle`, `rectanglefield` (GJ:341-348)

  These belong in a mesh/Cartan layer.
* **FFT glue** (GJ:350-358): arrays of grade-0 elements go to `Real`; arrays of graded elements go through `Couple`; Chains and Phasors go through `complexify`. **Skip it** (Julia-specific).
* **Code generation** (GJ:360-414):
  * `eval(generate_products(...))` for the default field, `Complex`, `Rational{BigInt}`, `BigFloat`, `BigInt`, `Complex{Big*}`, and `SymField`
  * `generate_algebra(m,t,mt,d,c)` registers a foreign scalar type (`*`, `iszero`, `+`/`-` with graded/mixed elements, inverses, derivations)
  * `generate_symbolic_methods`

  In Lean this becomes typeclass instances.
* **`__init__` / Requires extensions** (GJ:416-451): Reduce, Symbolics, SymPy, SymEngine, AbstractAlgebra, GaloisFields, LightGraphs, StaticArrays, Meshes, GeometryBasics, Makie, UnicodePlots, SpecialFunctions, EllipticFunctions, FewSpecialFunctions. **Skip.** Plotting interop is handled by the LeanPlot co-development.

### 4.11 Basis-generation machinery (DirectSum, used by Grassmann)

* **`generate(V)`** (DSb:36-47): `[Submanifold{V,0}(0)]` followed by, for each grade `g = 1..N` in lex order, `Submanifold{V,g}(bits)`. This is exactly the `basisindex` order.
* **`labels(V, vec="v", cov="w", duo="∂", dif="ϵ")`** (DSb:19-32) produces ASCII-digit symbol names in the same order, via `printlabel(…, label=true)`.
  * With `label=true`, indices 1..10 print as the *decimal number* (so index 10 prints as `10`).
  * Indices 11–36 print as `a…z`, and indices ≥ 37 as `A…Z`. ∞ prints as `∞` and ∅ as `∅`.
  * Consequence: the ASCII label `v110` means {1,10}, which is ambiguous. Oracle for N=11: `[:v, :v1, …, :v9, :v10, :va, :v12, …]`.
  * The pretty name of index 10 is `v₀`.
* **`alloc(V, sig=:V, vec, cov, duo, dif)`** (DSb:57-78) is what `@basis` expands into. It binds:
  * `V = Submanifold(V)`
  * `v = One` (the scalar)
  * for each blade i ≥ 2: **both** its pretty name (for example `v₁₂`, the Symbol of its `show` string) and its ASCII label (`v12`)
  * `v⃖ = "v"` (**a String**, likely a bug)
  * `𝟎 = Zero(V)`, `∞ = Infinity(V)`

  It returns the tuple `(V, v, v1, v2, …)` over the ASCII labels.
  * Macro expansion for `S"+-"`: `V = ⟨+-⟩; v = v; v₁ = v₁; v1 = v₁; v₂ = v₂; v2 = v₂; v₁₂ = v₁₂; v12 = v₁₂; v⃖ = "v"; 𝟎 = 𝟎; ∞ = ∞; (V, v, v1, v2, v12)`.
  * For `N > algebra_limit` it uses `generate(V)` rather than the cached `Λ(V).b`.
* Macro variants:
  * `@basis q sig vec cov duo dif` (DSb:88-92); `q` may be a Symbol/Expr (evaluated), an `Int`, or a string (via `Manifold(q)`)
  * `@basis_str` (DSb:94)
  * `@dualbasis` binds `V'` under the name `VV` with prefix `w` (DSb:106-112)
  * `@mixedbasis` binds `V⊕V'` as `W` plus both parts (DSb:122-132)
* **`Basis{V}`** (= `Λ`, DSb:158-202) has fields `b::Values{2^N, Submanifold{V}}` and `g::Dict{Symbol,Int}` (label → position).
  * `getindex(Λ, i::Int)` is the i-th blade (1-based, `basisindex` order); `[:]` returns all; `[range]` returns a vector.
  * `getproperty(Λ, :sym)` looks the symbol up in `g`, falling back to `lookup_basis(V, sym)`, which parses **arbitrary order and repeated indices** with sign:
    * `Λ(3).v32 = -1v₂₃`
    * `Λ(3).v21 = -1v₁₂`
    * `Λ(62).v32a87Ng = -1v₂₃₇₈agN`
    * `Λ(S"+++").v1231 = -1v₂₃`
    * out of range: `Λ(3).v4` gives BoundsError
  * `length = 2^N`. `show` prints `DirectSum.Basis{⟨111⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`.
  * `Λ(s)` means `getalgebra(s)`. It is cached per `(options, diffvars, diffmode, n, metric-hash, name)` in nested global vectors and dicts (DSb:226-268). `Λ(n::Int)` gives a Euclidean Int space.
* **`lookup_basis` / `indexparity`** (DSb:134-139, DSb:429-458, LZi:230-247):
  1. Split the name into a vector part (`v…`) and a covector part (`w…`).
  2. Map each character through `alphanumv`/`alphanumw` to an index.
  3. Bubble-sort: every adjacent swap toggles the parity.
  4. A repeated index `k` contracts in pairs: if `isone(s[k])` the parity toggles, and ∞ repeated gives `Zero`.
  5. Return `Single(-1, blade)` if the parity is odd, else the blade.

  **Quirk:** `s[k]` on a Submanifold returns an `Int` (+1 or −1), and `isone(+1)` is true. So **positive** squares flip the sign and negative ones do not: `Λ(S"+++").v11 = -1v` while `Λ(S"-++").v11 = v`. That is backwards relative to the metric. Do not replicate it; take the metric sign from the geometric product.
* **`getbasis(V, bits)`** (DSb:276-284) returns the cached blade for `N ≤ 8`, else constructs `Submanifold{V,popcount}(bits)`. `Submanifold{V}()` is `One` (DSb:286).
* `SparseBasis` (N ≤ 22) and `ExtendedBasis` (N ≤ 62) are lazy containers that print `…(v, ..., v₁₂₃…)` (DSb:309-376). In Lean all three collapse to one lazy structure.

### 4.12 Known bugs and quirks (decide per item: replicate only if the oracle must match)

| # | location | behavior | recommended port |
|---|---|---|---|
| 1 | MV:336 | `Multivector.getproperty` uses `bladeindex` (wrong coefficient) | use `basisindex`; exclude from goldens |
| 2 | MV:405 | `m[::Submanifold]` goes to grade indexing | component at `basisindex` |
| 3 | MV:367 | `equal(Multivector, Term)` reads past the end (crash) | correct bounds |
| 4 | MV:372, MV:642 | `Number == Multivector/Spinor` raises UndefVarError | implement the intent |
| 5 | PR:558 | PseudoCouple ± PseudoCouple uses `realvalue(a) ± imagvalue(b)` | correct formula |
| 6 | PR:651 | `Subamnifold` typo means `term + PseudoCouple` errors whenever the term's basis ≠ B | correct |
| 7 | MV:774, MV:795 | PseudoCouple equality/isapprox typos | correct |
| 8 | MV:1124 | `trivector(Couple)` uses `imaginarya` | correct |
| 9 | MV:269 | `Multivector(::Zero)` calls `zeros(::Expr)` | return the zero multivector |
| 10 | MV:252 | nested ternary in the `chain_src` large-N path uses `binomsum(N,G)` as a Bool | only reached for N ≥ 12; correct |
| 11 | MV:1017 | `(z::Phasor)(::Chain)` references an undefined `θ` | `z(value(t)...)` |
| 12 | MV:831 | `widen(::Couple)` has a misplaced paren | `Couple(widen(re), widen(im))` |
| 13 | MV:201-204 | `single(zero chain)` indexes `nothing` | return a zero Single or the chain |
| 14 | CO:898 | `evens(a,b)` with `b < a` has a negative length, so `Spinor` show for N=1 throws | handle empty ranges |
| 15 | MV:219-222 | `isbundle` is undefined | drop |
| 16 | CoSpinor | `one(::CoSpinor)` hangs; `Phasor{V}(::Complex)` hangs | define (or reject) explicitly |
| 17 | GJ:258-260 | `𝒫`/`subcomplex` call a non-callable `Δ` | port the intended `skeleton` semantics or drop |
| 18 | MV:16 and others | stale exports: `SparseChain MultiGrade angular radial coscalar eigprods pseudodot ⟂` | do not export |
| 19 | DSb:73 | `@basis` binds `v⃖` to the String `"v"` | bind to `One(V)` |
| 20 | LZi:236 | positive-square sign flip in the name parser | use the metric from the geometric product |
| 21 | MV:141 | `Chain(val, v::Submanifold)` is ambiguous | fine in Lean |
| 22 | products `Infinity + n` | ambiguous | return `Infinity` |

---

## 5. Display / printing

### 5.1 Leibniz primitives

* **Tables.** `vio = ('∞','∅')` (LZi:6), `alphanumv = "1234567890" * a-z * A-Z`, `alphanumw = digits * A-Z * a-z` (LZi:10-11).
  * `subs[k]` (LZi:14-28): `-1→'∞'`, `0→'∅'`, `1..9→'₁'..'₉'`, `10→'₀'`, `11..36→alphanumv[k]` (i.e. `a..z`).
  * `sups[k]` (LZi:31-45): `-1→'∞'`, `0→'∅'`, `1..9→'¹'..'⁹'`, `10→'⁰'`, `11..36→alphanumw[k]` (i.e. `A..Z`).
  * `pre = ("v","w","∂","ϵ")`, `PRE = ("X","x","Y","y")` (LZi:48-49).
* **`printindex(i, l=false, e="v", pre)`** (LZi:139-142):
  ```
  t = i > 36; j = t ? i-26 : i
  if l && 0 < j ≤ 10: return j                       # decimal digits (labels)
  return ((e ∉ (pre[1],pre[3])) xor t) ? sups[j] : subs[j]
  ```
  So vectors (`v`) and derivations (`∂`) get subscripts for i ≤ 36 and superscripts beyond, while covectors (`w`) and functions (`ϵ`) get the opposite. Index 37 prints as `A` and 62 as `Z`.
* **`printindices(io, indices, l, e)`** (LZi:145) prints `e` followed by each index char. An empty index list prints just `e`, so the scalar blade is `v`.
* **`printlabel(io, V, bits, label, vec, cov, duo, dif)`** (LZi:162-181):
  * Take `es = bits & ~diffmask`.
  * If there are no tangent bits, print `printindices(shift_indices(V, es))` with prefix `vec` (or `cov` if `dyadmode > 0`).
  * Otherwise print the tangent part with prefix `∂` or `ϵ` first, then the vector part (the order is `∂₁v₁`).
  * In dyadic (`V⊕V'`) spaces, the lower half gets `v` and the upper half gets `w` (for example `v₁w¹`).
  * `shift_indices` (LZi:122-131) maps index 1 to −1 (∞) when `hasinf`, maps the next one to 0 (∅) when `hasorigin`, and subtracts the shift from the rest.
* **`showvalue(io, V, B, x)`** (LZi:195-203):
  ```
  if showparens(typeof(x)):  print(io, "(", x, ")")    # Complex, Rational, Expr, non-term TensorAlgebra
  else:                      show(io, x); showstar(io, x)
  printindices(io, V, B)                                # the blade label
  ```
  * `showparens(T) = !check_parnot(T) && check_parval(T)`, with `parval = (Expr, Complex, Rational, TensorAlgebra)` and `parnot = (TensorTerm,)` (LZ:63-73).
  * `showstar(io,x)` (LZi:187-193) prints `"⊗"` if x is a TensorAlgebra; `""` if x is an Integer (non-Bool) or a finite AbstractFloat; `"*"` otherwise (Bool, NaN, Inf, Irrational, Symbol, …).

### 5.2 `showterm` (MV:46-58)

```
showterm(io, V, B, x, compact = io[:compact]):
  if check_parsym(T) && (T<:Real && signbit(x)) && !isnan(x):       # T ∈ Real ∪ Complex ∪ Symbol
      print(compact ? "-" : " - ")
      showvalue(io, V, B, (x is Signed, not BigInt, == typemin) ? -widen(x) : -x)
  else:
      print(compact ? "+" : " + "); showvalue(io, V, B, x)
```

* A negative real becomes ` - |x|`. `-0.0` prints as ` - 0.0`. `typemin(Int)` prints its widened magnitude: ` - 9223372036854775808v₂`.
* A Complex never takes the minus branch: ` + (-1-2im)v₂`.
* Rationals: ` - (1//2)v₂`.

### 5.3 Compact context

* `compact()` (MV:39-42) is a global toggle, default `true`. `compactio(io)` wraps `io` with `:compact => true` when the toggle is on (MV:44).
* `Chain`, `Multivector`, `Spinor` and `CoSpinor` wrap their io, so **coefficients print in compact form**: 6 significant digits, and complex numbers without spaces as `1+2im`.
* The **separators** (` + ` vs `+`) are decided by the caller's original `:compact` flag, captured before wrapping.
* `Single`, `Couple`, `PseudoCouple`, `Phasor` and `Submanifold` do **not** wrap.
* Oracle: `Chain(1/3,2/3,1e-20)` gives `0.333333v₁ + 0.666667v₂ + 1.0e-20v₃`, but `(1/3)v1` gives `0.3333333333333333v₁`. With `Grassmann.compact(false)`, `Chain(1/3,2/3)` gives `0.3333333333333333v₁ + 0.6666666666666666v₂`.

### 5.4 Per-type display rules (N, io assumed non-compact unless stated)

| type | algorithm | goldens (verified) |
|---|---|---|
| `Submanifold` (basis) | `printindices(io, V, bits)` (DS:326) | `v`, `v₁`, `v₁₂₃`, `v∞`, `v∅`, `v∞∅`, `v∞₁`, `v∅₁₂`, `w¹`, `∂₁v₁`, `v₀` (index 10), `va`, `vb` |
| `Submanifold` (space) | DS:325-356. `⟨`…`⟩`; each ambient index prints its metric char if present, else `_`. Metric char: `Signature` + diagonal gives `+`/`-`; Int gives `1`; conformal Signature gives `1` (sic); DiagonalForm gives the value with `,` separators. Prefix `T^μ` if `diffmode > 0`; `∞`/`∅` prefixes; tangent sub/superscripts; suffix `'` (dual) or `*` (dyadic); name subscript. | `⟨111⟩`, `⟨+++⟩`, `⟨-+++⟩`, `⟨∞∅111⟩` (for `S"∞∅+++"`), `⟨∞+++⟩`, `⟨∅+++⟩`, `⟨1,2,3⟩`, `⟨__+_+⟩`, `⟨1__1⟩`, `T¹⟨+++₁⟩` (Signature), `⟨---⟩'`, `⟨-++++---⟩*` |
| `Signature` / `DiagonalForm` | DS:175-189 / DS:226-243 (same scheme, no `_`) | `⟨+⟩` (ℝ), `⟨+++⟩`, `⟨1,1,1⟩` |
| `Zero` | `𝟎` (DS:604) | |
| `Infinity` | `∞` (DS:663) | |
| `One` | as a basis | `v` |
| `Single` | `showvalue(io, V, bits, value)` (DS:488) | `2v₁`, `-2v₁`, `2.5v`, `(1 + 2im)v₁`, `(1//2)v₁`, `π*v₁`, `NaN*v₁`, `Inf*v₁`, `-Inf*v₁`, `2v₁` (BigInt), `:x*v₁`, `(1v₁ + 2v₂ + 3v₃)v₁` (Chain value) |
| `Chain` | io := compactio; `showvalue` for term 1, `showterm` for terms 2..C(N,G); **zeros are printed** (MV:109-116) | `1v₁ + 1v₂ + 0v₃`, `4v₁ + 5v₂ + 6v₃`, `7v` (G=0), `7v₁₂₃`, `1.0v₁ - 0.0v₂ + 2.0v₃`, `(1//2)v₁ - (1//2)v₂ + (0//1)v₃`, `(1+2im)v₁ + (-1-2im)v₂ + (0+0im)v₃`, `true*v₁ + false*v₂ + true*v₃`, `-9223372036854775808v₁ + 3v₂ + 4v₃`, `v₁⊗v₁ + v₂⊗v₂ + v₃⊗v₃` (Chain of blades), `2v₁⊗v₁ + …` (Chain of Singles), `(1v₁+2v₂+3v₃)v₁ + (4v₁+5v₂+6v₃)v₂ + …` (Chain of Chains) |
| `Multivector` | io := compactio; `print(io, v[1])` (**plain `print`, no parens, no label**); then for each grade 1..N and each blade, `showterm` **only if `!isnull(coef)`** (`isnull = iszero`, AT:592). If every non-scalar is null: append `showstar(v[1])` and `"v⃖"` (MV:340-356) | `1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃`, `0v⃖`, `3v⃖`, `0.0v⃖`, `0 + 1v₁`, `0 - 1v₁ - 1v₁₂₃`, `-3 + 1v₁₂₃`, `1.5 - 2.5v₁₂₃`, `1+2im*v⃖`, `1//2*v⃖`, `true*v⃖`, `NaN*v⃖`, `Inf*v⃖`, `1.0 + NaN*v₁`, `1//2 - (1//2)v₁`, `1+0im + (-1+2im)v₁`, `a + :b*v₁₂₃` (Symbols) |
| `Spinor` | compactio; `print(v[1])`; then for even grades 2,4,…,N, **all** blades via `showterm` (zeros included) (MV:589-600) | `1 + 2v₁₂ + 3v₁₃ + 4v₂₃`, `0 + 0v₁₂ + 0v₁₃ + 0v₂₃`, `0.333333 - 0.666667v₁₂ + 0.0v₁₃ - 0.0v₂₃`, `1+1im + (0-2im)v₁₂ + …`, `1 + 2v₁₂` (N=2); N=1 throws (bug 14) |
| `CoSpinor` | compactio; odd grades 1,3,…; the first blade via `showvalue`, the rest via `showterm`, zeros included (MV:601-615) | `1v₁ + 2v₂ + 3v₃ + 4v₁₂₃`, `-1v₁ + 2v₂ - 3v₃ + 4v₁₂₃`, `-1.5v₁ + 0.0v₂ + 0.0v₃ + 0.0v₁₂₃` |
| `Couple` | `show(io, re)` (not compactio) then `showterm(io, V, B, im)` (MV:757-761) | `1 + 2v₁₂`, `1 - 2v₁₂`, `1.5 - 2.5v₁`, `0.3333333333333333 + 0.6666666666666666v₁`, `1 + 2im + (3 - 4im)v₁`, `1//2 - (3//4)v₁`, `1 + 0v` (B=One), `0 + 1v₁₂` |
| `PseudoCouple` | `showvalue(io, V, B, re)` then `showterm(io, V, UInt(V), im)` (MV:762-766) | `1v₁ + 2v₁₂₃`, `1v₁ - 2v₁₂₃`, `0v + 1v₁₂₃` (B=One) |
| `Phasor` | `show(io, amplitude)`; `print(io, compact ? "∠" : " ∠ ", angle)` (MV:931-934) | `1 ∠ 2`, `2.0 ∠ 0.5v₁₂`, `2 ∠ v₁₂`, `1.9900083305560516 + 0.1996668332936563v₁₂ ∠ 1.0v₁₂`; compact: `1∠2` |
| `Basis` | `DirectSum.Basis{$V,$(2^N)}(e1, e2, …)` (DSb:195-202) | `DirectSum.Basis{⟨111⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)`; `collect(Signature)` yields *space-style* blades `DirectSum.Basis{⟨-+++⟩,16}(⟨____⟩, ⟨-___⟩, ⟨_+__⟩, …)` |
| `SparseBasis` / `ExtendedBasis` | `…{V,2^N}(first, ..., last)` | `DirectSum.SparseBasis{⟨111111111111⟩,4096}(v, ..., v₁₂₃₄₅₆₇₈₉₀ab)`, `DirectSum.ExtendedBasis{⟨11…1⟩,4611686018427387904}(v, ..., v₁₂₃₄₅₆₇₈₉₀abc…xyzABC…XYZ)` |

### 5.5 Julia number formatting (a porting risk for display goldens)

Implement Julia's `show(Float64)` exactly, from `share/julia/base/ryu/shortest.jl` `writeshortest`:

* Digits:
  * Non-compact: the Ryu shortest round-trip digits `output` with exponent `nexp`.
  * Compact: `reduce_shortest(x, maxsignif=999_999)`, i.e. at most 6 significant digits, rounded.
* Let `olength = #digits` and `pt = nexp + olength`. Use **decimal form** iff `-4 < pt ≤ 6` and `!(pt ≥ olength && abs(mod(x+0.05, 10^(pt-olength)) - 0.05) > 0.05)`. Otherwise use `d.ddd e±X`, with at least one fractional digit (`1.0e20`) and no `+` in the exponent.
* Decimal form always carries `.0` for integers.
* Specials are `NaN`, `Inf`, `-Inf`, `-0.0`.

Oracle table (`jl_types/t12.jl`), in the order `show` | compact:

| value | `show` | compact |
|---|---|---|
| `1/3` | `0.3333333333333333` | `0.333333` |
| `1e-4` | `0.0001` | `0.0001` |
| `1e-5` | `1.0e-5` | `1.0e-5` |
| `999999.0` | `999999.0` | `999999.0` |
| `1e6` | `1.0e6` | `1.0e6` |
| `1234567.0` | `1.234567e6` | `1.23457e6` |
| `123456.789` | `123456.789` | `1.23457e5` (sic) |
| `0.1+0.2` | `0.30000000000000004` | `0.3` |
| `1.797…e308` | `1.7976931348623157e308` | `1.79769e308` |
| `5e-324` | `5.0e-324` | `5.0e-324` |

Other types:

* **Complex:** `show` gives `1 + 2im` (`1.5 - 2.5im`); compact gives `1+2im`.
* **Rational:** `1//3`, `-1//3`.
* **Irrational:** `π`. Converted into a Float64 Multivector it prints `3.14159v⃖` in compact mode.
* **Bool:** `true`. **Symbol:** `show` gives `:x`, `print` gives `x`.

---

## 6. Examples and goldens (verbatim; all re-verified against the oracle unless noted)

### 6.1 From README.md / docs (`design.md`, `algebra.md`)

```
julia> using Grassmann; @basis S"-++"          # README.md:135-136
(⟨-++⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
julia> DirectSum.Basis(V)                       # README.md:147-148
DirectSum.Basis{⟨-++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
julia> V = Submanifold(4)                       # algebra.md:283-284
⟨1111⟩
julia> G4 = collect(V)                          # algebra.md:293-294
DirectSum.Basis{⟨1111⟩,16}(v, v₁, v₂, v₃, v₄, v₁₂, v₁₃, v₁₄, v₂₃, v₂₄, v₃₄, v₁₂₃, v₁₂₄, v₁₃₄, v₂₃₄, v₁₂₃₄)
julia> G4.v12 + 2G4.v14                         # algebra.md:301-305
1v₁₂ + 0v₁₃ + 2v₁₄ + 0v₂₃ + 0v₂₄ + 0v₃₄         ::Chain{⟨1111⟩, 2, Int64, 6}
julia> G42 = collect(V(1,4)); sqrt(2) + G42.v14  # algebra.md:309-316
DirectSum.Basis{⟨1__1⟩,4}(v, v₁, v₄, v₁₄)
1.4142135623730951 + 1.0v₁₄                      ::Couple{⟨1__1⟩, v₁₄, Float64}
julia> @basis 3                                 # algebra.md:320-321
(⟨111⟩, v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
julia> 1 + v12 - v13                            # algebra.md:325-329
1 + 1v₁₂ - 1v₁₃ + 0v₂₃                           ::Quaternion{⟨111⟩, Int64} (= Spinor{⟨111⟩,Int64,4})
julia> Chain{V,1}(Values(4,5,6))                # algebra.md:335-336
4v₁ + 5v₂ + 6v₃
julia> value(Chain(4,5,6))                      # algebra.md:340-344
[4, 5, 6]  ::Values{3, Int64}
julia> wedge(Chain(1,2,3),Chain(4,5,6))         # algebra.md:348-349
-3v₁₂ - 6v₁₃ - 3v₂₃
julia> Spinor{V}(1,2,3,4)                       # algebra.md:353-354
1 + 2v₁₂ + 3v₁₃ + 4v₂₃
julia> complexify(1+im); complexify(Chain(1,2)) # algebra.md:436-440
1 + 1im
1 + 2v₁₂
julia> vectorize(1+2im); vectorize(Couple(1,2)) # algebra.md:444-448
1v₁ + 2v₂
1v₁ + 2v₂
julia> complementright(Multivector(1,2,3,4,5,6,7,8))   # algebra.md:475-479 (same for complementleft, complementrighthodge)
8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
julia> @basis S"++-"; hodge(Multivector{V}(1,2,3,4,5,6,7,8))   # algebra.md:498-502
-8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃
julia> vee(Chain{V}(1,2,3),hodge(Chain{V}(4,5,6)))  # algebra.md:510-511 (V = S"++-")
-4v
julia> Chain(1,2,3)*Chain(4,5,6)                # algebra.md:535-536
32 - 3v₁₂ - 6v₁₃ - 3v₂₃
julia> basis"3"; wedge(!v12,!v23); !vee(v12,v23); wedge(v12,!v12)   # algebra.md:934-948
-1v₁₃
-1v₁₃
1v₁₂₃
julia> Λ(62).v32a87Ng                           # runtests.jl:10 (golden: == -1Λ(62).v2378agN)
-1v₂₃₇₈agN
julia> Λ(ℝ^3); Λ(tangent(ℝ^2)); Λ(tangent((ℝ^0)',3,3))   # algebra.md:151-155 (@repl, re-run)
DirectSum.Basis{⟨+++⟩,8}(v, v₁, v₂, v₃, v₁₂, v₁₃, v₂₃, v₁₂₃)
DirectSum.Basis{T¹⟨++₁⟩,8}(v, v₁, v₂, ∂₁, v₁₂, ∂₁v₁, ∂₁v₂, ∂₁v₁₂)
DirectSum.Basis{T³⟨¹²³⟩',8}(w, ϵ₁, ϵ₂, ϵ₃, ϵ₁₂, ϵ₁₃, ϵ₂₃, ϵ₁₂₃)
julia> i,j,k = hyperplanes(ℝ^3); i^2, j^2, k^2, i*j*k; -(j+k)*(j+k); -(j+k)*i   # algebra.md:1031-1034
(-1v, -1v, -1v, 1v)
2 + 0v₁₂ + 0v₁₃ + 0v₂₃
0 - 1v₁₂ - 1v₁₃ + 0v₂₃
julia> basis"--"; v1^2, v2^2, v12^2, v1*v2*v12  # algebra.md:1038-1039
(-1v, -1v, -1v, -1v)
julia> @basis S"∞∅++"                           # algebra.md:1354-1358, issuestests.jl:9-16
(v∞^2, v∅^2, v1^2, v2^2) = (𝟎, 𝟎, 1v, 1v)
(v∞⋅v∅, v∞∅^2) = (-1v, 1v)
(v∞∅*v∞, v∞∅*v∅) = (-1v∞, 1v∅)
v∞*v∅ = -1 + 1v∞∅ + 0v∞₁ + 0v∞₂ + 0v∅₁ + 0v∅₂ + 0v₁₂ + 0v∞∅₁₂   ::Spinor{⟨∞∅11⟩,Int64,8}
v∅*v∞ = -1 - 1v∞∅ + 0v∞₁ + 0v∞₂ + 0v∅₁ + 0v∅₂ + 0v₁₂ + 0v∞∅₁₂
(⋆v∞, !v∞, ⋆v∅, !v∅) = (1v∞₁₂, 2v∅₁₂, -1v∅₁₂, -0.5v∞₁₂)
julia> Λ(22); Λ(7)⊕Λ(7)'; Λ(62)                 # design.md:115-138
DirectSum.SparseBasis{⟨1111111111111111111111⟩,4194304}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijkl)
DirectSum.SparseBasis{⟨+++++++-------⟩*,16384}(v, ..., v₁₂₃₄₅₆₇w¹²³⁴⁵⁶⁷)
DirectSum.ExtendedBasis{⟨11…(62 ones)…1⟩,4611686018427387904}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ)
julia> V = ℝ'⊕ℝ^3; V'; V⊕V'                     # design.md:90-92
⟨-+++⟩
⟨+---⟩'
⟨-++++---⟩*
julia> (ℝ^5)(3,5)                                # design.md:83-84
⟨__+_+⟩    ::Submanifold{⟨+++++⟩, 2, 0x0000000000000014}
julia> ℝ⊕ℝ' ⊇ Manifold(1); ℝ ∩ ℝ' == Manifold(0); ℝ ∪ ℝ' == ℝ⊕ℝ'   # design.md:103-105
true; true; true
julia> [(χ(Δ(ω)),χ(Δ(∂(ω)))) for ω ∈ (Λ(ℝ5).v12, …)]   # algebra.md:1342 — FAILS on master (Δ not callable)
```

Doc claims that are stale or misleading:

* The design-section example `Λ(V+V')` for `V=ℝ^22` now prints `ExtendedBasis{⟨++…--…⟩*,17592186044416}(v, ..., v₁₂₃₄₅₆₇₈₉₀abcdefghijklw¹²³⁴⁵⁶⁷⁸⁹⁰ABCDEFGHIJKL)`.
* The Reduce/GaloisFields outputs at algebra.md:1393-1485 cannot be checked (the extensions are not installed).
* `typeof(G4.v12 + G4.v14)` is `Chain{⟨1111⟩, 2, Int64, 6}` ✓.

### 6.2 From the test suite

* runtests.jl:4: `@basis "++++" s e; e124 * e23 == e134`; `Λ(S"++++").v124*Λ(S"++++").v23 = 1v₁₃₄`.
* runtests.jl:5: `[Λ(3).v32^2,Λ(3).v13^2,Λ(3).v21^2] == [-1Λ(3).v for j∈1:3]`, i.e. `[-1v, -1v, -1v]`.
* runtests.jl:7-9: `v1*v1, v1⋅v1, v1∧v1 == (1,1,0)`; with `-+++` the result is `(-1,-1,0)`; `h = 1v1+2v2; h⋅h == 3v`.
* runtests.jl:12: `Λ(Manifold(14)) + Λ(Manifold(14))' == Λ(Manifold(14)+Manifold(14)')`.
* issuestests.jl:17-31 (#17): `a = v + v1 - v1` is a `Couple` equal to `v` and to `1`; `a-1 == 0`.
* issuestests.jl:33-45 (#16): `(2v1+v2)+(v1+v2) == 3v1+2v2`; `v1 + A == 3v1 + 1v2`.
* issuestests.jl:47-50 (#14), in `+++`: `(v1+v2) + (v1+v2)*(v1+v2) == 2 + 1v1 + 1v2`.
* issuestests.jl:52-61 (#15): `exp(alpha/2*(i)) ≈ sqrt(2)*(1+i)/2` with `alpha = π/2` and `i,j,k = hyperplanes(ℝ^3)`.
* issuestests.jl:63-72 (#20), in `S"∞∅+"`: `v∅*v∞ == -1 - v∞∅`; `v∅*(-v∞) == 1 + v∞∅`; `Single{V}(-1, a) == -a`.
* issuestests.jl:74-82 (#22): `v1+v2` is a Chain; `Multivector(a) == v1+v2`; `Chain(v) == v`.
* generictests.jl:13-69: the isapprox/scalar matrix:
  * `v ≈ v`, `2v ≈ 2v`, `v1+v2 ≈ v1+v2` are all true.
  * `!(v ≈ v1)` and `!(v1+v2 ≈ v1)` hold.
  * `scalar(-v+v1) == -1v` and `scalar(v1+v2) == 0v`.
* generictests.jl:71-161: algebra laws over the spaces `3, V"+++", S"∞+", S"∅+", V"-+++", S"∞∅+"`:
  * unity, associativity and distributivity
  * `a⋅b == 0.5(ab+ba)`, `a∧b == 0.5(ab−ba)`, `ab == a⋅b + a∧b`, `ab == 2a⋅b − ba`, `aa == a⋅a`

  These make excellent **property tests** for the Lean port.

### 6.3 Additional type-layer goldens (oracle)

The following are verbatim lines from `jl_types/t1.out`, `t3.out`, `t4.out`, `t6.out`, `t8.out` and `t13.out`:

```
Couple(1,2)                  => 1 + 2v₁₂                      ::Couple{⟨11⟩, v₁₂, Int64}
Phasor(1,2)                  => 1 ∠ 2                         ::Phasor{⟨11⟩, Int64, Int64}
Single(2)                    => 2v                            ::Single{⟨⟩, 0, v, Int64}
Multivector N=0              => 5v⃖    Chain N=0 => 5v
Multivector(1,2,3,4)         => 1 + 2v₁ + 3v₂ + 4v₁₂          ::Multivector{⟨11⟩, Int64, 4}
Spinor(1,2,3,4,5,6,7,8)      => 1 + 2v₁₂ + 3v₁₃ + 4v₁₄ + 5v₂₃ + 6v₂₄ + 7v₃₄ + 8v₁₂₃₄
CoSpinor N=4 (1..8)          => 1v₁ + 2v₂ + 3v₃ + 4v₄ + 5v₁₂₃ + 6v₁₂₄ + 7v₁₃₄ + 8v₂₃₄
quaternion(1,2,3,4)          => 1 + 2v₁₂ - 3v₁₃ + 4v₂₃        quatvalue => [1, 2, 3, 4]
quaternion(1.0)              => 1.0 + 0.0v₁₂ - 0.0v₁₃ + 0.0v₂₃
vectorize(Couple{V,v12}(1,2))=> 1v₁ + 2v₂                     ::Chain{⟨11_⟩,1,Int64,2}
vectorize(PseudoCouple{V,v1}(3,4)) => 4v₂ + 3v₃               ::Chain{⟨_11⟩,1,Int64,2}
polarize(One(V))             => 1 ∠ 0          polarize(v12) => 1 ∠ v₁₂      polarize(2v13) => 1 ∠ 2v₁₃
complexify(Phasor(2.0,0.5v12)) => 1.7551651237807455 + 0.958851077208406v₁₂
angle(Couple{V,v12}(1,2))    => 1.1071487177940904v₁₂      radius => 2.23606797749979
V(I), V(2I), v1 + I          => v₁₂₃, 2v₁₂₃, 1v₁ + 1v₁₂₃ (PseudoCouple)
v + v1 - v1                  => 1 + 0v₁  (Couple)      v1 - v1 => 0v₁ (Single, not Zero)
v1 + 3 => 3 + 1v₁ ;  3 - v12 => 3 - 1v₁₂ ;  0 - v1 => -1v₁ ;  v1 + 0 => v₁
Λ(D"2,3").v1^2, v12^2        => (2v, -6v)
```

---

## 7. Dependencies on other chakravala packages (symbols used by `GJ`/`MV`)

* **AbstractTensors** (AT; imported at GJ:24, GJ:39-41, MV:21-22, MV:962-964):
  * Types: `TensorAlgebra`, `Manifold`, `TensorGraded`, `TensorTerm`, `TensorMixed`, `Scalar`, `GradedVector`, `Bivector`, `Trivector`.
  * Functions: `Values`, `Variables`, `FixedVector`, `clifford`, `hodge`, `wedge`, `vee`, `valuetype`, `scalar`, `isscalar`, `vector`, `isvector`, `bivector`, `isbivector`, `trivector`, `istrivector`, `volume`, `isvolume`, `⊗`, `complement`, `wedgedot_metric`, `contraction_metric`, `log_metric`, `pseudoscalar`, `equal`, `antiabs`, `antiabs2`, `geomabs`, `unit`, `unitize`, `unitnorm`, `value`, `involute`, `even`, `odd`, `⋆`.
  * Generic operator plumbing: `plus`/`minus`/`times`/`equal` via `interop` (AT:243-298); `isnull`; `norm`/`iszero`/`isone` (AT:444-446); scalar `∏ ∑ - /` (StaticVectors).
* **StaticVectors** (via AT): `Values`, `Variables`, `FixedVector`, `TupleVector`, `evens`, `countvalues`, `evenvalues`.
* **Leibniz** (GJ:34-36, GJ:45-49, GJ:73-74; MV:23, MV:31):
  * Space queries: `hasinf`, `hasorigin`, `dyadmode`, `value`, `pre`, `vsn`, `metric`, `mdims`, `gdims`, `bit2int`, `indexbits`, `indices`, `diffvars`, `diffmask`, `hasconformal`, `symmetricmask`, `indexstring`, `indexsymbol`, `combo`, `digits_fast`.
  * Cache limits and index functions: `algebra_limit`, `sparse_limit`, `cache_limit`, `fill_limit`, `gdimsall`, `spincumsum`, `binomial`, `binomial_set`, `binomsum`, `binomsum_set`, `lowerbits`, `expandbits`, `bladeindex`, `basisindex`, `indexbasis`, `indexbasis_set`, `loworder`, `intlog`, `antisum`, `antisum_set`, `anticumsum`, `antiindex`, `spinindex`, `binomcumsum`, `promote_type`, `mvec`, `svec`, `insert_expr`, `supermanifold`.
  * Grades and printing: `grade`, `antigrade`, `showvalue`, `basis`, `order`, `Fields`, `parval`, `mixed`, `mvecs`, `svecs`, `spinsum`, `spinsum_set`, `showstar`, `count_gdims`, `χ`, `check_field`.
  * Derivations: `Derivation`, `∇`, `Δ`, `d`, `∂`, `δ`.
* **DirectSum** (GJ:23, GJ:33, GJ:37; used throughout):
  * Types: `Submanifold`, `Single`, `Zero`, `One`, `Infinity` (not re-exported), `Signature`, `DiagonalForm`, `TensorBundle`, `Basis`/`Λ`, `SparseBasis`, `ExtendedBasis`, `SubAlgebra`.
  * Space constants and helpers: `V0`, `⊕`, `generate`, `basis`, `getalgebra`, `getbasis`, `dual`, `metrichash`, `antimetric`, `cometric`, `signbool`, `submanifold`, `supermanifold`, `isbasis`, `@basis` & co., `@S_str`/`@V_str`/`@D_str`, `ℝ`, `ℝ0-9`, `tangent`, `labels`, `lookup_basis`, `indexparity`, `printindices`, `shift_indices`, `interform`.
* **ComputedFieldTypes**: `@computed` (the lengths `X` in Chain, Multivector and Spinor). **SparseArrays** (legacy unsplitter, commented out). **AbstractFFTs** (glue). **Requires** (extensions). **LinearAlgebra** (`I`, `UniformScaling`, `det`, `tr`, `norm`, `dot`, `cross`, `rank`).

---

## 8. Lean 4 porting notes

### 8.1 What should be a type index (zero runtime cost) vs a runtime value

| Julia param | Lean recommendation | rationale |
|---|---|---|
| `V` (space) | **index**: `(V : Space)`, a structure `{ bundle : Bundle, mask : UInt64 }` (or `BitVec 64`). `Bundle` holds `n : Nat`, `opts` (hasinf, hasorigin, dyadmode, polymode), metric (signature `BitVec n` or diagonal `Array ℚ/Float`), `vars`, `diff`, `name` | shapes depend on it. Keep `Space` with `DecidableEq` so that `V₁ = V₂` checks reduce for literal spaces. |
| `N = mdims V` | derived `V.n`, used in types | |
| `G` (grade) | **index** `(G : Nat)` with `h : G ≤ V.n` as an auto-param `by omega`/`decide` | `Chain V G α := { v : Vector α (Nat.choose V.n G) }` |
| `X` (length) | not a parameter; computed in the `Vector` size | `@computed` becomes type-level computation |
| `B` (blade) of `Single`/`Couple`/`PseudoCouple`/`Submanifold` | **two layers**. Static: `(B : Blade V)` as an index where `Blade V := {bits : UInt64 // bits < 2^V.n}` (`grade := popcount`). Dynamic: store `bits` at runtime (8 bytes). | Julia's type-level B gives zero-cost `Single`. In Lean an index B is equally zero-cost, but the `+` lattice would need type-level `if` on `B₁ = B₂`, which only reduces for literals. |
| `T` (coefficient field) | a type parameter `α` with a typeclass `[GAField α]` (`Zero`, `One`, `Add`, `Neg`, `Mul`, `DecidableEq` or approximate equality, `Repr`/`JuliaShow`) | |
| Phasor `B`, `T` | type parameters (angle type, amplitude type) | |

**Recommended architecture: two layers.**

1. **Static layer.** `Chain V G α`, `Multivector V α`, `Spinor V α`, `CoSpinor V α`, `Couple V B α`, `PseudoCouple V B α`, `Single V B α` (value only), `Blade V G`, `Zero V`, `One V`.
   * Operations with statically known result types: `wedge : Chain V p α → Chain V q α → Chain V (p+q) α`, grade projections `Multivector.grade g : Chain V g α`, `toMultivector`, `toSpinor (h : Even G)`.
   * Invariants live in the types (`Nat.choose` sizes). The proofs are free for literal `V` (`by decide`) and `omega` for generic V.
2. **Dynamic layer**: `inductive TA (V : Space) (α)` with constructors
   `zero | inf | one | blade (b) | single (b) (x : α) | chain (g) (Vector α (choose n g)) | couple (b) (re im) | pseudo (b) (re im) | spinor (…) | cospinor (…) | multi (…) | phasor …`.
   * `HAdd`/`HSub` implement §4.5 exactly: a `match` on constructor pairs plus the `adder` decision list.
   * This layer is what the Julia oracle compares against (type tag, values, `show` string).
   * The key theorem that makes this layer trustworthy:
     `theorem toDense_add (a b : TA V α) : toDense (a + b) = toDense a + toDense b`.
     Here `toDense` embeds everything into `Multivector`. With this theorem every lattice case is correct by one proof, and the representation choice is purely a "which constructor" decision (§8.4).

### 8.2 How Julia gets its speed, and the Lean equivalents

* **`@generated` unrolling per `(N,G)`.** Julia specializes the code on the type parameters `V,G` and emits literal tuple constructors with precomputed indices (MV:131-140, MV:241-259, MV:300-314; AL:747-1040). Lean does **not** monomorphize on `Nat` values. Use these instead:
  * **Bit tricks, no tables:**
    * blade product sign = parity of `Σ_k popcount((a >> k) & b)` (or the classic `reorderingSign`)
    * metric factor = `Π_{i ∈ a&b} g_i`, which for Signature is `(-1)^popcount(a & b & S)`
    * result blade = `a ^^^ b`
  * **Precomputed tables for N ≤ 12** (`cache_limit`): `bladeIndex[n][bits]`, `indexBasis[n][g]`, `basisIndex`, `spinIndex`, `antiIndex`. Julia caches exactly these (LZu:181-250). In Lean, build them with `initialize` (an `IO.Ref`-free `builtin_initialize` constant, or a top-level `def` evaluated once as a closed term, marked `@[noinline]` so it is shared). Sizes: `2^12 × 12` entries.
  * **Dense geometric product** over a `Multivector`: iterate the nonzero coefficients of `a` and `b` (`2^n × 2^n`) with the bit tricks, accumulating into `basisIndex (a^^^b)`. That is O(4^n) with a tiny constant, the same complexity as Julia's generated code. For Chains, iterate the `C(n,p) × C(n,q)` pairs.
  * `@[specialize]` on the coefficient typeclass and `@[inline]` on the index helpers.
* **Unboxed storage.** Julia `Values{N,Float64}` is an unboxed tuple. Lean `Array Float` **boxes** each Float, which is a big perf trap. Options:
  * (a) A dedicated `FloatArray`-backed representation (`structure MultivectorF (V) where v : FloatArray; h : v.size = 2^V.n`) for the Float64 hot path, with the generic `Vector α n` path for exact types (`Int`, `ℚ`, `Complex`).
  * (b) A `class Storage α` giving `α ↦ FloatArray | Array α`.

  Benchmark against the Julia oracle (`@btime`) for N=3,5,8.
* **Grade extraction.** Julia compiles runtime `m[g]` into an `if` chain. In Lean, `m.grade g` is a slice `[binomSum n g, binomSum n (g+1))`, which is O(1) with the prefix-sum table.
* **Caches beyond 12**: compute lazily (`bladeIndex` via the lex-rank formula in §3.4). The ExtendedBasis (N ≤ 62) should never allocate `2^N`.

### 8.3 Tricky semantics to preserve (if matching the oracle)

1. **Lex (not numeric) blade order within a grade.** Store and iterate via `indexBasis n g`.
2. **1-based vs 0-based.**
   * `Chain[i]` is 1-based. `Multivector[g]` means *grade* `g ∈ 0..N`, but `Multivector[range]` is 1-based raw components.
   * Recommendation: expose explicit names (`m.component i`, `m.gradeBlock g`, `m.gradeChain g`) instead of overloading `GetElem`. If you implement `GetElem`, pick one meaning per type and document it.
3. **Values with 0 coefficient remain Singles** (`v1 - v1 = 0v₁`, not `Zero`). Only explicit construction, grade mismatch or products produce `Zero`.
4. **Couple formation depends on space options.** It is disabled in conformal (`∞∅`) and tangent spaces. The pseudoscalar is `grade(V)`, not `N`, when `diffvars ≠ 0`.
5. **`Couple(scalar Single)` uses `B = pseudoscalar`.** `PseudoCouple(pseudoscalar)` uses `B = One`. `Couple{V,B}(term)` ignores whether the term's basis equals `B`.
6. **Equality asymmetries.** Couples with different `B` compare equal only when both imaginary parts are 0. Number vs graded element is equal only when the number is 0, except at grade 0.
7. **`isscalar`/`iszero` are norm-and-≈ based.** Keep Float `≈` semantics: `isapprox(x,y; rtol=√eps, atol=0)`, i.e. `|x−y| ≤ rtol·max(|x|,|y|)`.
8. **Display** (§5): which types wrap compactio, zero-skipping only in `Multivector`, the `v⃖` suffix, `print` vs `show` for the scalar part, parentheses for Complex/Rational, the `*`/`⊗` stars, and Julia's float formatting (§5.5). **The float formatter is the single biggest display risk**: implement Ryu-shortest with the exact `exp_form` rule (a fuzz test against the oracle over 10⁵ random doubles is cheap).
9. **`hyperplanes` ignores the Bool `λ`** (always `+I`), and its `𝕚𝕛𝕜` order is the reverse of `quaternion`'s.
10. **`polarize(Chain2)` reads (amplitude, angle)**, while `polarize(Complex)` reads (x, y).
11. **Phasor with a Real angle exponentiates the reals**: `complexify(Phasor(1.0,2.0)) = e²`.
12. **Label parsing** accepts any order and repeats with a permutation sign. **Do not** replicate the metric-sign quirk (LZi:236). ASCII label `10` vs `a` ambiguity: use pretty names (`v₀`) or an explicit `Blade.ofIndices`.

### 8.4 Where proofs pay off (development velocity, not ceremony)

* `lexRank`/`lexUnrank` bijection on `Fin (choose n k)`; `basisIndex` is a bijection `Fin (2^n) ≃ bitmasks`; the Spinor and CoSpinor index maps partition it. Use `decide` for n ≤ 6 and a structural proof in general.
* `popcount (a ^^^ b) = popcount a + popcount b − 2·popcount (a &&& b)`: grade bookkeeping for products (`bv_decide` for 64-bit instances).
* Reordering sign is a homomorphism, i.e. associativity of the blade product. This is the core lemma behind `A*(B*C) = (A*B)*C` (generictests.jl:111-118). State it and prove it (`bv_decide`/`grind` on bitvectors for fixed widths).
* `toDense_add`, `toDense_neg`, `toDense_smul` (§8.1): **one proof covers the entire §4.5 table**. Also `toDense_injective` for each container, and `gradeChain (toMultivector c) g = if g = G then c else 0`.
* `lookupBasis` parity = `Equiv.Perm.sign` of the sorting permutation (tests `v21 = -v12`, `v1231 = -v23`).
* Decidable instances for the lattice: `resultKind : Kind → Kind → SpaceFlags → Kind` as a total function, with a `theorem resultKind_comm_on_types` where commutative (the lattice *is* symmetric in kind, see §4.5; only argument order inside Couple/PseudoCouple differs).

### 8.5 Julia-specific parts to skip or redesign

* **Skip:**
  * `@computed`, `@pure`, `@generated`; the whole `generate_products` / `generate_algebra` / `generate_symbolic_methods` code generation (GJ:360-414). Replace with typeclass instances; symbolic scalars come from a `Coeff` instance over a Lean expression type if needed.
  * Requires/`__init__` extensions; the FFT glue; `ChainBundle` / `isbundle`; the stale exports; `compact()` global mutable state (make it an explicit `ShowConfig` parameter).
  * Multi-flavored `Basis`/`SparseBasis`/`ExtendedBasis`: collapse into one lazy `Λ V` view with `getbasis`.
* **Redesign:**
  * `@basis` becomes a Lean command elaborator `basis! S"-++"` that declares `V, v, v1, …, v123` (and pretty names via `«v₁₂»`) as `abbrev`s.
  * `V"..."`/`S"..."`/`D"..."` become `macro`/`elab` string literals, or a `Space.ofString` plus `decide`.
  * Julia `==` across types becomes `BEq` on the dynamic layer, with the semantics of §4.6 (fixed where noted).
* **Keep but isolate:** tangent / dyadic / conformal spaces. Implement them in the same index scheme with `Space` flags, but test them separately; they are rarely hot.

### 8.6 Suggested Lean module decomposition (≈ LOC)

| module | contents | LOC |
|---|---|---|
| `Grassmann/Index/Binomial.lean` | `choose` tables, prefix sums `binomSum/spinSum/antiSum`, lemmas | 150 |
| `Grassmann/Index/Lex.lean` | `indexBasis`, `lexRank/unrank`, `bladeIndex/basisIndex/spinIndex/antiIndex`, cached tables for n ≤ 12, bijection proofs | 350 |
| `Grassmann/Index/Bits.lean` | popcount/parity/reorder-sign/metric-factor bit ops + `bv_decide` lemmas | 200 |
| `Grassmann/Space/Bundle.lean` | `Bundle` (Signature/DiagonalForm/Int encodings, options hash decode, dual `'`, `⊕`, `∪ ∩ ⊆`, `tangent`) | 350 |
| `Grassmann/Space/Submanifold.lean` | `Space` (mask), `Blade V`, `isbasis`, `V(i…)`, `shift`, `supermanifold` | 250 |
| `Grassmann/Space/Labels.lean` | `subs/sups/alphanum`, `printIndex`, `printLabel`, `labels`, name parser with parity (`lookupBasis`) | 300 |
| `Grassmann/Space/Syntax.lean` | `S"…"`/`V"…"`/`D"…"` literals, `basis!` command, `Λ` view | 250 |
| `Grassmann/Types/Static.lean` | `Single, Chain, Multivector, Spinor, CoSpinor, Couple, PseudoCouple, Phasor, Zero, One, Infinity` structures | 300 |
| `Grassmann/Types/Construct.lean` | constructors, one-hot builders, conversions (§4.1-4.2), `multispin`, zero/one | 400 |
| `Grassmann/Types/Access.lean` | component/grade access, projections (§4.3-4.4), property-name access | 300 |
| `Grassmann/Types/Dynamic.lean` | `TA` sum type, `resultKind`, `+`/`−`/unary `−`/scalar `*`, `toDense` + homomorphism theorems | 550 |
| `Grassmann/Types/Equality.lean` | `BEq`, `approxEq`, `isZero/isScalar…` | 200 |
| `Grassmann/Types/ComplexLike.lean` | Couple/PseudoCouple/Phasor math, `complexify/polarize/vectorize`, quaternions, `abs2/radius/angle` | 300 |
| `Grassmann/Show/JuliaFloat.lean` | Ryu shortest + compact rule, Complex/Rational/Int formatting | 400 |
| `Grassmann/Show/Tensor.lean` | `showValue/showTerm/showStar`, per-type display, `ShowConfig` | 300 |
| `Grassmann/Top.lean` | `hyperplanes`, `Space.nabla`, `∂/d/δ`, `project/reject`, `chain/path`, `column(s)`, `betti` scaffolding | 350 |
| `Grassmann/Oracle/Golden.lean` + `oracle/dump.jl` | JSON reader and comparators | 350 |
| **total (this report's scope)** | | **≈ 5,300** |

---

## 9. Oracle test plan (Julia dumps JSON; the Lean test harness compares)

**General conventions.**

* Coefficient encoding in JSON:
  * `Int64` as a number
  * `Float64` as the **string** `repr(x)` (shortest round-trip, plus `"NaN"`, `"Inf"`, `"-Inf"`, `"-0.0"`)
  * `Rational` as `[num, den]`
  * `Complex` as `[re, im]` (recursively encoded)
* Element encoding:
  ```json
  {"space":"⟨111⟩", "kind":"Chain|Multivector|Spinor|CoSpinor|Couple|PseudoCouple|Single|Submanifold|Zero|One|Infinity|Phasor",
   "grade":G, "bits":B, "T":"Int64", "values":[...],
   "show":sprint(show,x), "show_compact":sprint(show,x;context=:compact=>true),
   "show_nocompactio": (Grassmann.compact(false); …)}
  ```
* Spaces:
  * `Submanifold(n)` for `n = 0..6`, plus `8`, `11` (label `v₀`/`va` boundary), `12` and `13` (`cache_limit` boundary)
  * `S"-++"`, `S"+-"`, `S"--"`, `S"-+++"`, `S"∞+++"`, `S"∅+++"`, `S"∞∅++"`, `S"∞∅+++"`, `D"1,2,3"`, `D"2,3"`
  * `tangent(ℝ^2)` and `(ℝ^2)⊕(ℝ^2)'` (display and indexing only)
* Value distributions:
  * Ints uniform in `[-3,3]`, zero-heavy (30%) to exercise zero-skipping and the `v⃖` path.
  * Float64 drawn from `{0.0, -0.0, 1.0, -2.5, 1/3, 2/3, 1e-5, 1e-4, 123456.789, 1e6, 1e20, π, NaN, Inf}` ∪ `randn()`.
  * `Rational{Int}` from small num/den; `Complex{Int}` with components in `[-2,2]`.
  * Never use Symbol coefficients for goldens (the display is Julia-specific).
* **Skip known-crashing calls**: bugs 3, 4, 16 in §4.12, `collapse`, `𝒫`, `subcomplex`, `Phasor{V}(::Complex)` and `one(::CoSpinor)`. Julia can crash or hang on these, and a crash kills the whole dump run. For the other buggy entries, either record `{"error": "<ExceptionType>"}` goldens or leave them out.

**Dumps (one JSON file each).**

1. `index_tables.json`: for `n ≤ 12` and each `g`, `indexbasis(n,g)`. `bladeindex/basisindex/spinindex/antiindex(n,bits)` for all bits when `n ≤ 10`, and 2000 random bits for `n ∈ 11..20`. `binomsum/spinsum/antisum(n,i)`.
2. `labels.json`: for each space, `labels(V)`, `[string(b) for b in Λ(V).b]` (pretty), and `show(V)`. For the lazy containers: `show(Λ(n))` for `n ∈ {9,12,22,23,40,62}`.
3. `lookup.json`: for random index sequences (length ≤ 5, with repeats and any order) in the `+++`, `-++` and `∞∅++` spaces, `getproperty(Λ(V), sym)` gives kind, bits, value. Exclude positive-repeat pairs if the port fixes quirk 20, or mark them.
4. `construct.json`: every constructor call in §4.1 over the value distributions: `Chain{V,G}(vals)`, `Chain(v)`, `Multivector{V}(vals)`, `Spinor{V}`, `CoSpinor{V}`, `Couple{V,B}`, `PseudoCouple{V,B}`, `Single{V}`, `Couple(term)`, `PseudoCouple(term)`, `quaternion(...)`, `Multivector(tuple)`/`Spinor(tuple)` inference. Record the result element encoding.
5. `convert.json`: `Multivector(x)`, `Spinor(x)` (even inputs), `CoSpinor(x)` (odd inputs), `multispin(x)`, `Complex(x)`, `complexify(x)`, `vectorize(x)`, `polarize(x)`, `quatvalue(x)` for x over all kinds.
6. `access.json`: for random elements, `x[i]` (Chain), `x[g]`/`x(g)`/`x(g,i)` (Multivector, Spinor, CoSpinor), `scalar/vector/bivector/volume/imaginary(x)` (skipping `trivector(Couple)`), `z(G)` for Couple/PseudoCouple, and `firstindex/lastindex/length`.
7. `lattice.json` **(most important)**: for each non-special space and each ordered pair of kinds from the sample set in `jl_types/t5.jl` (terms of every grade, Chains of grade 1/2/N, Couple with even/odd `B`, PseudoCouple, Spinor, CoSpinor, Multivector), dump `a+b` and `a-b` with random coefficients. Skip `term+PseudoCouple` with a non-matching basis (bug 6). Also dump `PseudoCouple ± PseudoCouple` only if replicating bug 5.
8. `equality.json`: `a == b` and `a ≈ b` for random pairs of the same and different kinds, including zero-coefficient variants. Excludes bugs 3 and 4.
9. `display.json`: `show`/compact/`compact(false)` strings for all elements of files 4–8, plus the Float/Complex/Rational formatting table (§5.5) over 10⁴ random doubles (`repr`, compact `sprint`).
10. `zero_one.json`: `zero(x)`/`one(x)` per kind (skipping CoSpinor `one`); the Zero/One/Infinity arithmetic table (§4.9).
11. `top.json`: `hyperplanes(ℝn)` for n = 1..6; `(ℝ^n)(∇)`, `tangent(ℝ^n)(∇)`; `∂(Λ(ℝn).v1…k)`; `chain`/`path` of `v1…k`; `project`/`reject` round trips in `S"∞+++"` and `S"∞∅+++"` for 100 random vectors (Float64). Compare with `≈ 1e-12`.
12. **Property suites (no goldens needed)**, run in Lean on random elements: generictests.jl:71-161 (unity, associativity, distributivity, `a⋅b = ½(ab+ba)`, …), `toDense` homomorphism, index bijections, `Λ(V).v_{σ(I)} = sign(σ)·v_I`.
