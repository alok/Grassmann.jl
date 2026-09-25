# MeshTopology.jl — Lean 4 porting spec

**Source:** `/Users/alokbeniwal/chakravala/MeshTopology.jl` at commit `1291ce5`, "split-off MeshTopology from Cartan" (2026-07-27). Its `src/` is byte-identical to the registered v0.1.0 installed at `~/.julia/packages/MeshTopology/14YRf` (checked with `diff -r`).

**Files** (2879 LOC in total):

| File | Lines |
|---|---|
| `src/MeshTopology.jl` | 716 |
| `src/lagrange.jl` | 448 |
| `src/quotient.jl` | 753 |
| `src/grid.jl` | 309 |
| `src/element.jl` | 553 |
| `README.md` | 70 |
| `docs/src/{index,library}.md` | – |
| `test/runtests.jl` | 4 (the only test is `@test 1 == 1.0`) |

**Citation prefixes:**
- `MT:` = `src/MeshTopology.jl`
- `LG:` = `src/lagrange.jl`
- `QT:` = `src/quotient.jl`
- `GR:` = `src/grid.jl`
- `EL:` = `src/element.jl`

**Oracle:** Julia 1.13.0 with the registered stack was used for all behaviour claims marked (✓J). Dependency versions: MeshTopology 0.1.0, StaticVectors 1.0.9, AbstractTensors 0.8.11, Cartan 0.4.16.

**Golden artifacts written alongside this report** (directory `notes/meshtopology_oracle/`):
- `patched.jl`: a loader that makes upstream code runnable (see §9.1);
- `mtsrc/`: a patched copy of `src`;
- `dump_goldens.jl`: the generator;
- `meshtopology_goldens.json`: ~550 KB, 110 quotient-topology cases, 7 simplex meshes, and cross products. The schema is described in §9.

---

## 0. TL;DR for the implementer

1. **Scope.** MeshTopology is the *combinatorial* layer under Cartan.jl. It holds only integers: node ids, element connectivity and boundary gluing tables. It has no coordinates. Everything is `Values{N,Int}` (a static N-tuple of 1-based Ints) arranged in arrays.
2. **The four families:**
   - **ProductTopology.** A lazy Cartesian grid of integer ranges.
   - **QuotientTopology.** A structured grid `s = (n1,…,nN)` with a per-face gluing table. This covers torus, Möbius, Klein, sphere, ball, cone, Hopf and so on. Its heart is the O(1) "ghost index" resolver `m[Val(K), i…]` used by finite-difference stencils. Its second heart is `elementfuns`, which identifies duplicate grid points into canonical node ids for building quad or triangle meshes.
   - **SimplexTopology / DiscontinuousTopology.** An unstructured simplex list with sub-mesh views.
   - **LagrangeTopology.** Higher-order (P_M) node numbering for triangles and tets, built from edge and facet tables.
3. **Most of the shipped package is broken.**
   - Several files reference `Grassmann.*`, `Leibniz.*`, `Submanifold` and `∂`, none of which are imported (a leftover of the split from Cartan). So these throw `UndefVarError` in *every* environment, even with Cartan loaded (✓J):
     - `simplexnumber` and therefore **all Lagrange constructors**;
     - `edges`/`adjacency`/`antiadjacency`/`sparse` for N≥3;
     - `faces`, `facets`, `facetsinterior`, `_facetsindices`, `skeleton`;
     - non-open `resample`.
   - There are about 30 further latent bugs, listed in §8.6 (Q-list).
   - **The Lean port should implement the intended semantics.** It should replicate observable quirks only where a caller could depend on them; the Q-list marks each case.
4. **Conventions that must be preserved bit-for-bit** (the goldens depend on them):
   - 1-based ids;
   - column-major linearization;
   - face numbering `2a-1` = low end and `2a` = high end of axis `a`;
   - closed periodic grids (node 1 ≡ node n);
   - **colex edge ordering**;
   - edge-opposite-vertex local numbering for triangles;
   - lexicographic local edge numbering for tets;
   - the Lagrange node numbering formulas of §4.7.

---

## 1. Purpose & scope

The README (lines 15-16, 28-62) describes the package as a "foundational unified topological framework for various types of computational meshes, purpose-built for the formulation of manifolds with non-trivial topological structure". It "unifies grids, quotient topology, and Lagrange simplex finite elements with support for fiber product topology".

The README defines the core alias (README:34, MT:76):

```
ImmersedTopology{N,M} = AbstractArray{Values{N,Int},M}
```

Every topology object *is* an `M`-dimensional array whose entries are `N`-tuples of node indices:
- **Simplex meshes:** `M = 1` (a list of elements); `N` = vertices per element.
- **Grid (quotient) topologies:** `M = N` = grid dimension, and each entry is the multi-index that grid point is identified with.

**Downstream usage** (grep counts over Cartan.jl + Adapode.jl):

| Function | Uses | Function | Uses |
|---|---|---|---|
| `resample`/`resize` | 65 | `columns` | 18 |
| `edges` | 36 | `edgesindices` | 21 |
| `faces`/`facets` | 29 | `neighbors` | 17 |
| `totalnodes` | 28 | `degrees`/`weights` | 28 |
| `discontinuous`/`disconnect` | 28 | `incidence`/`adjacency` | 22 |
| `interp` | 20 | `interior` | 12 |
| `verticesinv` | 10 | `facetsigns` | 10 |
| `subimmersion`/`fullimmersion` | 12 | `LagrangeTriangles`/`Tetrahedra` | 7 |
| `BilinearTopology`/`elementsplit` | 7 | `elementfuns`/`linearelements` | 4 |

Cartan's grid stencils call `immersion(g)[Val(K), i…]` per point per axis. This is the perf-critical path (see `cartan-core.md` §4.5.3).

**Out of scope here, owned by the Cartan port:**
- the `XParameter` constructors (QT:87-127; they need Cartan's `ProductSpace`, `PointArray` and `⊕`);
- `SimplexManifold`, `boundary`, `edgelengths`, `laplacian`, `rms`, `select` and `unbundle`, which are exported by MT but defined only in Cartan (Cartan `element.jl:17-19,56-58,125-126`, and `laplacian = Diagonal(degrees) - adjacency` at Cartan `element.jl:505-506`);
- `∂` on topologies, defined in Cartan (`element.jl:251-266`) on top of `facets`/`facetsinterior`.

---

## 2. Public API inventory

**Legend for the Status column:**
- **E** = exported;
- **u** = unexported but used by Cartan (imported explicitly at Cartan `topology.jl:183-227`, `quotient.jl:16-131`, `element.jl:159-854`);
- **✗** = exported but undefined in MT.
- **B(Qn)** = broken; see the Q-list in §8.6.

**Unicode operators:**
- `×` is `LinearAlgebra.cross` (ASCII alias `cross`).
- `⊆`/`⊂` appear only in display output.
- `∂` is Grassmann's; it has no definition in MT.
- `:` (Colon) is overloaded for `Values`.

### 2.1 `MeshTopology.jl` (core)

| Symbol | Signature → result | Semantics | Status | Line |
|---|---|---|---|---|
| `Values` | re-export of `StaticVectors.Values{N,T}` | static tuple | E | MT:29 |
| `resample` | `resample(m::OneTo,i::Int)` → `LinRange(1,m.stop,i)` | same for UnitRange/StepRange/LinRange: `LinRange(first,last,i)` | E | MT:36-39 |
| | `resample(m::StepRangeLen,i)` → `range_start_step_length(m[1], step*(len-1)/(i-1), i)` | uniform respacing | E | MT:40 |
| | `resample(m::AbstractRange)` → `m`; `resample(m::AbstractRange,(i,))` → `resample(m,i)` | | E | MT:41-42 |
| | `resample(m::AbstractArray{T,0}, ())` → `m`; `resample(m::AbstractVector,(i,))`, `resample(m::AbstractVector,i=length(m))` → `LinRange(m[1],m[end],i)` | | E | MT:43-46 |
| | `resample(m,i::Int...)` → `resample(m,i)` | vararg to tuple | E | MT:155 |
| | `resample(m::ProductTopology{N}, i::NTuple{N}=size(m))` → `ProductTopology(resize.(m.v,i))` | **not LinRange: calls `resize` per axis** | E, **B(Q15) for N=1 with a tuple** | MT:156-159 |
| `CrossRange` | `struct CrossRange <: AbstractVector{Int}; n::Int; m::Int end`; `CrossRange(n)=new(n,crossrange(n))` | antipodal (half-turn) map on a closed periodic axis | E | MT:48-53 |
| `crossrange(n)` | `Int((isodd(n) ? n+1 : n)/2) - 1` = `ceil(n/2)-1` | shift amount | u | MT:55 |
| | `length(t)=t.n`; `size=(n,)`; `t[i] = i ≤ t.m ? i+t.m : i-t.m`; `iterate` | | | MT:57-63 |
| `ImmersedTopology{N,M}` | `const = AbstractArray{Values{N,Int},M}` | root alias | E | MT:76 |
| `immersion` | `const immersion = ImmersedTopology` | a type alias used as an accessor name; Cartan adds `immersion(::FiberBundle)` | E | MT:83 |
| `sdims` | `sdims(::ImmersedTopology{N}) = N`, also on `Type` | simplex arity (vertices per element) | u | MT:90-91 |
| `immersiontype(m)` | `typeof(m)` | | u | MT:98 |
| `fullimmersion(m::ImmersedTopology)` | `m` | overridden per type | u | MT:106 |
| `topology(m::ImmersedTopology{N,1})` | `m` | | E | MT:108 |
| `subelements(m::ImmersedTopology{N,1})` | `OneTo(length(m))` | | u | MT:109 |
| `ProductTopology{N,S<:AbstractVector{Int}}` | `v::Values{N,S}`, subtype of `ImmersedTopology{N,N}` | lazy grid: `m[i1..iN] = Values(v[1][i1],…,v[N][iN])` | E | MT:129-132 |
| | `ProductTopology()` (0-D, `Values{0,Vector{Int}}()`); `ProductTopology(i::Int, jk::Int...)` → `OneTo`s; `ProductTopology(i::AbstractVector, jk...)` | constructors | E | MT:133-137 |
| `show` | only for range axes | `print(Values(first.(v)), ':', Values(last.(v)))` | | MT:139 |
| `(:)(min::Values{N,Int}, max::Values{N,Int})` | `ProductTopology(min[k]:max[k])`; also a 3-argument version with step | `Values(1,1):Values(3,4)` | E (Base method) | MT:141-142 |
| `resize` | `resize(::OneTo,i)=OneTo(i)` | | u | MT:147 |
| | `resize(m::StepRange,i) = isone(m.start) ? 1:1:i : i:-1:1` | any other StepRange becomes reversed | u | MT:148 |
| | `resize(::CrossRange,i)=CrossRange(i)` | | u | MT:149 |
| | `resize(m::ProductTopology,i)` | resizes the **last axis only** | u | MT:150-153 |
| | UnitRange / generic Vector | no method (MethodError) | u | – |
| `size`, `getindex` (Cartesian, linear, CartesianIndex), `IndexStyle=IndexCartesian`, `eltype` | – | column-major linear indexing | | MT:161-179 |
| `exclude(m::ProductTopology{N}, Val(n1)[,Val(n2)…])` | `ProductTopology(m.v[all axes except n…])` | up to 4 excluded axes; `N==2` has a special case | u | MT:183-202 |
| `cross` (`×`) | `a::PT × b::PT` → concatenates axes; `PT×AbstractVector`, `AbstractVector×PT`, `PT×Int` (→`OneTo`), `Int×PT` | product grid | E (LinearAlgebra) | MT:204-208 |
| `top_id` | `top_id = 0`, a **mutable global** incremented by id-less constructors | bundle cache key | u | MT:212 |
| `refval`, `refnodes`, `RefInt` | `RefInt = Union{RefValue{Int},Int}` | node-count sharing | u | MT:214-218 |
| `SimplexTopology{N,P,F,T}` | fields `id, t::Vector{Values{N,Int}}, i::P, p::RefValue{Int}, f::F, I::P, v::P`; `T=(istotal,isfull)::Tuple{Bool,Bool}` | continuous simplicial (sub)mesh | E | MT:235-249 |
| constructors | `SimplexTopology(id,t,i=vertices(t),p=maximum(i))` (istotal = `length(i)==p`, isfull = true); `SimplexTopology(id,t,p)`; `SimplexTopology(t,…)` → `id = (top_id += 1)`; `SimplexTopology(t::SimplexTopology) = t` | | E | MT:251-258 |
| `bundle` | `m.id` | | u | MT:265 |
| `fulltopology` | `m.t` | | u | MT:272 |
| `topology` | `isfull ? t : view(t,f)` | | E | MT:279 |
| `totalelements` | `length(t)` | | u | MT:286 |
| `elements` | `length(f)` | | u | MT:293 |
| `subelements` | `f` | | u | MT:300 |
| `refnodes` | `p` | | u | MT:307 |
| `totalnodes!` | `p.x = n` (mutation) | | u | MT:308 |
| `totalnodes` | `p[]` | | u | MT:315 |
| `nodes` | `length(i)` | | u | MT:322 |
| `fullvertices` | `I` | | u | MT:329 |
| `vertices` | `i` | | E | MT:336 |
| `verticesinv` | `v` | | u | MT:337 |
| `size`, `length`, `axes` | `size(f)`, etc. | | | MT:339-341 |
| `m[k::Int]` | `t[getfacet(m,k)]` | | | MT:342 |
| `AbstractTensors.mdims(m)` | `N` | | | MT:343 |
| `getimage(m,i)` | `iscover ? i : vertices[i]` (`i` if `P<:OneTo`) | subspace vertex → full vertex id | u | MT:350-351 |
| `getfacet(m,i)` | `isfull ? i : f[i]` (`i` if `F<:OneTo`) | subspace element → full element id | u | MT:358-359 |
| `istotal` / `isfull` / `iscover` | `T[1]` / `T[2]` / `isfull && istotal` | | u/u/E | MT:366,373,380 |
| `untotal(t,p)` | rebuild with `istotal = false` and node count `p` | | u | MT:382-384 |
| `fullimmersion_vertices(m)` | `istotal ? OneTo(totalnodes) : (maximum(I)==length(I) ? OneTo : I)` | | u | MT:386-394 |
| `fullimmersion(m::SimplexTopology)` | full element list, same id and node Ref | | u | MT:396-399 |
| `m[ks::AbstractVector{Int}]` | element subset (§4.6) | | | MT:401-405 |
| `(m)(vs)` = `subtopology(m, vs::AbstractVector{Int})` | vertex-induced subset | | u | MT:407-415 |
| `getelement(m,i)` | element `i` with vertices renumbered through `verticesinv` | | u | MT:417-420 |
| `subtopology(m)` | all elements renumbered | | u | MT:422-425 |
| `subimmersion(m)` | standalone renumbered mesh (id 0) | | u | MT:432-442 |
| `verticesinv(n,ind,isc)` | `isc ? ind : (out=zeros(n); out[ind]=1:len; out)`; `OneTo` passthrough | | u | MT:444-451 |
| `refine(m)` | materialize `OneTo` fields into `Vector`s (for later mutation by Cartan's mesh refinement) | | u | MT:453-466 |
| `DiscontinuousTopology{N,P,T<:SimplexTopology{N}}` | fields `id, t::T, i::P, I::P` | every element gets private nodes | E | MT:483-488 |
| constructors | `DiscontinuousTopology(m)` (id is 0 if `bundle(m)==0`, else fresh); `(m,I)`; `(id,m)`; `(id,m,I)` | | E, **B(Q17) for non-full m** | MT:490-517 |
| `SimplexTopology(d)` | `d.t` | | | MT:518 |
| `discontinuousvertices(d)` | length `N*totalelements`; entry `N(e-1)+k` = `e` | node → owning element | u | MT:520-528 |
| forwarded | `totalelements, elements, subelements, istotal, isfull, iscover` → `d.t` | | | MT:530-532 |
| `bundle(d)` | `d.id` | | | MT:533 |
| `fulltopology(d)` | `topology(fullimmersion(d))` | | | MT:534 |
| `topology(d)` | `collect(d)` | | | MT:535 |
| `totalnodes(d)` / `nodes(d)` | `N*totalelements` / `N*elements` | | | MT:536-537 |
| `fullvertices(d)` / `vertices(d)` | `d.I` / `d.i` | | | MT:538-539 |
| `isdiscontinuous` | `false` for Simplex, `true` for Discontinuous | | u | MT:546-547 |
| `isdisconnected` | `true` iff `P<:OneTo` | | u | MT:554-556 |
| `d[k::Int]` | `(1:N) .+ N*(getfacet(d,k)-1)` | | | MT:561 |
| `getimage(d,i)` | `OneTo` → `i`; else `vertices(d)[i]` (discontinuous node → continuous vertex) | | u | MT:564-565 |
| `fullimmersion(d)` | `DiscontinuousTopology(id, fullimmersion(t), ind, ind)` with `ind = fullimmersion_vertices(d)`; **becomes disconnected (OneTo) when istotal** | | | MT:568-571 |
| `d[ks]`, `d(vs)` | subsets | **B(Q17)** | | MT:573-580 |
| `continuous(m)` | `m` for Simplex; `m.t` for Discontinuous | | E | MT:587-588 |
| `discontinuous(m)` | `DiscontinuousTopology(0, m)`; identity on Discontinuous | | E | MT:595-596 |
| `disconnect(m)` | `DiscontinuousTopology(id, t, OneTo(totalnodes))` | | E | MT:603-604 |
| `getelement`, `subtopology`, `subimmersion`, `refine` on Discontinuous | analogous | | u | MT:606-625 |
| `_axes(t)` | `(OneTo(length(t)), OneTo(N))` | for display | u | MT:702 |
| `summary`/`array_summary` | §5 | for Simplex, Discontinuous and Lagrange | | MT:704-714 |
| `SimplexManifold` | – | **✗** | E | MT:67 |
| `VectorTopology` | commented out; skip | – | – | MT:627-693 |

### 2.2 `lagrange.jl`

| Symbol | Signature → result | Status | Line |
|---|---|---|---|
| `simplexnumber(N,n)` | `binomial(n+N-1, N)` (the n-th N-simplex number) | u, **B(Q1)** | LG:21 |
| `trinum(n)`, `tetnum(n)` | `simplexnumber(2,n)`, `simplexnumber(3,n)` | u | LG:22-23 |
| `LagrangeTopology{M,N,P,F,T}` | abstract, subtype of `ImmersedTopology{N,1}`; `M` = polynomial degree, `N` = nodes per element | E | LG:25 |
| forwarded | `totalelements, elements, subelements, istotal, isfull, iscover, isdiscontinuous, isdisconnected` → `cornertopology(m)` | | LG:27-29 |
| `bundle`, `fulltopology = topology(fullimmersion(m))`, `topology = collect(m)` | | u | LG:30-32 |
| `totaledges(m)` | `totalnodes(edgesindices(m))` (the edge count) | u | LG:33 |
| `totalfacets(m)` | `totalnodes(facetsindices(m))` | u | LG:34 |
| `totalcornernodes(m)` | `totalnodes(cornertopology(m))` | E | LG:35 |
| `totaledgesnodes(m)` | `(M-1)*totaledges(m)` | E | LG:36 |
| `totalfacetsnodes(m)` | `facetsimplex(m)*totalfacets(m)` | u | LG:37 |
| `totalcenternodes(m)` | `centersimplex(m)*totalelements(m)` | E | LG:38 |
| `cornernodes`, `edgesnodes`, `facetsnodes`, `centernodes` | subspace analogues using `nodes(…)`/`elements` | E/E/u/E | LG:39-42 |
| `lagrangesimplex(N,M)` | `simplexnumber(N-1,M+1)` = `binomial(M+N-1, N-1)` (nodes per element, N corners) | u | LG:47 |
| `centersimplex(N,M)` | `simplexnumber(N-1,M-N+1)` = `binomial(M-1, N-1)` (interior nodes) | u | LG:48 |
| `facetsimplex(N,M)` | `centersimplex(N-1,M)` | u | LG:49 |
| `edgesimplex(N,M)` | `M-1` | u | LG:50 |
| `fullvertices`, `vertices` | `m.I`, `m.i` | u/E | LG:51-52 |
| `size`, `length`, `axes`, `mdims` | via the corner topology | | LG:55-58 |
| `getimage`, `getfacet`, `subtopology(m)` | as for Simplex | u | LG:60-67 |
| `LagrangeEdges{M,N,P,F,T}` | fields `id, t::SimplexTopology{2}, i, I` | u, **B(Q18)** | LG:71-82 |
| `LagrangeTriangles{M,N,P,F,T}` | fields `id, t::SimplexTopology{3}, e::SimplexTopology{2}` (edges), `ei::SimplexTopology{3}` (element→edge ids), `i, I` | E | LG:84-97 |
| `LagrangeTetrahedra{M,N,P,F,T}` | fields `id, t{4}, f{3}` (facets), `e{2}`, `fi{4}` (element→facet ids), `ei{6}` (element→edge ids), `i, I` | E | LG:99-114 |
| constructors | `LagrangeEdges{M}(t)`, `LagrangeTriangles{M}(t, e=edges(t), ei=edgesindices(t,e))`, `LagrangeTetrahedra{M}(t)` (computes `e`, `(f,fi) = _facetsindices(t)`, `ei`) plus `(id,…)` variants | E | LG:116-150 |
| `cornertopology` | `m.t` | E | LG:152 |
| `edges`, `edgesindices` | `m.e`, `m.ei` (for LagrangeEdges: `m.t` and `Values.(subelements(t))`) | E | LG:153-158 |
| `facets`, `facetsindices` | Triangles: `m.e`, `m.ei`; Tetrahedra: `m.f`, `m.fi` | E/u | LG:159-164 |
| `totalnodes`, `nodes` | the sum of the corner, edge, facet and center counts | u | LG:166-171 |
| `lagrangevertices2/3/4` | vertex list of a subset (§4.7) | u | LG:173-190 |
| `edgesindex`, `facetsindex`, `centerindex` | node-number generators (generated functions) | u | LG:192-251 |
| `getedge(m,i)` | interior nodes of full edge `i`: `edgesindex(Values(getfacet(edges(m),i)), np, Val(M))` | u | LG:252-254 |
| `getlagrange1..4`; `m[i]` dispatch | element node list (§4.7) | u | LG:255-282 |
| `fullimmersion`, `m[ks]`, `m(vs)` | | u | LG:284-322 |
| `_getelement`, `getelement1..4`, `getelement` | renumbered element; **B(Q18) typos** | u | LG:330-369 |
| `subimmersion` | **B(Q18): `M` undefined** | u | LG:371-402 |
| `refine` | materialize | u | LG:404-447 |

### 2.3 `quotient.jl`

| Symbol | Signature → result | Status | Line |
|---|---|---|---|
| `QuotientTopology{N,L,M,O,LA<:ImmersedTopology{L,L}}` | fields `p::Values{O,Int}, q::Values{O,LA}, r::Values{M,Int}, s::Values{N,Int}, c::Values{M,Int}`; constructor `QuotientTopology(p,q,r,s,c=zeros)` | E | QT:27-36 |
| `invert_q(Val(O), r)` | the faces `f` with `r[f] ≠ 0`, in face order (length O) | u | QT:40-43 |
| `OpenTopology{N,L,M,LA}` | alias `QuotientTopology{N,L,M,0,LA}` | E | QT:45 |
| `CompactTopology{N,L,M,LA}` | alias `QuotientTopology{N,L,M,M,LA}` | E | QT:46 |
| `QuotientTopology(n::ProductTopology)`, `OpenTopology(n::ProductTopology)` | `OpenTopology(n.v)`: **routes to ProductSpace, B(Q33)** | E | QT:47-48 |
| `OpenTopology(n::QuotientTopology)` | `OpenTopology(size(n))` | E | QT:49 |
| `OpenTopology(n::Values{N,Int})` | `QuotientTopology((), (), zeros(2N), n)` | E | QT:50 |
| named constructors on `Values{N,Int}` | `Cylinder(2)`, `Mobius(2)`, `Wing(2)`, `Mirror(1..5)`, `Clamped(1..5)`, `Torus(1..5)`, `Hopf(2,3)`, `Klein(2)`, `Cone(2)`, `Tube(2,3)`, `Ball(1..5)`, `Sphere(1..5)`, `Geographic(2)`: full table in §4.3 | E | QT:51-85 |
| `XParameter` | 14 families (Open, Cylinder, …, Geographic) | unexported, needs Cartan; Q26 | QT:87-127 |
| generic methods per family `X ∈ {Open,…,Geographic}` | `X(p::Values{N,<:AbstractVector})` → `X(ProductSpace(p))` (Cartan); `X(p::AbstractVector...)`; `X(n::NTuple)` → `X(Values(n))` | E | QT:129-139 |
| defaults | Hopf: `X(n::Int...)`, `X()=X(7,60,61)`; Open/Mirror/Clamped/Torus: `X()=X(61,61)`, `X(n::Int...)`; Tube/Ball/Sphere: `X(n::Int...)`; `Cylinder(n=61,m=20)`, `Wing(61,20)`, `Mobius(61,20)`, `Klein(61,61)`, `Cone(n=31,m=2n+1)`, `Geographic(n=61,m=n÷2)` | E | QT:140-171 |
| | `TubeTopology()=Tube(20,61)`; `BallTopology()=TubeTopology(20,61)` **(Q8)**; `SphereTopology()=TubeTopology(31,61)` **(Q8)** | E | QT:172-177 |
| `PolarTopology`, `RevolvedTopology` | `= BallTopology`, `= TubeTopology` (function aliases) | E | QT:179-181 |
| `isopen(t)` | `O == 0` (false for the generic method, true for `OpenTopology`) | u | QT:183-184 |
| `iscompact(t)` | intended `O == 2N`; **the Julia call is ambiguous for every compact topology (Q2)** | u | QT:185-186 |
| `_to_axis(f)` | `(iseven(f) ? f : f+1) ÷ 2` = `ceil(f/2)` | u | QT:187 |
| `zerotuple`, `zeroprodtop` | helpers (`r==0 ? () : (ProductTopology(sizes),)`) | u | QT:189-193 |
| `cross` (`×`) | `Open×Open`, `Open×Int`, `Int×Open`, `Q×Int`, `Int×Q` (**Q12**), `Q{a}×Q{b}` for (a,b) ∈ {(1,1),(1,2),(2,1),(1,3),(3,1),(1,4),(4,1),(2,2),(2,3),(3,2)} | E | QT:195-283 |
| `cross_sphere(Q1,Q1)`, `cross_sector(Q1, Q1..Q4)` | build polar/spherical gluings from 1-D factors | u | QT:285-314 |
| `getlocate(a, x, t...)` | insert `x` at position `a` of `t` (N ≤ 5) | u | QT:316-321 |
| `locate_fast`, `locate`, `location` | ghost-index formulas (§4.4) | u | QT:323-361 |
| `resize(m::QuotientTopology, i)` | set the last axis size to `i`; resize `q` maps (**Q16**) | u | QT:363-378 |
| `resample(m::QuotientTopology, i::NTuple=size(m))` | all sizes; resample `q` (**Q14, Q1, Q15**) | E | QT:380-393 |
| `size(m) = m.s.v`, `eltype = Values{N,Int}`, `iterate` (column-major) | | | QT:395-398 |
| `m[i1,…,iN]` | `N>5 ? Values(i) : m[Val(0), i…]` | | QT:400-402 |
| `m[i]` (N=1) | §4.4 | | QT:403-416 |
| `bounds(i,n,Val(K),Val(a))` | `(K==0 \|\| K==a) ? (1<i<n) : (0<i≤n)` | u | QT:418 |
| `m[Val(K), i…]` for N=1..5 | ghost resolver (§4.4); **Q11 for N=5** | | QT:420-561 |
| `findface` | slicing helper (§4.5) | u | QT:563-577 |
| `subtopology(m::QuotientTopology, …)` and call syntax `m(i…, :, j…)` | slices keeping 1..4 axes (§4.5) | u | QT:579-752 |

### 2.4 `grid.jl`

| Symbol | Signature → result | Status | Line |
|---|---|---|---|
| `MultilinearTopology{N}` | abstract, subtype of `ImmersedTopology{N,1}`; `MultilinearTopology(m::QuotientTopology{2}) = BilinearTopology(m)` | E | GR:19, 216 |
| `linearelement(l::AbstractArray{T,d}, i…)` | d = 1..5: the corner values of the cell at `(i…)` in a fixed order (§4.8) | E | GR:21-50 |
| `linearelements(l::AbstractArray{T,d}, s=size(l))` | the array of all cells, size `s .- 1` | E, **B(Q4) d=1, Q5 d=4** | GR:52-56 |
| `linearelements(m::QuotientTopology)` | `linearelements(elementfuns(LinearIndices(m), m))` | E | GR:58-59 |
| `linearelement(m::QuotientTopology, ij…)` | cell with `elementfun` values | E | GR:60-90 |
| `elementfuns(m)` / `elementfuns(l, m, s)` | canonical linear index per grid point (§4.6), then collapse; returns `LinearIndices` for Open or N≥… | E | GR:92-145 |
| `elementfun(m, ij…)` | `min(getlinear(l,m,Val(0),ij…), l[ij…])` | E | GR:147-152 |
| `mycollect`, `mycollect2` | debug helpers (`mycollect` has no matching method) | u | GR:154-155 |
| `getlinear(l, m, Val(K), ij…)` | §4.6; the generic version returns `l[ij…]` (**Q6**) | u | GR:162-198 |
| `BilinearTopology{Q,P,V}` | fields `m::Q, q::Vector{Values{4,Int}}, t::Vector{Values{3,Int}}, i::P, v::V, iq, it::Vector{Int}, s::Vector{Pair{Int,Int}}`; subtype of `MultilinearTopology{4}`; no `size` method (**Q23**) | E | GR:204-214 |
| `BilinearTopology(m::QuotientTopology{2})` | `efs=elementfuns(m)`; `detect_tri(vec(linearelements(efs)))`; `i=vertices(efs)`; `v=to_verticesinv(efs)` | E | GR:217-222 |
| `QuotientTopology(t)`, `vertices`, `verticesinv`, `nodes = length(v)`, `elementsplit`, `elementquad`, `elementtri` | accessors | E | GR:224-230 |
| `detect_tri(quad)` | split degenerate quads into triangles (§4.8) | u | GR:232-264 |
| `elementsplit(iq,it)` | `out[iq[j]] = 4=>j`, `out[it[j]] = 3=>j` | E | GR:265-277 |
| `to_verticesinv(m)` | `unique(vec(m))` (`OneTo` for LinearIndices) | u | GR:279-280 |
| `verticesinv(m::QuotientTopology)` | `unique(vec(elementfuns(m)))`; `OneTo(length)` for Open | u | GR:281-282 |
| `duplicates(m)` | `setdiff(vec(LinearIndices), vec(elementfuns))` | u | GR:283-286 |
| `duplicatemap(m)` | `dup .=> els[dup]` | u | GR:287-292 |
| `uniquemap(m)` | `unique(els) .=> 1:k` | u | GR:293-297 |
| `vertices(m::QuotientTopology)` / `vertices(elm::Array{Int})` | compact renumbering (§4.6) | E | GR:298-308 |

### 2.5 `element.jl`

| Symbol | Signature → result | Status | Line |
|---|---|---|---|
| `column(t,i=1)` | `getindex.(value(t), i)` | u | EL:24 |
| `columns(t::ImmersedTopology{N})` / `columns(t::AbstractVector{<:Values{N}})` | `Values{N}` of vectors: column `k` = the k-th vertex of each element (uses `topology(t)`, so **full ids**) | u | EL:25-28 |
| `reducedcolumns(m::SimplexTopology)` | `iscover ? columns(m) : columns(subtopology(m))` (**renumbered ids**) | u | EL:30 |
| `vertices(e::ImmersedTopology{N,1})` | distinct ids in first-appearance order; returns `OneTo(n)` iff `max == count` | E | EL:34-47 |
| `pointset` | `= vertices` | u | EL:33 |
| `vertices(e::ImmersedTopology{1,1})` | `column(e)` | E | EL:32 |
| `sparse(t::SimplexTopology, cols=reducedcolumns(t), np=nodes(t))` | directed pair count `A[c_a[k], c_b[k]] += 1` for local a<b | u, B(Q1) | EL:51-57 |
| `adjacency(t, cols=reducedcolumns(t), n=nodes(t))` | `A + Aᵀ` | E, B(Q1) | EL:50 |
| `antiadjacency(t, cols=…, n=…)` | `A - Aᵀ` | E, B(Q1) | EL:49 |
| `edges(t)` | `SimplexTopology{2}` of unique edges in **colex** order (§4.9); `edges(t::SimplexTopology{2}) = t` | E, B(Q1) for N≥3 | EL:59-66 |
| `edgetopology(adj)` | `findall(!iszero, triu(adj))` → `Values(row, col)` pairs | u | EL:67-70 |
| `edges(t::DiscontinuousTopology{3})` | per-element `(t1,t2),(t2,t3),(t3,t1)` using discontinuous ids | E | EL:71-82 |
| `facetsinterior(t)` | `(SimplexTopology of facets in first-appearance order, bnd)` where `bnd` lists the indices of facets met a second time | u, B(Q1) | EL:84-96 |
| `facets(t) = faces(t, Val(N-1))`, `facets(t,h) = faces(t,h,Val(N-1))` | | E | EL:97-98 |
| `faces(t, N::Int)` | `faces(t, Val(N))` | E | EL:100 |
| `faces(t, Val(k))` | `k==N`: `t`; `k==2`: `edges(t)`; `k==1`: vertex singletons; else first-appearance sorted k-subsets | E, B(Q1) | EL:101-114 |
| `_facetsindices(t)` | `(facets, element→facet-id table ordered opposite-vertex)` | u, B(Q1) | EL:115-141 |
| `faces(t, h, Val(k), g=identity)` | oriented (co)boundary sums: `(facet list, coefficient vector)` (§4.9) | E, B(Q1) | EL:142-166 |
| `complement(t)` | `fullimmersion(t)[setdiff(1:totalelements, subelements)]` (AbstractTensors.complement) | E (AT) | EL:188-190 |
| `skeleton(t)` | `faces.(t, ones, Val(1..N+1), abs)` | u, B(Q1) | EL:193 |
| `isedge(e)`, `isedge(e,t)` | `all(e .∈ t)` | u | EL:196-197 |
| `discontinuousboundary(dt, e)` | map continuous boundary edges to discontinuous node pairs | u | EL:198-207 |
| `assemblelocal!(M, mat, [m,] tk)` | `M[tk[i],tk[j]] += mat[i,j]*m` | u | EL:285-298 |
| `weights(t)` | `inv.(degrees(t))` (Float64, `Inf` for unused nodes) | E | EL:300 |
| `weights(t,B)`, `degrees(t,B)` | `B*ones(totalnodes)`: **dimension bug (Q20)** | E | EL:301-302 |
| `degrees(t)` | number of elements containing each node (length `totalnodes`) | E | EL:303-309 |
| `assembleincidence(t,f,m,Val(T))` | needs Cartan's `fibertype`/`fiber` | u, broken standalone | EL:311-319 |
| `incidence(t, cols=columns(t))` | sparse `totalnodes × elements`, `A[v,e] = multiplicity` | E | EL:320-327 |
| `interp(t,B)`, `interp(d::Discontinuous, b[,w])` = `view(b, discontinuousvertices(d))`, `interp(t::Simplex, b, w)` | | E, **Q20** | EL:329-334 |
| `pretni` | reverse interp | u, Q20 | EL:333-334 |
| `invmap(t::Values{3},n)` | local position of `n` (defaults to 3) | u | EL:336 |
| `findmissing(n::Values{2})` | the local index in {1,2,3} not in `n` | u | EL:337 |
| `interior(e)`, `interior(fixed, neq)` | `sort!(setdiff(1:neq, fixed))`; the one-argument form is **Q19** | E | EL:339-340 |
| `facesindices(t)` | `edgesindices(t)` if N==3, else error | u | EL:342 |
| `edgesindices(t, et=edges(t))` | element→edge id table (§4.9) | E, **Q21** | EL:344-349 |
| `localedge(A, v::Values{2..5})` | local edge ordering | u | EL:350-366 |
| `neighbor(k, ab...)` | first of `setdiff(intersect(ab...), k)`, or 0 | u | EL:368-371 |
| `neighbors(t, n2e=incidence(t))` | per element: the element across the facet opposite each vertex (0 = boundary) | E | EL:373-393 |
| `facetsign(i,ni) = i<ni ? 1 : -1`; `facetsigns(t)` | | E | EL:395-397 |
| `edgesigns(i::Values{2..5})` | orientation sign per local edge (§4.9) | u | EL:399-402 |
| `facets(i::Values{2..5})` | oriented local facets (**Q22 for 5**) | E | EL:404-407 |
| `refinement(t::LagrangeTriangles)` | subdivide P_M triangles into M² linear triangles (M ≤ 4) | u | EL:413-455 |
| `refinement(t::LagrangeTetrahedra)` | M=1 only | u | EL:459-465 |
| `refinetriangle(t::Values{3,6,10,15})`, `refinetetrahedron(Values{4})` | local tables | u | EL:419-465 |
| exported but undefined here | `edgelengths`, `laplacian`, `boundary`, `select`, `rms`, `unbundle`, `value` (re-exported from AbstractTensors) | ✗ / E | EL:15-18 |

---

## 3. Data representations

### 3.1 Global conventions

- **Ids are 1-based Julia `Int`.** Node ids, element ids, edge ids and face ids all start at 1. The value `0` is a sentinel for "none" (boundary neighbor, open face, not-in-subset in `verticesinv`).
- **Linearization is column-major.** `LinearIndices(s)[i1,…,iN] = i1 + (i2-1)s1 + (i3-1)s1 s2 + …`. `vec(A)` and all "colmajor" goldens use this order.
- **Faces of a grid axis.**
  - Axis `a` (1-based) has face `2a-1` at `i_a = 1` (low; ghost index 0) and face `2a` at `i_a = n_a` (high; ghost index `n_a+1`).
  - `_to_axis(f) = ceil(f/2)`.
  - Face `f` is *odd* iff it is a low face.
- **Periodic grids are closed.** Both endpoints exist, and node 1 and node n represent the same point, so the period is `n-1`. This is why the torus lookup maps index 0 to `n-1` (not `n`), and index 1 to `n`. `CrossRange(n)` is the half-turn `i ↦ i + (n-1)/2 (mod n-1)` for odd n; for even n it is only approximately antipodal.
- **Transversal coordinates of a face** are the coordinates of all other axes in ascending axis order. Gluing maps `q[slot]` take those as input and produce the target face's transversal coordinates (also ascending); the resolved axis coordinate is then *inserted* at the target axis position (`getlocate`).

### 3.2 `ProductTopology{N,S}`

- **Compile-time:** `N` (grid dimension) and `S` (axis vector type).
- **Runtime:** `v::Values{N,S}`, one integer vector per axis.
- **Element:** `m[i1..iN] = Values(v[1][i1], …, v[N][iN])`, so `size = length.(v)`.
- **Axis vectors that occur in practice:**
  - `OneTo(n)` (identity);
  - `n:-1:1` (reversal; `StepRange` with start ≠ 1);
  - `1:1:n` (identity, but typed as StepRange);
  - `a:b` (UnitRange, user-supplied);
  - `CrossRange(n)`;
  - arbitrary `Vector{Int}`.
- **A 0-D `ProductTopology()`** holds `Values{0,Vector{Int}}()`. As an array it is 0-dimensional and prints `fill(Int64[])`.

### 3.3 `QuotientTopology{N,L,M,O,LA}` (the gluing table)

| Param | Meaning | Compile-time in Julia | Lean recommendation |
|---|---|---|---|
| `N` | grid dimension | yes | **type index** (`QuotientTopology (N : Nat)`) |
| `L` | `N-1`, dimension of the `q` maps | yes | derived (`N-1`), not stored |
| `M` | `2N`, number of faces | yes | derived |
| `O` | number of glued faces | yes (drives `isopen`/`iscompact` dispatch) | **runtime** (`Array` length); `isopen := O==0`, `iscompact := O==2N` |
| `LA` | type of the q maps | yes | an `AxisMap` sum type |

**Fields (all runtime data):**
- `s::Values{N,Int}`: grid sizes.
- `r::Values{2N,Int}`: `r[f] ∈ 0..O`. `0` means face `f` is open (not glued). Otherwise it is the *slot* of the gluing data.
  - **Invariant in every constructor:** the nonzero entries of `r`, read in face order, are exactly `1,2,…,O`. So `r[f]` = rank of `f` among the glued faces, and `invert_q` inverts it.
- `p::Values{O,Int}`: `p[slot]` = the target face id (1..2N) for the glued face owning `slot`. `p[r[f]] = f` means a self-gluing, which is a reflection (mirror).
- `q::Values{O, ProductTopology{N-1}}`: `q[slot][transversal…]` = the target face's transversal coordinates (a `Values{N-1}`). For N=1 these are 0-D arrays that are never read.
- `c::Values{2N,Int}` ∈ {0,1}: **collapse** flags. `c[f]=1` means every grid point on face `f` is one node (a pole or center). It is used only by `elementfuns` (§4.6); `getindex` ignores it.

**Lean-optimal representation** (zero-cost normalization of `p`/`q`/`r`):

```lean
structure Glue (N : Nat) where
  target : Fin (2*N)                -- 0-based face id (Julia p-1)
  map    : Vector AxisMap (N-1)     -- per transversal axis (ascending)
inductive AxisMap | oneTo (n) | rev (n) | stepFwd (n) | cross (n) | explicit (a : Array Nat)
structure QuotientTopology (N : Nat) where
  s     : Vector Nat N
  faces : Vector (Option (Glue N)) (2*N)
  c     : Vector Bool (2*N)
```

`toTable` reproduces Julia's `(p, q, r)` for goldens: iterate faces, assign ranks. The product maps in QT are always per-axis (`ProductTopology` of 1-D vectors), so `Vector AxisMap (N-1)` is exact.

### 3.4 `SimplexTopology{N,P,F,T}`

| Field | Meaning | Julia kind |
|---|---|---|
| `N` | vertices per element (2 = edge, 3 = triangle, 4 = tet, 6 = element→6-edge table) | type param |
| `id` | bundle id for Cartan's caches; 0 = uncached; otherwise a globally incremented `top_id` | runtime |
| `t::Vector{Values{N,Int}}` | **fulltopology**: all elements of the parent mesh, as full vertex ids | runtime (shared by every sub-view) |
| `i::P` | **vertices** of this subspace (full ids). `OneTo(n)` when the vertex set is exactly `1..n`. Otherwise a `Vector` in first-appearance order (or the user's order for `m(vs)`) | runtime, P ∈ {OneTo, Vector} |
| `p::RefValue{Int}` | **totalnodes**: node count of the full mesh, *shared mutable* among views | runtime |
| `f::F` | **subelements**: indices into `t` (OneTo when full) | runtime |
| `I::P` | **fullvertices**: vertices of the parent (collected into a Vector when `P` is a Vector) | runtime |
| `v::P` | **verticesinv**: `i` itself when `istotal && isfull` (cover). Otherwise a length-`totalnodes` vector with `v[i[k]] = k` and 0 elsewhere | runtime |
| `T = (istotal, isfull)` | `istotal := length(i) == totalnodes` *as computed at the root* (subsets inherit the parent's value!), `isfull := length(f) == length(t)` | **type param** (Tuple of Bools) |

**Invariants:**
- `1 ≤ t[e][k] ≤ totalnodes`.
- `v[i[k]] == k` (when not a cover).
- `getfacet(m,k) = f[k]`, `getimage(m,k) = i[k]`.

**Lean representation:**

```lean
inductive IdxVec | range (n : Nat) | arr (a : Array Nat)
structure SimplexTopology (N : Nat) where
  id : Nat
  conn : Array Nat        -- flat, stride N (Julia t), size = N*totalElements
  verts fullVerts vinv : IdxVec
  sub : IdxVec            -- subelements
  totalNodes : Nat
  isTotal isFull : Bool
```

Make `N` a type index. Make `isTotal`/`isFull` runtime Bools (they are data-derived; making them indices forces sigma types for no measurable gain). The flat `conn` avoids one heap object per element; Julia's `Vector{Values{N,Int}}` is inline too.

### 3.5 `DiscontinuousTopology{N,P,T}`

- `t`: the continuous SimplexTopology.
- `i`: vertices, i.e. the **continuous vertex id of each discontinuous node**. It has length `N*elements` and comes from interleaving the element vertex lists: `i[N(e-1)+k] = t[e][k]`. For disconnected topologies it is `OneTo(N*totalelements)`.
- `I`: fullvertices.
- Discontinuous node numbering: element `e` owns nodes `N(e-1)+1 … N e`.

### 3.6 Lagrange topologies

`LagrangeTriangles{M,N,P,F,T}`:
- `M`: degree (type param);
- `N = lagrangesimplex(3,M) = (M+1)(M+2)/2` (type param, computed in the inner constructor at LG:92);
- `P,F,T` from the corner topology;
- fields: the corner mesh `t`, the edge mesh `e`, the element→edge table `ei` (a `SimplexTopology{3}` whose "nodes" are edge ids, with `totalnodes = #edges`), and `i`/`I` (node lists).

`LagrangeTetrahedra` adds the facet mesh `f` and the element→facet table `fi`, and uses the 6-edge table `ei`.

**Lean:** make `M` a type index; the per-element node count is `lagrangeSimplex d M`. Store per-element node lists lazily (compute on `get`, as Julia does); do not materialize them.

### 3.7 `BilinearTopology`

Fields:
- `m`: the quotient topology.
- `q`: quads.
- `t`: triangles.
- `i`: renumbered vertex array, the same shape as the grid.
- `v`: `verticesinv` = canonical linear ids in first-appearance order.
- `iq`, `it`: original cell ids.
- `s`: split pairs.

**Quad and triangle entries are canonical linear ids** (`elementfun` values in `1..prod(s)`), *not* compact node ids. Use `i[L]` to map a canonical id `L` to a compact node id `1..nodes`.

---

## 4. Algorithms

### 4.1 Utilities

```
crossrange(n)  = ceil(n/2) - 1                      # MT:55
CrossRange(n)[i] = i ≤ m ? i+m : i-m,  m=crossrange(n)
simplexnumber(N,n) = binomial(n+N-1, N)             # Julia binomial: 0 if k>n≥0
lagrangesimplex(N,M) = binomial(M+N-1, N-1)          # 3,6,10,15,21 for N=3; 4,10,20,35,56 for N=4
centersimplex(N,M)  = binomial(M-1, N-1)             # N=3: 0,0,1,3,6 ; N=4: 0,0,0,1,4
facetsimplex(N,M)   = centersimplex(N-1,M)           # N=4: 0,0,1,3,6 ; N=3: 0,1,2,3,4
edgesimplex(N,M)    = M-1
```

The oracle tables (JSON `numbers`) confirm these; M runs 1..5 in each row.

**Combinatorics used, all from unimported Grassmann/Leibniz:**
- `combo(n,g)` = lexicographic g-subsets of `1:n`, e.g. `combo(4,2) = [[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]`.
- `combinations(v,k)` = k-subsets of positions of `v` in lexicographic *position* order, e.g. `combinations([5,2,7],2) = [[5,2],[5,7],[2,7]]`.
- `indexparity!(v)` = in-place insertion sort with adjacent swaps; it returns `(odd_number_of_swaps, sorted)`, e.g. `indexparity!((3,1,2)) = (false, [1,2,3])`.
- `value(∂(pseudoscalar of dim M))` = boundary coefficients in lex order of the (M-1)-subsets: `[(-1)^(M-j) for j=1..M]`. So M=2 gives `[-1,1]`, M=3 gives `[1,-1,1]`, M=4 gives `[-1,1,-1,1]` and M=5 gives `[1,-1,1,-1,1]` (✓J).

### 4.2 ProductTopology

**Constructors:**
- `ProductTopology(3,4)` has axes `(OneTo(3), OneTo(4))`.
- `v1 × v2` concatenates axes.
- `Values(a…):Values(b…)` is `ProductTopology(a_k:b_k)`.

**Resizing:**
- `resize(m, i)` replaces the **last** axis by `resize(axis, i)`.
- `resample(m, (i1..iN))` resizes every axis.

**Exclusion:** `exclude(m, Val(k)…)` drops the listed axes (in ascending order of the remaining ones).

### 4.3 Named quotient topologies (QT:47-85)

**Notation:**
- `F1..F2N` are faces. `→g` means "glued to face g".
- `PT(…)` is a ProductTopology; `CR` is CrossRange; `rev(n) = n:-1:1`; `id(n) = OneTo(n)`.
- Transversal maps are listed per slot.
- `p` and `r` are the literal table entries.

**2-D tables:**

| Topology | p | r | q[slot] | c | Meaning |
|---|---|---|---|---|---|
| Open(N) | () | 0…0 | () | 0 | no gluing |
| Cylinder(n1,n2) | (2,1) | (1,2,0,0) | PT(n2), PT(n2) | 0 | axis 1 periodic |
| Mobius | (2,1) | (1,2,0,0) | PT(rev n2) ×2 | 0 | axis 1 periodic with flip `j ↦ n2+1-j` |
| Wing | (1,2) | (1,2,0,0) | PT(rev n2) ×2 | 0 | each i-end folded onto itself reversed (upper and lower wing surfaces) |
| Mirror(n1,…) | (1,) | (1,0,…) | PT(n2,…,nN) | 0 | F1 is a mirror; the rest open |
| Clamped | (1,2,…,2N) | (1..2N) | per face: PT(all other n) | 0 | every face is a mirror |
| Torus | (2,1,4,3,…) | (1..2N) | as Clamped | 0 | all axes periodic |
| Hopf(n1,n2) | (2,1,4,3) | (1,2,3,4) | PT(CR n2)×2, PT(n1)×2 | 0 | axis 1 periodic with half-turn in j |
| Klein | (2,1,4,3) | (1,2,3,4) | PT(rev n2)×2, PT(1:1:n1)×2 | 0 | axis 1 periodic flipped; axis 2 periodic |
| Cone | (1,4,3) | (1,0,2,3) | PT(CR n2), PT(n1), PT(n1) | 0 | F1 is an apex (self, half-turn); F2 open; axis 2 periodic |
| Tube(n1,n2) | (4,3) | (0,0,1,2) | PT(n1), PT(n1) | 0 | axis 2 periodic |
| Ball(n1,n2) = Polar | (1,2,4,3) | (1,2,3,4) | PT(CR n2), PT(n2), PT(n1)×2 | (1,0,0,0) | F1 is the center (self, half-turn, collapsed); F2 mirror; axis 2 periodic |
| Sphere(n1,n2) | (1,2,4,3) | (1,2,3,4) | PT(CR n2)×2, PT(n1)×2 | (1,1,0,0) | both poles self-glued with half-turn and collapsed; axis 2 periodic |
| Geographic | (2,1,3,4) | (1,2,3,4) | PT(n2)×2, PT(CR n1)×2 | 0 | axis 1 periodic; F3/F4 poles with half-turn **not collapsed** |

**1-D tables:**

| Topology | p | r | q | Note |
|---|---|---|---|---|
| Mirror(n) | (1,) | (1,0) | – | |
| Clamped(n) | (1,2) | (1,2) | – | |
| Torus(n) = Sphere(n) | (2,1) | (1,2) | – | |
| Ball(n) | – | – | – | `= Open(n)` |

**3-D and higher:**

| Topology | p | r | c | Line |
|---|---|---|---|---|
| Hopf(n1,n2,n3) | (2,1,4,3,6,5) | (1..6) | 0 | QT:70 |
| Tube(n1,n2,n3) | (1,2,6,5) | (1,2,0,0,3,4) | (1,0,1,1,0,0) | QT:74 |
| Ball(3) | (1,2,3,4,6,5) | (1..6) | (1,0,1,1,0,0) | QT:77 |
| Ball(4) | (1..6,8,7) | – | (1,0,…) | QT:78 |
| Ball(5) | – | – | – | QT:79, **typo `PRoductTopology` (Q9)** |
| Sphere(3) | (1,2,3,4,6,5) | – | **0** | QT:82 |
| Sphere(4) | (1..6,8,7) | – | 0 | QT:83 |
| Sphere(5) | (1..8,10,9) | – | 0 | QT:84 |

Transversal maps (`q`):
- **Hopf(3):** `q = PT(id n2, CR n3)×2, PT(id n1, CR n3)×2, PT(n1,n2)×2`.
- **Tube(3):** `q = PT(id n2, CR n3), PT(n2,n3), PT(n1,n2)×2`. F3/F4 are open but collapse flags are set.
- **Ball(3):** `q = PT(id n2, CR n3), PT(n2,n3), PT(id n1, CR n3)×2, PT(n1,n2)×2`.
- **Sphere(3):** as Ball(3) but F2 has the CR map too.
- **Ball(k), Sphere(k) for k = 4, 5:** CR on the **last** transversal axis for every face except the last-axis faces, which are periodic.

### 4.4 Ghost-index resolution `m[Val(K), i1..iN]` (QT:400-561)

```
bounds(i, n, K, a) = (K == 0 || K == a) ? (1 < i < n) : (0 < i ≤ n)
function resolve(m, K, idx):                 # N ∈ 2..5 ; N>5 → idx unchanged
    inb[a] = bounds(idx[a], s[a], K, a)  for a=1..N
    if ∃ unique a with !inb[a] and ∀ b≠a inb[b]:
        low  = idx[a] < 2
        f    = low ? 2a-1 : 2a
        slot = r[f];  if slot == 0: return idx          # open face: identity, possibly out of range
        pr   = p[slot];  a2 = ceil(pr/2)                 # target face and axis
        i    = idx[a]
        if low:  x = isodd(pr) ? |i-1| + 1              # target low face  → reflect about 1
                                 : s[a2] - |i-1|          # target high face → wrap: 1→n, 0→n-1
        else:    x = iseven(pr) ? s[a2] + s[a] - i        # target high face → reflect about n
                                 : i + 1 - s[a]           # target low face  → wrap: n→1, n+1→2
             # QUIRK Q11: for N==5 and a==5 Julia uses s[4] in place of s[a]
        t    = q[slot][ idx without axis a ]              # Values{N-1}
        return insert(t, at position a2, x)               # getlocate
    return idx                                            # interior, corner, or multi-axis ghost
```

- **1-D** (QT:403-416): interior `1<i<n` gives `i`. `i<2` uses face 1 and `i≥n` uses face 2, with the same formulas (target axis = 1).
- **Plain indexing** `m[i…]` is `K = 0`. **Corners and edges of the grid** (two or more axes out of bounds) are returned unchanged. This is why `collect(TorusTopology(4,5))` keeps its four corners.
- **Periodic self-inverse property:** under `K=0` the resolver *swaps* the representatives on the two faces. For the torus, `(1,j) ↦ (n1,j)` and `(n1,j) ↦ (1,j)`. It is not a projection onto a canonical representative; `elementfun` (next section) supplies canonicality.

**Goldens (✓J), Torus(4,5), K=0, rows i = 0..5, columns j = 0..6:**

```
(0,0)=>[0,0] (0,1)=>[0,1] (0,2)=>[3,2] (0,3)=>[3,3] (0,4)=>[3,4] (0,5)=>[0,5] (0,6)=>[0,6]
(1,0)=>[1,0] (1,1)=>[1,1] (1,2)=>[4,2] (1,3)=>[4,3] (1,4)=>[4,4] (1,5)=>[1,5] (1,6)=>[1,6]
(2,0)=>[2,4] (2,1)=>[2,5] (2,2)=>[2,2] (2,3)=>[2,3] (2,4)=>[2,4] (2,5)=>[2,1] (2,6)=>[2,2]
(3,0)=>[3,4] (3,1)=>[3,5] (3,2)=>[3,2] (3,3)=>[3,3] (3,4)=>[3,4] (3,5)=>[3,1] (3,6)=>[3,2]
(4,0)=>[4,0] (4,1)=>[4,1] (4,2)=>[1,2] (4,3)=>[1,3] (4,4)=>[1,4] (4,5)=>[4,5] (4,6)=>[4,6]
(5,0)=>[5,0] (5,1)=>[5,1] (5,2)=>[2,2] (5,3)=>[2,3] (5,4)=>[2,4] (5,5)=>[5,5] (5,6)=>[5,6]
```

Torus(4,5), K=1 / K=2 pairs:
- `(1,1)=>([4,1],[1,5])`
- `(4,5)=>([1,5],[4,1])`
- `(0,1)=>([3,1],[0,1])`
- `(1,0)=>([1,0],[1,4])`

Other topologies:
- **Mobius(4,5):** `(0,2)=>[3,4]`, `(1,2)=>[4,4]`, `(4,2)=>[1,4]`, `(5,2)=>[2,4]`.
- **Sphere(4,5):** `(0,2)=>[2,4]`, `(1,2)=>[1,4]`, `(1,3)=>[1,1]`, `(5,3)=>[3,1]`.
- **5-D Torus(3,4,5,6,7):** `[2,2,3,4,7]` gives `[2,2,3,4,2]`. This is Q11; the correct result is `[2,2,3,4,1]`.

All lookups for K ∈ 0..N and indices 0..n+1 are in the JSON (`quotient[*].ghosts`).

### 4.5 Slicing `m(i…, :, j…)` → `subtopology` (QT:563-752)

**One colon at axis A.** Here `vals` = the fixed coordinates and `R = (2A-1, 2A)`.

```
findface(ri) = (ri==0 || p[ri] ∉ R || q[ri][vals…] ≠ vals) ? 0 : (p[ri] ≠ R[1] ? 2 : 1)
p1, p2 = findface(r[R1]), findface(r[R2]); n = s[A]
p1=0,p2=0  → OpenTopology(n)
p1=0,p2≠0  → Q(p=(2,), r=(0,1), s=(n,), c=c[R])
p1≠0,p2=0  → MirrorTopology(n)                     # c reset to 0
else       → Q(p=(p1,p2), r=(1,2), s=(n,), c=c[R])
```

In words: a face gluing survives only if it glues axis A to itself **and** the transversal map fixes the slice's fixed coordinates. For example:
- `Sphere(4,5)(:,j)` is open for every j.
- `Sphere(4,5)(i,:)` is a 1-D torus.
- `Torus(4,5)(:,1)` is a 1-D torus.

**Two or three colons** (QT:621-698):
- Each of the 4 or 6 faces uses `findface(m,R,ri,vals, Val(excluded transversal axes)…)`. It compares `exclude(q[ri], excluded…)[vals…] == vals`, then returns the *position* of `p[ri]` within `R` (1..4 or 1..6).
- The new `p` is the list of nonzero positions.
- The new `q[k]` is the 1-D axis map of the other kept axis (`ProductTopology(q[r].v[position])`).
- The new `r` counts the nonzero positions cumulatively.
- The new `s` is the kept sizes; the new `c` is `c[R]`.

**Special cases:**
- An all-colon call returns `m`.
- An `OpenTopology` slice returns `OpenTopology(kept sizes)`.
- `subtopology(m, Val(A))` ignores the transversal maps: face k keeps `isodd(p) ? 1 : 2` when glued (QT:587-602).

Goldens: `quotient[*].slices` (all 1-colon slices of the 2-D cases plus `Val(1)`/`Val(2)`).

### 4.6 Node identification: `elementfuns` and `vertices` (GR:92-308)

`elementfun(l, m, idx) = min(getlinear(l, m, Val(0), idx), l[idx])`, where `l = LinearIndices(s)`.

**`getlinear` in 2-D (GR:164-198)**, with `isi = 1<i<n1` and `isj = 1<j<n2`:

```
if isj && !isi:
   if i<2:   slot=r[1]; if slot≠0 && isodd(p[slot]): return l[location_low(…, i, j)]   # else fall through
   else:     slot=r[2]; if slot≠0:                  return l[location_high(…, i, j)]
elif isi && !isj:
   if j<2:   slot=r[3]; if slot≠0 && isodd(p[slot]): return l[location_low(…, j, i)]
   else:     slot=r[4]; if slot≠0:                  return l[location_high(…, j, i)]
elif !isi && !isj:        # corner (always, since K=0)
   o1 = resolve(m, K=1, (i,j)); o2 = resolve(m, K=2, (i,j))
   return l[min(o1[1],o2[1]), min(o1[2],o2[2])]
return l[i,j]
```

**Other dimensions:**
- **1-D** (GR:163): returns the *tuple* `m[i]`, which causes **Q3** (Julia errors).
- **N ≥ 3:** the generic fallback returns `l[idx]`. **Only collapse flags act in 3-D and higher (Q6).**

**Collapse pass (GR:102-144).** Run it after the pointwise computation, sequentially for f = 1..2N:
- `c[2a-1] = 1` sets every point with `i_a = 1` to `1`.
- `c[2a] = 1` sets every point with `i_a = n_a` to the *current* value at the point with `i_a = n_a` and all other coordinates equal to 1.

**`vertices(elm)`** (compact renumbering, GR:300-308):

```
els = vec(elm)
dup = setdiff(1:len, els)                   # positions that are nobody's representative (ascending)
unq = unique(els)                           # representatives, first-appearance order
out = zeros(len); out[unq] = 1:length(unq)
rhs = [out[els[d]] for d in dup]            # read BEFORE writing (broadcast semantics)
out[dup] = rhs
reshape(out, size(elm))
```

**Other outputs:**
- `verticesinv(m) = unq` and `nodes = length(unq)`.
- `duplicatemap = dup .=> els[dup]`.
- `uniquemap = unq .=> 1:k`.
- For `OpenTopology`, `elementfuns` returns `LinearIndices` and `vertices` returns the same.

**Transitivity quirk (Q7).** Low faces identify only via a *mirror* (odd target). Periodic identification is found only from the high side, and `min` picks the smaller id. As a result, gluings with a non-identity transversal map (Mobius, Klein, Hopf flips) do **not** merge all equivalent points:
- **Mobius(4,5):** point (4,2) maps to (1,4) = 13, and `min(13,8) = 8`. But (1,4) itself stays 13, so nodes 8 and 13 remain distinct although they are the same point.
- Identity maps (Torus, Cylinder) are fully correct.
- **Recommendation:** implement `elementfunsJulia` (bit-exact, for goldens) and `elementfunsClosed`. The latter is a union-find closure over all face gluings plus collapses, with the representative = the minimum linear index. Use the closed version downstream and document the difference.

**Goldens (✓J), `elementfuns`:**

| Case | Result (rows) |
|---|---|
| Torus(4,5) | `[1 5 9 13 1; 2 6 10 14 2; 3 7 11 15 3; 1 5 9 13 1]` |
| Mobius(4,5) | `[1 5 9 13 1; 2 6 10 14 18; 3 7 11 15 19; 1 8 9 5 1]` |
| Sphere(4,5) | `[1 1 1 1 1; 2 6 10 14 2; 3 7 11 15 3; 4 4 4 4 4]` |
| Geographic(4,5) | `[1 5 9 13 17; 1 6 10 14 17; 2 7 11 15 18; 1 5 9 13 17]` |

**Goldens (✓J), `vertices`:**

| Case | Result (rows) |
|---|---|
| Torus(4,5) | `[1 4 7 10 1; 2 5 8 11 2; 3 6 9 12 3; 1 4 7 10 1]` |
| Mobius(4,5) | `[1 4 8 11 1; 2 5 9 12 14; 3 6 10 13 15; 1 7 8 4 1]` |
| Sphere(4,5) | `[1 1 1 1 1; 2 5 7 9 2; 3 6 8 10 3; 4 4 4 4 4]` |

### 4.7 Lagrange node numbering (LG:173-282)

Let:
- `np = totalnodes(corner mesh)`;
- `ne = #edges` (edges in colex order, §4.9);
- `nf = #facets` (tets; first-appearance order from `_facetsindices`);
- `es = M-1`;
- `fs = facetsimplex(4,M)`;
- `cs3 = centersimplex(3,M)` (triangle center count);
- `cs4 = centersimplex(4,M)`.

**Global node layout:**

```
corners          : 1 .. np
edge e, k-th     : np + es*(e-1) + k                          k = 1..es
facet f, k-th    : np + es*ne + fs*(f-1) + k                   (tets only)
cell  E, k-th    : np + es*ne [+ fs*nf] + cs*(E-1) + k
totalnodes       : np + es*ne + cs3*nt                  (triangles)
                   np + es*ne + fs*nf + cs4*nt          (tets)
```

**Triangle element node list** (`getlagrange3`, M ≥ 3; M=2 uses `getlagrange2`, M=1 the corners). Let `ti = (v1,v2,v3)` and `ei = (E1,E2,E3)`, where `Ek` is the edge **opposite vertex k**:
- local edge 1 runs `v2→v3`, local edge 2 runs `v3→v1`, local edge 3 runs `v1→v2` (a cyclic traversal);
- `σk = +1` if the traversal goes from lower id to higher id (`edgesigns`, EL:400), else −1.

```
nodes = [v1,v2,v3,
         for k in 1..3: np + es*(Ek-1) .+ (σk==1 ? (1..es) : (es..1)),
         np + es*ne + cs3*(i-1) .+ (1..cs3)]        # M==3: single np+2ne+i
```

This is **conforming**: shared edges produce identical physical node sequences.

**Quirk Q18d:** the center block uses the *subspace* element index `i`, not `getfacet(t,i)`. It is correct only for full meshes; for subsets it disagrees with `lagrangevertices3`.

Golden, tri8/grid meshes, `P3 tri (1,2,5)` with `np=6`, `ne=9`, `ei=(5,4,1)`, `σ=(+,−,+)`: `[1,2,5, 15,16, 14,13, 7,8, 25]`.

**P2** (`getlagrange2`): `[v1,v2,v3, np+E1, np+E2, np+E3]`, e.g. `[1,2,5,11,10,7]`.

**Tetrahedron element node list** (`getlagrange4`, used for M ≥ 3; M=2 is `[ti; np .+ ei]`):
- `ei` is the 6 edges in local **lexicographic** pair order `(12,13,14,23,24,34)` (EL:358-361).
- `fi` is the 4 facets, `fi[k]` = the facet opposite local vertex k (EL:123-137).

```
edge block  : for k in 1..es: for each local edge j in 1..6: np + es*ei[j] - (es-k)   # k-major, NO orientation sign
facet block : for k in 1..fs: for each local facet j in 1..4: np + es*ne + fs*fi[j] - (fs-k)   # k-major, no orientation
cell block  : np + es*ne + fs*nf + cs4*(i-1) .+ (1..cs4)       # M==4: single; M<4: empty
```

**Quirk Q18c:** tet edge and face nodes carry **no orientation correction**. Tets of degree ≥3 are conforming only if every element tuple is sorted ascending. A Lean `fixed` variant should apply orientation per edge (as for triangles) and per face (a rotation or reflection of the face-interior triangle lattice).

Golden, tet2 `(1,2,3,4),(2,3,4,5)`, M=3, `np=5`, `ne=9`: `[1,2,3,4, 6,8,12,10,14,16, 7,9,13,11,15,17, 27,26,25,24]`. M=4 and M=5 are in the JSON (`simplex.tet2.lagrange`).

**Subset vertex lists** (`lagrangevertices3`, used for `L[ks]`):

```
vcat(vertices(t), [np + es*e - (es-k) for k in 1..es for e in vertices(ei)], centerindex(subelements(t)…))
```

Here `vertices(ei)` is the list of edge ids in first-appearance order.

**Refinement** (`refinement(L)`, EL:413-455) replaces each P_M triangle by M² linear triangles, using these local tables (indices into the element node list):
- **M=1:** identity.
- **M=2 (6 nodes):** `(1,6,5),(2,4,6),(3,5,4),(4,5,6)`.
- **M=3 (10 nodes):** `(1,8,7),(2,4,9),(3,6,5),(8,9,10),(9,4,10),(4,5,10),(5,6,10),(6,7,10),(7,8,10)`.
- **M=4 (15 nodes):** `(1,10,9),(2,4,12),(3,7,6),(11,12,15),(12,4,15),(4,5,15),(5,6,14),(6,7,14),(7,8,14),(8,9,13),(9,10,13),(10,11,13),(11,15,13),(5,14,15),(8,13,14),(13,15,14)`.
- **M ≥ 5:** MethodError.
- **Tetrahedra:** M=1 only.

The result is `SimplexTopology(0, out, vertices(L), nodes(L))`.

### 4.8 Multilinear cells (GR:21-90) and triangle detection

**Cell vertex order** (`i1 = i+1` and so on):

| Dim | Order |
|---|---|
| 1-D | `(i),(i1)` |
| 2-D | `(i,j),(i1,j),(i1,j1),(i,j1)`, counter-clockwise |
| 3-D | bottom `(i,j,k),(i1,j,k),(i1,j1,k),(i,j1,k)`, then top with k1 in the same order |
| 4-D | the 3-D cube at `w`, then `(i,j1,k1,w1),(i1,j1,k1,w1),(i1,j,k1,w1),(i,j,k1,w1),(i,j1,k,w1),(i1,j1,k,w1),(i1,j,k,w1),(i,j,k,w1)` (a reversed snake) |
| 5-D | the 4-D pattern at `v`, then the same 16 at `v1` |

Cells are enumerated column-major over `i ∈ 1..s1-1, j ∈ …`. **Quirk Q5:** the 4-D version uses `s[3]` for the `w` range.

**`detect_tri`** (GR:232-264) runs on the column-major list of 2-D quads. It checks each quad in the order below; the first match removes the quad and records a triangle:

| Condition | Triangle |
|---|---|
| `q1==q2` | `(q2,q3,q4)` |
| else `q2==q3` | `(q1,q2,q4)` |
| else `q3==q4` | `(q1,q2,q3)` |
| else `q4==q1` | `(q1,q2,q3)` |

`iq` and `it` record the original cell ids. `elementsplit[cell] = 4=>quad_idx | 3=>tri_idx`.

Golden, Sphere(4,5):
- quads `[[2,3,7,6],[6,7,11,10],[10,11,15,14],[14,15,3,2]]`;
- tris `[[1,2,6],[3,4,7],[1,6,10],[7,4,11],[1,10,14],[11,4,15],[1,14,2],[15,4,3]]`;
- `iq=[2,5,8,11]`, `it=[1,3,4,6,7,9,10,12]`.

### 4.9 Simplex combinatorics (EL)

**`vertices(list)`:** distinct ids in first-appearance order. It returns `OneTo(n)` iff `max == #distinct`. Examples:
- `[(2,1),(1,3)]` gives `OneTo(3)`;
- `[(5,2),(2,7)]` gives `[5,2,7]`.

**`sparse(t)`:**

```
A = zeros(np,np)
for (a,b) in combo(N,2): for each element k: A[t_k[a], t_k[b]] += 1
```

Here `np = nodes(t)` and the columns are `reducedcolumns(t)`. For subsets these are renumbered local ids, which differs from `edges`/`incidence`, which use full ids.

**`adjacency = A + Aᵀ`, `antiadjacency = A − Aᵀ`.**

**`edges(t)`:**

```
adj = adjacency(t, columns(t), totalnodes(t))
edges = [(i,j) for (i,j) in findall(!=0, triu(adj))]   # column-major ⇒ sorted by (j, i): COLEX
```

- Diagonal entries from degenerate elements yield self-edges: `[(3,3,1)]` gives `[[1,3],[3,3]]`.
- Golden, tri8: `[1,2],[2,3],[1,4],[1,5],[2,5],[4,5],[2,6],[3,6],[5,6],[4,7],[4,8],[5,8],[7,8],[5,9],[6,9],[8,9]`.
- **Lean:** collect the canonical pairs `(min,max)`, dedupe, sort by `(max,min)`. Radix or counting sort by `max` is O(E).

**`edgesindices(t, et)`:**
- `A` is the symmetric map `(a,b) ↦ edge id`.
- Triangle: `(A[v2,v3], A[v1,v3], A[v1,v2])`, i.e. the edge opposite each vertex.
- Tet: `(A[v1,v2],A[v1,v3],A[v1,v4],A[v2,v3],A[v2,v4],A[v3,v4])`, lex; Values{5} is lex too.
- The result is a `SimplexTopology(0, ei, OneTo(ne), ne)`.
- **Q21:** the matrix is sized `nodes(t)` rather than `totalnodes`. It fails for non-contiguous ids and for subsets.

**`faces(t, Val(k))`** (1<k<N): for each element, the lex k-subsets of the **sorted** vertex tuple, deduplicated in first-appearance order. `k=1` gives `Values.(vertices)`, `k=2` gives `edges(t)` (colex), and `k=N` gives `t`.

**`faces(t, h, Val(k), g)`** (oriented incidence):

```
val = (k+1 == N) ? [(-1)^(N-j) for j in 1..N] : ones(binomial(N,k))
for each element e:
   (odd, s) = indexparity(t_e)
   for (idx, w) in enumerate(lex k-subsets of s):
       v = h[e] * (odd ? -val[idx] : val[idx])
       new w → push (w, g(v)) ; existing → bnd += g(v)
return (SimplexTopology(0, list, totalnodes), bnd)
```

- `facets(t, ones)` gives boundary coefficients (nonzero ⇒ boundary facet).
- Golden, tri2 `[(1,2,3),(2,4,3)]`: `([1,2],[1,3],[2,3],[2,4],[3,4])`, `[1,-1,0,1,-1]`.
- Golden, tet2: facets `[1,2,3],[1,2,4],[1,3,4],[2,3,4],[2,3,5],[2,4,5],[3,4,5]`, coefficients `[-1,1,-1,0,1,-1,1]`.

**`skeleton(t)`** = `[faces(t, ones, Val(k), abs) for k in 1..N+1]`. It gives incidence counts per face; the last entry is empty.

**`facetsinterior(t)`:** like `faces(Val(N-1))`, but also returns `bnd` = the indices j of facets seen again (interior facets). Golden tri8: `bnd = [2,3,7,5,10,9,11,14]`.

**`_facetsindices(t)`** (N ≥ 4). For element i, `c = combinations(t_i, N-1)` (positional lex). Combination j omits local vertex `N+1-j`, so `outi[i][N+1-j]` = the id of `sort(c[j])` (first-appearance numbering). It returns `(SimplexTopology(facets), SimplexTopology(outi, OneTo(nf), nf))`.
- Golden tet2: facets `[1,2,3],[1,2,4],[1,3,4],[2,3,4],[2,3,5],[2,4,5],[3,4,5]`, `fi = [[4,3,2,1],[7,6,5,4]]`.
- For N=3 it returns `(edges, edgesindices)`.

**`incidence(t)`:** `A[t_e[k], e] += 1`, with size `totalnodes × elements` (full ids, subspace element index).

**`degrees(t)`:** `b[v]` = number of elements containing v (length `totalnodes`). **`weights = 1 ./ degrees`**, giving `Inf` for unused nodes.

**`neighbors(t)`:**

```
elemsOf[v] = sorted list of subspace elements containing full vertex v   # from incidence
for element k with vertices (v1..vN):
   nbr[j] = first(setdiff(∩_{l≠j} elemsOf[v_l], {k})) or 0   # element across the facet opposite v_j
```

Golden tri8: `[4,2,0],[5,0,1],[0,4,0],[7,1,3],[8,6,2],[0,0,5],[0,8,4],[0,5,7]`.

**`facetsigns(t)`:** `[nbr < k ? 1 : -1 for nbr in neighbors(t)[k]]`. Boundary facets (0) always get +1.

**Local oriented facets `facets(::Values)`:**

| Input | Facets |
|---|---|
| `(a,b)` | `(b),(a)` |
| `(a,b,c)` | `(b,c),(c,a),(a,b)` |
| `(a,b,c,d)` | `(b,c,d),(d,c,a),(a,b,d),(c,b,a)` |

For 5 vertices the fifth facet has 5 entries (Q22).

**`edgesigns`:**
- 2 vertices: the scalar `i1<i2 ? 1 : -1`.
- 3 vertices: `(i2<i3, i3<i1, i1<i2)`.
- 4 or 5 vertices: lex pairs.

**Subsets:**
- `m[ks]` returns elements `f[ks]` with vertices = first-appearance order of those elements. It keeps `istotal` from the parent (**Q28**), sets `fullvertices = vertices(m)`, and computes `verticesinv`.
- `m(vs)` keeps the elements whose vertices all lie in `vs`, with `vertices = vs` as given.
- `subimmersion` renumbers through `verticesinv`: `(1,5,4),(4,5,8),(5,6,9)` becomes `(1,2,3),(3,2,4),(2,5,6)`.
- `complement(s)` returns the remaining elements of the full mesh.

**Discontinuous topologies:**
- `d[k] = (N(k'-1)+1 … N k')` with `k' = getfacet`.
- `discontinuousvertices` = the element id of each node.
- `interp(d, b) = view(b, discontinuousvertices(d))` scatters element-constant data onto discontinuous nodes.
- `edges(d::Discontinuous{3})` is per-element `(1,2),(2,3),(3,1)` in discontinuous ids.
- `discontinuousboundary(d, e)` maps each continuous boundary edge to the discontinuous node pair of the first element containing it. Golden: `[[1,2],[7,8]]` for tri4 edges `(1,2),(2,3)`.

---

## 5. Display / printing

The Lean `ToString`/`Repr` should reproduce the **prefix** exactly. Type-parameter suffixes are Julia-specific; use a stable short form.

**Simplex, Discontinuous and Lagrange summary** (MT:704-714):

```
"$(length(m))×$(N)$(iscover(m) ? "⊆" : "⊂")$(totalnodes(m)) $(TypeString)"
```

- For Lagrange types `N` is the nodes-per-element param (e.g. `4×10⊆28 LagrangeTriangles{3, 10, …}`).
- `text/plain` display is the summary plus `":"` followed by one element per line, ` [a, b, c]`.
- Examples (✓J):

  ```
  8×3⊆9 SimplexTopology{3, Base.OneTo{Int64}, Base.OneTo{Int64}, (true, true)}:
   [1, 2, 5]
   [1, 5, 4]
   ...
  3×3⊂9 SimplexTopology{3, Vector{Int64}, Vector{Int64}, (true, false)}:
  2×3⊂7 SimplexTopology{3, Vector{Int64}, Base.OneTo{Int64}, (false, true)}:     # non-contiguous ids
  8×3⊆24 DiscontinuousTopology{3, Vector{Int64}, SimplexTopology{3, …}}:
  4×6⊆15 LagrangeTriangles{2, 6, Base.OneTo{Int64}, Base.OneTo{Int64}, (true, true)}:
  2×35⊆55 LagrangeTetrahedra{4, 35, …}:
  ```

- `print(m)` (compact) uses Julia's vector printing: `Values{3, Int64}[[1, 2, 3], [2, 4, 3]]`.

**ProductTopology with range axes** (MT:139). `print` gives `"[1, 1]:[3, 4]"`, i.e. `Values(first.(v))` followed by `':'` and `Values(last.(v))`, where `Values` prints `[a, b]`.
- `Values(1,1):Values(1,2):Values(3,6)` prints `[1, 1]:[3, 5]` (the last element of `1:2:6` is 5).
- `text/plain` display is the default array: `"3×4 ProductTopology{2, Base.OneTo{Int64}}:"` plus a matrix of `[i, j]`.
- Docstring (MT:120-126) shows `11×11 ProductTopology{2, OneTo{Int64}}:`. Julia 1.13 prints `Base.OneTo{Int64}` instead.
- A non-range axis (CrossRange) falls back to the default array show: `5-element ProductTopology{1, CrossRange}:` followed by ` [3]` … on separate lines.

**QuotientTopology:**
- The default N-D array display with alias names: `4×5 CompactTopology{2, 1, 4, ProductTopology{1, Base.OneTo{Int64}}}:` when O==2N, `2×3 OpenTopology{2, 1, 4, Vector{Values{1, Int64}}}:` when O==0, otherwise `QuotientTopology{2, 1, 4, 2, …}`.
- Compact `print` is `Values{2, Int64}[[1, 1] [3, 2] [1, 3]; [2, 3] …]`.

**Other types:**
- CrossRange prints as a vector (`5-element CrossRange:`, then ` 3` and so on).
- **BilinearTopology cannot be displayed** (no `size` method; Q23).

---

## 6. Examples and goldens

The README and docs contain **no** executable examples beyond the docstrings. `test/runtests.jl` is trivial. All goldens were harvested from the oracle into `notes/meshtopology_oracle/meshtopology_goldens.json`.

A verbatim selection follows.

**Docstring examples:**
- `ProductTopology(11,11)` has summary `11×11 ProductTopology{2, Base.OneTo{Int64}}`.
- `ProductTopology(1:11,1:11)` has summary `11×11 ProductTopology{2, UnitRange{Int64}}`.

**CrossRange:**

```
CrossRange(1..12) =
 1:[1]  2:[1,2]  3:[2,1,2]  4:[2,1,2,3]  5:[3,4,1,2,3]  6:[3,4,1,2,3,4]  7:[4,5,6,1,2,3,4]
 8:[4,5,6,1,2,3,4,5]  9:[5,6,7,8,1,2,3,4,5]  10:[5,6,7,8,1,2,3,4,5,6]
 11:[6,7,8,9,10,1,2,3,4,5,6]  12:[6,7,8,9,10,1,2,3,4,5,6,7]
```

**`collect` (K=0):**

```
Cylinder(4,5):   [1,1] [4,2] [4,3] [4,4] [1,5] / [2,1] [2,2] [2,3] [2,4] [2,5] / [3,1] … [3,5] / [4,1] [1,2] [1,3] [1,4] [4,5]
Mobius(4,5):     [1,1] [4,4] [4,3] [4,2] [1,5] / [2,*] / [3,*] / [4,1] [1,4] [1,3] [1,2] [4,5]
Wing(4,5):       [1,1] [1,4] [1,3] [1,2] [1,5] / … / [4,1] [4,4] [4,3] [4,2] [4,5]
Hopf(4,5):       [1,1] [4,4] [4,1] [4,2] [1,5] / [2,5] [2,2] [2,3] [2,4] [2,1] / [3,5] … [3,1] / [4,1] [1,4] [1,1] [1,2] [4,5]
Cone(4,5):       [1,1] [1,4] [1,1] [1,2] [1,5] / [2,5] … [2,1] / [3,5] … [3,1] / [4,1] [4,2] [4,3] [4,4] [4,5]
Geographic(4,5): [1,1] [4,2] [4,3] [4,4] [1,5] / [1,1] [2,2] [2,3] [2,4] [1,5] / [2,1] [3,2] [3,3] [3,4] [2,5] / [4,1] [1,2] [1,3] [1,4] [4,5]
Sphere(3,4):     [1,1] [1,1] [1,2] [1,4] / [2,4] [2,2] [2,3] [2,1] / [3,1] [3,1] [3,2] [3,4]
```

**`elementfuns`** (column-major matrices, printed row-wise):

```
Klein(5,5):       [1 6 11 16 1; 2 7 12 17 2; 3 8 13 18 3; 4 9 14 19 4; 5 10 11 6 1]
Mobius(5,5):      [1 6 11 16 1; 2 7 12 17 22; 3 8 13 18 23; 4 9 14 19 24; 1 10 11 6 1]
Hopf(5,5):        [1 6 11 16 1; 2 7 12 17 2; 3 8 13 18 3; 4 9 14 19 4; 5 10 1 6 1]
Cone(5,7):        [1 6 11 1 6 11 1; 2 7 12 17 22 27 2; …; 5 10 15 20 25 30 5]
Wing(5,7):        [1 6 11 16 11 6 1; 2 7 …; 5 10 15 20 15 10 5]
Sphere(5,7):      [1 1 1 1 1 1 1; 2 7 12 17 22 27 2; 3 8 …; 4 9 …; 5 5 5 5 5 5 5]
Ball(3,4,5) 3-D:  every point with i=1, j=1 or j=n2 → 1; else own linear index (e.g. [:,:,1] = [1 1 1 1; 1 5 8 1; 1 6 9 1])
Torus(3,4,5) 3-D: identity LinearIndices (Q6)
```

**`linearelements`:**
- Torus(4,5): cells `[1,2,6,5] [5,6,10,9] [9,10,14,13] [13,14,2,1] / [2,3,7,6] … / [3,1,5,7] [7,5,9,11] [11,9,13,15] [15,13,1,3]`.
- 4-D first cell of Open(3,3,3,3): `[1,2,5,4,10,11,14,13,40,41,38,37,31,32,29,28]`.
- 5-D Open(2^5): `[1,2,4,3,5,6,8,7,15,16,14,13,11,12,10,9,17,18,20,19,21,22,24,23,31,32,30,29,27,28,26,25]`.

**Cross products (Q-tables):**

| Product | p | r | s | Notes |
|---|---|---|---|---|
| `Torus(4)×Torus(5)` | [2,1,4,3] | [1,2,3,4] | – | |
| `Torus(4)×Open(5)` | [2,1] | [1,2,0,0] | – | |
| `Mirror(4)×Torus(5)` | [1,4,3] | [1,0,2,3] | – | |
| `Torus(3,4)×5` | [2,1,4,3] | [1,2,3,4,0,0] | – | |
| `5×Torus(3,4)` | [2,1,4,3] **(Q12, should be [4,3,6,5])** | [0,0,1,2,3,4] | [5,3,4] | |
| `cross_sphere(Torus4,Torus5)` | [1,2,4,3] | – | – | q=(CR5,CR5,id4,id4), c=[1,1,0,0] |
| `cross_sector(Torus4,Torus5)` | – | – | – | as cross_sphere but q2=id5, c=[1,0,0,0] |

**Simplex:** tri8 (§4.9), plus `grid4x3`, `tri4`, `noncontig`, `tet2`, `tet5cube` and `edge3` in JSON `simplex`, each with ~30 derived quantities.

Selected tri8 values:

```
edgesindices = [5,4,1] [6,3,4] [8,7,2] [9,5,7] [12,11,6] [13,10,11] [15,14,9] [16,12,14]
degrees      = [2,3,1,3,6,3,1,3,2]
facetsigns   = [-1,-1,1] [-1,1,1] [1,-1,1] [-1,1,1] [-1,-1,1] [1,1,1] [1,-1,1] [1,1,1]
facets(t,1s) = edges [[1,2],[1,5],[2,5],[1,4],[4,5],[2,3],[2,6],[3,6],[5,6],[4,8],[5,8],[4,7],[7,8],[5,9],[6,9],[8,9]]
               coeffs [1,0,0,-1,0,1,0,1,0,0,0,-1,-1,0,1,-1]
t[[2,5,7]]: vertices [1,5,4,8,6,9]; verticesinv [1,0,0,3,2,5,0,4,6]; subimmersion [1,2,3],[3,2,4],[2,5,6]; summary "3×3⊂9"
discontinuous(t): vertices [1,2,5,1,5,4,2,3,6,…]; dverts [1,1,1,2,2,2,…]; summary "8×3⊆24"
```

---

## 7. Dependencies on other chakravala packages (and others)

| Package | Symbols used | Where |
|---|---|---|
| **StaticVectors** | `Values{N,T}` (static immutable tuple), `countvalues(a,b)` (`Values(a:b...)`), `Variables{N,T}` (mutable static vector, used in `faces(t,h,…)`), `zeros(Values{N,Int})`, `SOneTo` (axes) | everywhere; EL:146 |
| **AbstractTensors** | `value` (re-exported; `value(t)` of an array returns it; `value(Chain)` gives coefficients), `mdims` (extended), `complement` (extended) | MT:26, 343; EL:24, 147, 188 |
| **Grassmann** (NOT imported; B(Q1)) | `Grassmann.binomial` (= `Base.binomial`), `Grassmann.combo(n,g)` (lex g-subsets of 1:n), `Submanifold(M)(I)` (pseudoscalar), `∂` (boundary), `value` | LG:21; EL:53, 147; QT:382, 389 |
| **Leibniz** (via Grassmann, NOT imported) | `Leibniz.combinations` (= `Combinatorics.combinations`), `Leibniz.indexparity!` | EL:90, 109, 127, 152-153 |
| **Cartan** (reverse dependency; not imported) | `ProductSpace`, `PointArray`, `⊕`, `fibertype`, `fiber`, `means`, `Manifold` | QT:88-134; EL:25, 312-317, 334 |
| stdlib | `SparseArrays` (`sparse`, `spzeros`, `SparseMatrixCSC`), `LinearAlgebra` (`cross`, `triu`, `Diagonal`, `I`), `Base.Threads` (`@threads` in `neighbors`) | |

**Consequence for the port:**
- MeshTopology-Lean needs only a small **Combinatorics** module: `binomial`, `combo`, `combinations`, `indexParity`, and the boundary sign `(-1)^(M-j)`. Share it with the Leibniz port if one exists.
- It needs a tiny **sparse builder** (COO with duplicate summation → CSC, `transpose`, `findall(!=0, triu(·))`), or hash-map-based replacements.
- It must **not** depend on the Grassmann multivector algebra; `∂(pseudoscalar)` is just a sign pattern.

---

## 8. Lean 4 porting notes

### 8.1 Type indices vs runtime values

| Julia param | Role | Lean |
|---|---|---|
| `N` in `ImmersedTopology{N,M}` / `SimplexTopology{N}` | vertices per element | **type index**; element access returns `Vector Nat N` (or `Fin`-indexed getters over a flat array) |
| `N` in `QuotientTopology{N}` / `ProductTopology{N}` | grid dimension | **type index** |
| `L`, `M` (Quotient) | `N-1`, `2N` | derived, not stored |
| `O` (Quotient) | #glued faces | runtime |
| `LA`, `S`, `P`, `F` (container types: OneTo vs Vector vs StepRange vs CrossRange) | fast paths | runtime sum types `IdxVec` / `AxisMap` |
| `T = (istotal, isfull)` | subspace flags | runtime `Bool`s |
| `M` in Lagrange (degree) | node counts | **type index**; `N_nodes = lagrangeSimplex d M` computed |
| `K` in `m[Val(K), …]` | stencil axis | runtime `Nat` argument marked `@[specialize]`/`@[inline]`, or separate functions per K via a `Fin (N+1)` argument |

**Zero-cost dependent-typing wins:**
- **`Fin totalNodes` connectivity.** Use `structure Mesh (N) where nodes : Nat; conn : Array (Fin nodes)` with `conn.size = N * ne`. Validate once in the constructor (O(n)); then every gather `pts[conn[k]]` with `pts : Vector P nodes` is bounds-check-free. `Fin n` is erased to `Nat` at runtime.
- **Faces as `Fin (2*N)` and axes as `Fin N`.** This removes the `_to_axis` arithmetic errors and the Q11-type bug class; `face.axis : Fin N` is a definitional projection.
- **`Vector Nat N` for grid sizes and multi-indices** in the API. For hot paths, see 8.2.

**Keep as runtime + theorems:**
- Lagrange per-element node counts. Proving `3 + 3(M-1) + binom(M-1,2) = binom(M+2,2)` definitionally is awkward. Produce `Array Nat` and prove `size = lagrangeSimplex 3 M` as a theorem (by `omega` after unfolding a closed form `(M+1)(M+2)/2`), or return `Vector` via `cast` with that theorem.

### 8.2 Performance: how Julia gets its speed, and the Lean equivalent

- **`Values` is an isbits stack tuple.** `Vector{Values{N,Int}}` is a flat buffer. Lean `Vector Nat N` is a heap `Array`, so returning one per lookup allocates.
  - Store connectivity **flat** (`Array Nat`, stride N; or `ByteArray`-packed UInt32 if memory matters).
  - Expose `@[inline] def elemVertex (t) (e : Nat) (k : Fin N) : Nat`.
  - Offer `Vector`-returning getters only for non-hot APIs.
- **`@generated` functions** (`edgesindex`, `centerindex`, `facetsindex`, `neighbors`, `resize`, `exclude`, `getindex(ProductTopology)`) unroll over compile-time N or M. In Lean, use plain loops over `Fin N` with `@[specialize]` on functions taking N and M as explicit arguments. For N ≤ 5 the compiler unrolls enough; correctness does not depend on unrolling.
- **Ghost resolver hot path.** Cartan stencils call `immersion(g)[Val(K), i…]` once per point, per axis, per derivative.
  - Provide `resolveLinear : QuotientTopology N → (K : Nat) → (idx : Vector Int N) → Nat`, which returns a scalar linear index with no allocation.
  - Better, precompute a **`NeighborTable`**: for each axis a and each point, the linear ids of the ±1 neighbors under `Val(a)`, as `Array UInt32` of size `2N·∏s`. Julia recomputes the branches per call; a table turns every stencil into a gather. Build it once per grid: the default 2-D 61×61 grid needs 2·2·3721 ≈ 14.9k entries, and the 3-D Hopf default (7,60,61) needs about 154k. Wider stencils (±2) can compose two table lookups, since the ghost resolver only ever handles one layer.
- **`elementfuns`/`vertices`** are one-shot O(∏s). The only non-linear part is `setdiff`/`unique`; use a `Array Nat` marker of size ∏s instead of hashing.
- **`edges`/`edgesindices`/`neighbors`** use sparse matrices in Julia, which is O(E log E) with allocation.
  - `edges`: canonical pairs, then sort by `(hi, lo)` (bucket by `hi`: O(E)).
  - `edgesindices`: `HashMap (Nat×Nat) Nat`, or CSR row lookup since pairs are bucketed by `hi`.
  - `neighbors`: node→element CSR (`incidence` transposed), then per facet intersect short sorted lists. Julia uses `@threads`; Lean can use `Task.spawn` chunks, optionally.
- **`faces`/`facets` (N ≥ 3)** use `findfirst` on a growing vector, which is **O(F²)** in Julia. Use a `HashMap (Vector Nat k) Nat` for first-appearance ids. Order must stay first-appearance for golden parity.
- **`detect_tri`** uses `deleteat!` in a loop (O(Q²)). Do a single pass that partitions into two arrays while preserving order; the results are identical.

### 8.3 What is Julia-specific: skip or redesign

- **`top_id`** (a global mutable counter) and **`bundle` ids.** They are cache keys for Cartan's global array caches. In Lean, take `id : Nat` as an explicit constructor argument (default 0). If needed, provide `IO.Ref`-based `freshId`. Goldens must not compare `bundle`.
- **`p::RefValue{Int}`** shares a mutable node count among views (so in-place mesh refinement updates all views), together with `totalnodes!` and `refine` (OneTo → Vector materialization for mutation). Lean is immutable: store `totalNodes : Nat`. Make `refine` the identity, or a "materialize" that converts `IdxVec.range` to `.arr`.
- **`view` vs `collect`** (`topology` returns a view when not full). Lean returns a lazy `IdxVec`-indexed accessor.
- **`@pure`, `IndexStyle`, `_ind2sub`, `iterate`** plumbing. Provide `ForIn` instances and column-major `linearIndex`/`cartesianIndex` helpers.
- **`immersion` as a type alias used as a function.** Skip; Cartan-Lean defines `immersion` on bundles.
- **Display type strings.** Emit a short form such as `SimplexTopology{3}`, and compare only the prefix in tests.
- **`XParameter`** functions, `VectorTopology` (commented out), `mycollect*`, `assembleincidence` and `pretni`: these need Cartan fiber types. Move them to the Cartan port.
- **Ambiguity errors** (Q2, Q15, Q20) are Julia dispatch artifacts. Implement the intended semantics.

### 8.4 Tricky semantics to get exactly right

1. **Closed periodic grids.** Index 0 wraps to `n-1`, and `1 ↔ n` swap under K=0.
2. **The upper-face formulas use the source axis size for the offset and the target axis size for the reflection base.** `s[a2] + s[a] - i` and `i + 1 - s[a]` differ when the target axis ≠ the source axis (for example `5×Torus` after the Q12 fix, or cross-axis gluings).
3. **The K parameter changes which axes count as in-bounds** (strict for axis K and for K=0, inclusive for the others). Only single-axis violations are resolved.
4. **The `elementfuns` min-rule** (low faces identify only via mirrors) and the sequential collapse overrides; see §4.6.
5. **`vertices(elm)` renumbering order is first appearance in column-major order of the *elementfun values*.** It is not sorted.
6. **Edges are colex-sorted; faces and facets are first-appearance** (sorted tuples); `_facetsindices` uses **positional** combinations of the *unsorted* tuple, so the opposite-vertex slot is `N+1-j`.
7. **Triangle local edges are opposite-vertex, tet local edges are lex pairs.** Triangle Lagrange edges are orientation-corrected; tet ones are not.
8. **`istotal` of a subset is inherited from the parent, not recomputed.** `iscover` for subsets is therefore false only because `isfull` is false.
9. **`sparse`/`adjacency`** use renumbered (`reducedcolumns`) ids and `nodes(t)` size, while `edges`, `incidence`, `degrees` and `neighbors` use full ids and `totalnodes`. They differ on subsets (golden in `t14` run: `adjacency(t[[2,4]])` is 5×5, `edges(t[[2,4]])` uses full ids).
10. **`weights` produce `Inf`** for unused node ids (non-contiguous meshes). The JSON stores the string `"Inf"`.
11. **Degenerate simplices** (repeated vertex) produce self-edges `[v,v]` in `edges`.

### 8.5 Suggested Lean module decomposition

| Module | Contents | ~LOC |
|---|---|---|
| `MeshTopology/Combinatorics.lean` | `binomial`, `simplexNumber`, `lagrangeSimplex`, `centerSimplex`, `facetSimplex`, `combo` (lex subsets), positional `combinations`, `indexParity`, `boundarySign`; lemmas (closed forms, `centerSimplex N M = binom (M-1) (N-1)`) | 150 |
| `MeshTopology/IdxVec.lean` | `IdxVec` (range/arr), `AxisMap` (oneTo/rev/stepFwd/cross/explicit, `get`, `size`, `resize`), `CrossRange`, `crossRange`; theorems: `cross_cross` involution for odd n on 2..n-1, range lemmas | 150 |
| `MeshTopology/Product.lean` | `ProductTopology N`, get (Cartesian/linear), resize/resample/exclude/cross, colon ctor, show | 180 |
| `MeshTopology/Quotient/Core.lean` | `Glue`, `QuotientTopology N` (normalized faces), `toTable`/`ofTable` (Julia p,q,r), `bounds`, `resolve` (generic N; plus `resolveJulia5` flag for Q11), `resolveLinear`, `NeighborTable` | 350 |
| `MeshTopology/Quotient/Named.lean` | Open, Cylinder, Mobius, Wing, Mirror, Clamped, Torus, Hopf, Klein, Cone, Tube, Ball/Polar, Sphere, Geographic for N=1..5; defaults | 250 |
| `MeshTopology/Quotient/Ops.lean` | `cross` family (+cross_sphere/sector), `subtopology`/slicing (k colons), resize, resample (intended semantics) | 350 |
| `MeshTopology/Grid.lean` | `elementfunsJulia`, `elementfunsClosed` (union-find), collapse, `vertices` renumber, `duplicates`/maps, `linearElements` N=1..5 (Julia vertex order) | 300 |
| `MeshTopology/Bilinear.lean` | `BilinearTopology`, `detectTri`, `elementSplit` | 120 |
| `MeshTopology/Simplex.lean` | `SimplexTopology N` (flat conn), constructors, accessors, `getImage`/`getFacet`, subsets `sub`/`byVertices`, `subImmersion`, `fullImmersion`, `complement`, `verticesInv` | 380 |
| `MeshTopology/Discontinuous.lean` | `DiscontinuousTopology N`, `disconnect`, `continuous`, `discontinuousVertices`, `interp`, boundary map | 160 |
| `MeshTopology/Sparse.lean` | COO→CSC with dup-sum, transpose, dense export (tests), triu findall | 150 |
| `MeshTopology/Element.lean` | `columns`, `sparse`/`adjacency`/`antiadjacency`, `incidence`, `edges` (colex), `edgesIndices`, `faces` (plain/oriented), `facetsInterior`, `facetsIndices`, `skeleton`, `neighbors`, `facetSigns`, `edgeSigns`, local `facets`, `degrees`, `weights`, `interior`, `assembleLocal` | 500 |
| `MeshTopology/Lagrange.lean` | `LagrangeEdges`/`Triangles`/`Tetrahedra` M, node maps (`edgesIndex` signed/unsigned, `facetsIndex`, `centerIndex`), element getters, subset vertex lists, totals, `refinement` tables (M ≤ 4 tri, plus a generic M-lattice refinement as an extension) | 450 |
| `MeshTopology/Show.lean` | summaries (`8×3⊆9 …`), ProductTopology range show | 80 |
| `MeshTopology/Proofs.lean` | see 8.7 | 300 |
| `Tests/MeshTopologyGolden.lean` | JSON loader and comparators for `meshtopology_goldens.json` | 250 |
| **Total** | | **≈ 4100** |

### 8.6 Bug and quirk register (Q-list)

All entries were verified by running the oracle (✓J). The last column says what the Lean port should do: **F** = implement the fix (goldens record a Julia error or mismatch), **R** = replicate for parity (optionally with a fixed variant), **D** = document only.

| Id | Location | Behaviour | Port |
|---|---|---|---|
| Q1 | LG:21; EL:53, 90, 109, 127, 147, 152; QT:382, 389 | `Grassmann`, `Leibniz`, `Submanifold` and `∂` are not imported, so all Lagrange constructors, `edges`/`adjacency` for N≥3, `faces`, `facets`, `skeleton`, `facetsinterior`, `_facetsindices` and compact `resample` throw UndefVarError, even with Cartan loaded | F |
| Q2 | QT:185-186 | `iscompact(::CompactTopology)` is a MethodError (ambiguous) | F: `O==2N` |
| Q3 | GR:163 | 1-D non-open `elementfuns` compares `Values` with `Int` (MethodError). Intended: `l[m[i][1]]`, then min | F |
| Q4 | GR:52 | `linearelements(::AbstractVector)` broadcasts wrongly (MethodError). Intended: `[(l[i], l[i+1]) for i in 1..n-1]` | F |
| Q5 | GR:55 | 4-D `linearelements` uses `s[3]-1` for the w range | F (goldens only for s3==s4) |
| Q6 | GR:162 | `getlinear` is the identity for N≥3, so 3-D+ quotients merge nothing except collapses | R (`elementfunsJulia`) + provide a closed variant |
| Q7 | GR:171-190 | the min-rule makes Mobius, Klein and Hopf identification non-transitive (duplicate nodes remain) | R + closed variant |
| Q8 | QT:174, 176 | `BallTopology()` and `SphereTopology()` return TubeTopology | D (probably intended Ball(20,61), Sphere(31,61)) |
| Q9 | QT:79 | `BallTopology(Values{5})` has the typo `PRoductTopology` | F |
| Q10 | QT:82-84 vs 81 | Sphere(3..5) has no collapse flags while Sphere(2) does | D, replicate |
| Q11 | QT:557 | 5-D upper face of axis 5 uses `n4` | R behind a flag (default fixed) |
| Q12 | QT:214-221 | `Int × Q` does not shift `p` by 2 (targets the wrong faces) | F |
| Q13 | QT:223-283 | `Q{a}×Q{b}` rebuilds `q` as identity (flips and CrossRange lost) and resets `c` | R (documented semantics of product) |
| Q14 | QT:391 | general-O `resample` indexes `perms[t[(j+1)÷2]]`: BoundsError for Tube, wrong for Cone. Intended `perms[axis(t[j])]` | F |
| Q15 | MT:45 vs 156 | `resample(::ProductTopology{1}, (i,))` is ambiguous, so 2-D compact `resample` fails even with Q1 patched | F |
| Q16 | QT:369 | `resize(Q)` compares slot values `r[j]` against `r[2N-1..2N]` and indexes `r` by slot (mixes slot and face). Wrong for Tube (resizes q of faces 3/4) | F: resize `q[slot]` iff the face of `slot` is not on axis N |
| Q17 | MT:506-515 | `DiscontinuousTopology(id,m,I)` for non-full `m` gets `i = nothing` (the else-branch value is a `for` loop), so all discontinuous subsets crash | F |
| Q18a | LG:344, 351, 365 | typos `_getelemeent`, `getelment3` | F |
| Q18b | LG:371-402 | `subimmersion` has no `where M`; Tetrahedra builds `LagrangeTriangles` | F |
| Q18c | LG:192-212, 268-273 | tet edge and face nodes have no orientation handling (nonconforming unless tuples are sorted) | R + fixed variant |
| Q18d | LG:266, 272 | center nodes use the subspace index `i`, not `getfacet(t,i)` | F (goldens exist only for the full mesh; the subset golden records Julia's value) |
| Q18e | LG:146-147 | LagrangeTetrahedra `vertices`/`fullvertices` use the triangle count (25 vs 30 for M=3) | F |
| Q18f | LG:153-162 | `LagrangeEdges` is broken (edgesindices is a Vector; M≥2 getindex fails) | F: `nodes = [a,b, np+(M-1)(e-1)+1..]` |
| Q19 | EL:339 | `interior(e)` passes its arguments reversed (MethodError). Intended `interior(e) = setdiff(1:totalnodes(e), vertices(e))` | F |
| Q20 | EL:301-302, 329-333 | `degrees(t,B) = B*ones(totalnodes)` is dimensionally wrong (intended `B*ones(elements)`); `interp(t,B)` and `pretni` are ambiguous | F |
| Q21 | EL:345 | `edgesindices` sizes the lookup matrix `nodes(t)`, failing on non-contiguous ids and subsets | F (use `totalnodes`) |
| Q22 | EL:407 | `facets(::Values{5})` fifth facet has 5 vertices | F: `(i4,i3,i2,i1)` pattern; document |
| Q23 | GR:204 | `BilinearTopology` has no `size` (cannot display or iterate) | F (size = #cells) |
| Q24 | MT:67; EL:15-18 | exported but undefined names | skip (Cartan) |
| Q25 | QT:595-618 | `subtopology` with p1≠0, p2=0 returns `MirrorTopology(n)` (drops `c`); p1=0, p2≠0 hard-codes `p=(2,)` | R |
| Q26 | QT:95, 111 | `WingParameter` recurses infinitely; `HopfParameter(Values{2})` reads `n[3]` | Cartan port |
| Q27 | EL:397 | boundary facets get sign +1 | R |
| Q28 | MT:404 | subsets inherit `istotal` from the parent | R |
| Q29 | QT:47, 129-135 | `QuotientTopology(::ProductTopology)` and `X(::Values{N,<:AbstractVector})` route to Cartan's `ProductSpace` (UndefVarError in MT) | F: accept ProductTopology sizes |
| Q30 | MT:40 | `resample(::StepRangeLen)` computes the step as `step*(len-1)/(i-1)`; fine | D |

### 8.7 Proofs that aid velocity (and make the port stand out)

All of these are cheap, mostly `omega`, `decide` or `simp`, and each guards a real bug class above.

1. **Ghost resolver is in-range.** For `n ≥ 2` and `i ∈ {0,1}` the low formulas give `1 ≤ x ≤ n`; similarly for `i ∈ {n, n+1}`. Hence `resolve` returns in-bounds indices whenever exactly one axis is out of range by at most 1 (`omega`). This catches Q11-class typos at compile time if resolve is written generically over `Fin N`.
2. **Periodic involution.** For torus faces, `resolve(resolve(x)) = x` on face points; for CrossRange with odd n, `cr(cr(i)) ≡ i (mod n-1)` (`decide` for small n; `omega` generally).
3. **`vertices` renumbering is a surjection onto `1..nodes`** and constant on elementfun classes.
4. **`edges` is strictly colex-sorted and duplicate-free**, and every local pair of every element appears. `edgesIndices` is correct: `edges[ei[e][k]] = sortPair(opposite edge)`.
5. **Lagrange index bounds.** Every node id is ≤ totalNodes. Triangle **conformity theorem:** for two elements sharing edge {a,b}, their edge-node sequences on that edge coincide as sets and are reverses as sequences exactly when their traversal orientations differ. This is a standout guarantee that Julia lacks for tets (Q18c).
6. **Discontinuous `getindex` is a bijection** `Fin ne × Fin N ≃ Fin (N*ne)`.
7. **`lagrangeSimplex` closed forms** and `3 + 3(M-1) + centerSimplex 3 M = lagrangeSimplex 3 M` (M ≥ 1). These make `Vector Nat (lagrangeSimplex 3 M)` element getters typecheck without runtime casts.

---

## 9. Oracle test plan

### 9.1 Harness

Upstream cannot run the interesting paths (Q1). Also, injecting a `const Grassmann` binding at runtime does **not** work: generated-function generators run in their defining world age (Julia ≥1.12), so the late binding stays invisible (✓J).

The working approach is `notes/meshtopology_oracle/patched.jl`. It copies `src/` to `mtsrc/`, inserts `import Grassmann; import Grassmann: Leibniz, Submanifold, ∂` after `import AbstractTensors`, and `include`s it as a fresh top-level module `Main.MeshTopology`:

```julia
import Grassmann
let f = joinpath(@__DIR__, "mtsrc", "MeshTopology.jl")
    src = read(f, String)
    occursin("import Grassmann\n", src) || write(f, replace(src,
        "import AbstractTensors\n" => "import AbstractTensors\nimport Grassmann\nimport Grassmann: Leibniz, Submanifold, ∂\n"; count=1))
    include(f)
end
using .MeshTopology; const MT = MeshTopology
```

Run it with:

```
julia --startup-file=no --project=<scratchpad>/juliaenv notes/meshtopology_oracle/dump_goldens.jl
```

It takes about 27 s. Wrap every call in `try`; errors are recorded as `{"error": "…"}` so that Julia-broken cases become explicit "expected error / fixed in Lean" goldens.

**JSON conventions** (`J` in the script):
- `Values` and tuples become arrays.
- N-D arrays become `{"dims":[…], "colmajor":[…]}`.
- `Pair`s become `[a, b]`.
- `Inf` becomes the string `"Inf"`.
- Sparse matrices are densified.
- Ghost grids cover indices `0..n+1` per axis in column-major order: `{"K", "lo":0, "dims", "colmajor"}`.

### 9.2 What is dumped now (`meshtopology_goldens.json`)

| Key | Content | Inputs |
|---|---|---|
| `crossrange` | `collect(CrossRange(n))` | n = 1..12 |
| `producttopology` | show strings, collect, linear index, resize, exclude, reversed axis | small fixed |
| `numbers` | simplexnumber (N 0..4, n 0..6), lagrangesimplex, centersimplex, facetsimplex (N 2..4, M 1..6) | exhaustive small |
| `quotient[]` (110 cases) | per case: `table{p,q,r,s,c}`, `O`, `isopen`, `iscompact`, `collect`, `ghosts` (K=0..N, all indices 0..n+1; N ≤ 3), `elementfuns`, `vertices`, `verticesinv`, `duplicatemap`, `uniquemap`, `linearelements`, and for 2-D `bilinear{q,t,iq,it,split,v,i,nodes}`, `slices{axis1[j], axis2[i], val1, val2}`, `resize7` | 14 2-D families × sizes {(3,3),(4,5),(5,7),(6,4),(7,7)}; 6 1-D families × n ∈ {4,5,7}; 8 3-D families × {(3,4,5),(4,4,5)}; 5 4-D families (3,4,5,4) with 11 sample lookups; 5-D Torus with 7 samples (documents Q11) |
| `cross` | 13 product tables (Open, Torus, Mirror, Int, Mobius; cross_sphere, cross_sector) | fixed |
| `simplex{tri8,tri4,grid4x3,noncontig,tet2,tet5cube,edge3}` | summary prefix, vertices, verticesinv, totals, flags, columns, incidence, sparse, adjacency, antiadjacency, edges, edgesindices, neighbors, facetsigns, degrees, weights, facets, facets_h, facetsinterior, facetsindices, faces1, skeleton, edgesigns, localfacets, discontinuous{elements, vertices, dverts, totalnodes}, subset (3 elements: vertices, verticesinv, fullvertices, subtopology, subimmersion, complement, summary), byvertices (vertex-induced), lagrange M=1..5 (tri: elements, totals, refinement; tet: elements, totals, vertices_len), lagrange_subset3 | hand-picked meshes: structured tri grid, non-contiguous ids, 2-tet, 5-tet cube (Kuhn-like), edge chain |

### 9.3 Further dumps to add (recommended distributions)

1. **Random quotient lookups.** For every family and N ∈ {2,3}, random sizes `n_a ∈ 3..9` (include even and odd for CrossRange), random K ∈ 0..N, and random indices in `0..n+1`, 1000 per family. Compare `resolve` exactly.
2. **Relabelled simplex meshes.** Take `gridtris(nx,ny)` for nx, ny ∈ 3..8, apply a random vertex permutation *and* a random per-element rotation or reflection of vertex order, and randomly drop 10% of the elements to make ids non-contiguous.
   - Dump `edges`, `edgesindices`, `neighbors`, `facetsigns`, `facets_h`, `_facetsindices` and `LagrangeTriangles{2,3,4}` elements.
   - This stresses colex ordering, opposite-edge conventions and orientation signs.
   - For tets, use the 5- and 6-tet cube splits on 2×2×2 blocks with random relabelings. Keep the M=3,4 conformity check as a *Lean-side* property test, since Julia fails it (Q18c).
3. **Subset families.** For each mesh, random element subsets and random vertex subsets. Check `t[ks]` and `t(vs)` (vertices, verticesinv, subimmersion, complement), plus the `iscover`/summary prefix.
4. **Lagrange totals** for random meshes: `totalnodes` = corners + (M-1)·E + cs·T (triangles) and the tet formula. Check `max(element node ids) == totalnodes` for full meshes (it holds for tri; for tets it holds only for the facet and center formula, since Q18e affects only `vertices`).
5. **`elementfunsClosed` (Lean-only) vs Julia.** For identity-map topologies (Torus, Cylinder, Clamped, Mirror, Tube, Open, Sphere, Ball, Cone, Geographic), assert that the Lean closed variant equals Julia's output exactly. For Mobius, Klein and Hopf, assert that Julia's is a refinement of Lean's (every Julia class ⊆ a Lean class).
6. **Display strings.** The summary prefix for Simplex, Discontinuous and Lagrange (full and subset), and `sprint(show, ProductTopology(ranges…))`.

### 9.4 Comparison rules

- **Exact integer equality** for everything except `weights`: compare Float64 with `==` (they are exact reciprocals); `"Inf"` equals the Lean `Float.inf`.
- **Julia-error cases** (Q-list F items) are asserted as "Julia errors, Lean returns intended value". Store the Lean intended values in a separate hand-verified file, so that the harness never silently accepts divergence.
- **Never compare `bundle`/`top_id`.** It depends on the order of global side effects.
