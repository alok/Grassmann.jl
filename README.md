# Grassmann.lean

A Lean 4 port and interactive 3D Geometric Algebra platform built on [Michael Reed](https://github.com/chakravala)'s ⟨Grassmann-Clifford-Hodge⟩ differential geometric algebra ecosystem ([Grassmann.jl](https://github.com/chakravala/Grassmann.jl) — `DirectSum`, `Leibniz`, `AbstractTensors`, `StaticVectors`, `Cartan`, `MeshTopology`, `Adapode`, `Fatou`, `UnitSystems`, `Similitude`, and more), paired with a pure-Lean interactive **Geometric Algebra Studio** inspired by [Steven De Keninck](https://github.com/enkimute)'s [ganja.js](https://github.com/enkimute/ganja.js) CoffeeShop and Wedge game.

- **Live Web Studio**: **[https://grassmann-studio.vercel.app](https://grassmann-studio.vercel.app)** (WebGL2 + WebXR, dedicated Web Worker Lean-compiled WASM, zero server required)
- **Toolchain**: `leanprover/lean4:v4.36.0` (zero external Lean dependencies in the root package)

---

## Architecture — *"It's All in Lean"*

1. **Core Geometric Algebra Engine (`DirectSum/`, `Grassmann/`, `Cartan/`, `MeshTopology/`, …)**:
   - Spaces are values (`ℝ^3`, `S!"-+++"`, `D!"0,1,1,1"`, `S!"∞∅+++"`); elements are indexed by space and grade/parity (`Chain V 2 Float`, `Spinor V Float`, `Multivector V Rat`).
   - Elaboration-time unrolled kernels (`Grassmann.Kernel.Generated.{R2,R3,R4,STA,PGA2,PGA3,CGA2,CGA3}`) run on unboxed `FloatArray`s at C/Julia speed (`interpreteCGA3 circle` **70.6 ns**, `motorSlerp` **56 ns**, 960-tri `sliceMeshByPlane` **52.4 µs**, `ALOK-1007` linearity guard in [`scripts/check_packed_linearity.py`](scripts/check_packed_linearity.py); see [`docs/PERF.md`](docs/PERF.md)).
   - **Strictly `Init`-only runtime core**: 98 transitive core runtime modules split via Lean 4.36 `module` + `meta import` depend solely on `Init`.
   - **Kernel-Verified Formal Proofs (`Grassmann/Proofs/`, `Tests/Proofs/Axioms.lean`)**: **83** `#print axioms` `#guard_msgs` audits (`[propext, Classical.choice, Quot.sound]` only; zero `sorry`, zero custom `axiom`, zero `native_decide`) covering Clifford ring/exterior/Hodge/conformal laws, Poincaré duality vs degenerate PGA3 Hodge star, PGA3 Study motors, CGA2/3 null points & Euclidean distances, exact rational `ℝ3` rotors, `STA` (`-+++`) Lorentz boost & spatial rotation Minkowski invariance, and `PGA2`/`PGA3` Wedge projective incidence laws.
   - **3.49M+ Oracle & Property Tests (`Tests/`, `oracle/`)**: pinned Julia goldens + property/unit tests (`3,490,648 passed, 0 failed`).

2. **Interactive `Grassmann.Studio` Engine (32 Strictly `Init`-Only Modules)**:
   - **74 CoffeeShop Presets** (`Grassmann/CoffeeShop/`): 2D/3D PGA, CGA, STA, Dual/Hyperbolic/Elliptic algebras, plus 5 physics/relativity/streamline showstoppers (`pga3d_bouncing_cube`, `pga3d_double_pendulum`, `sta_terrell_penrose`, `sta_maxwell_streamlines`, `pga3d_hopf_streamlines`), all with KaTeX `formula` + `summary` metadata and interactive `@param` sliders.
   - **Wedge 2D + 3D Game (`Grassmann/Wedge/`)**: 16 projective geometry puzzle levels, 6 animated tutorials (`T1..T6`), and SplitMix64 procedural challenge generation.
   - **LiveScript v2 & Fast 3D Meshing (`Grassmann/Eval/`)**: pure-Lean GA script parser/evaluator with `slider(...)` / `@param` bindings, forward-mode AD surfaces, 2D marching-triangles contours, and an unboxed `ImplicitExpr` RPN bytecode VM + adaptive Marching Tetrahedra (`Gyroid 16³` in **1.3 ms** native / **3.2–3.9 ms** WASM).
   - **Pure-Lean GPU Shader Compiler (`Grassmann/Codegen/GPUInit.lean`)**: emits straight-line WGSL, GLSL 300 es, and Metal MSL OPNS & implicit raymarching shaders directly from Lean.
   - **Binary `GSIR` v1 Wire Protocol (`Grassmann/Scene/`, [`docs/SCENE_IR_V1.md`](docs/SCENE_IR_V1.md))**: compact binary frames shared verbatim across Web, macOS, and Apple Vision Pro.

3. **Multi-Target Deployment (`c/`, `wasm/`, `web/`, `Grassmann/Server.lean`, [`docs/CABI_WASM_SERVER.md`](docs/CABI_WASM_SERVER.md))**:
   - **Native C ABI (`scripts/build-cabi.sh`)**: standalone `libgrassmann_cabi.dylib` + `include/grassmann/cabi.h`.
   - **Browser WebAssembly (`scripts/build-wasm.sh`)**: Lean 4.36 → C → Emscripten hybrid `-O3`/`-Oz` WASM (**1.44 MB raw / 434.5 KB gz**, content-fingerprinted `wasm-manifest.json`).
   - **Apple 3-Platform Static XCFramework (`scripts/build-apple-static.sh`)**: `GrassmannCABI.xcframework` for `macos-arm64`, `xros-arm64-simulator`, and `xros-arm64` powering native macOS + Apple Vision Pro clients.
   - **Pure-Lean Binary Server (`lake exe ga-server`)**: persistent HTTP/1.1 keep-alive + RFC 6455 binary WebSocket server in pure Lean 4.36 (`Std.Internal.UV.TCP`).
   - **WebGL2 / WebXR Studio (`web/`)**: thin Three.js renderer (zero JS geometric algebra math) with KaTeX formula card, visual 74-preset gallery, dynamic `@param` sliders, timeline, GA syntax highlighter, Zen mode, 60fps WebM recorder, and `.grassmann.json` import/export.

---

## Quickstart

### Core Lean Build, Tests & Benchmarks
```bash
lake build --wfail                                   # all libraries, Studio, CABI, tests, bench, ga-server
uv run python3 scripts/check_packed_linearity.py     # ALOK-1007 codegen linearity & Init-only closure guard
lake test                                            # 3,490,648+ unit, golden & property tests
lake exe bench --smoke                               # benchmark smoke check
```

### Studio Tests, Native C ABI, WASM, Apple XCFramework & Local Server
```bash
# Run all 6 pure-Lean Studio test suites
for t in Studio StudioExpansion StudioParity GPUInit LiveScript Showcase; do
  lake build --wfail "Tests.$t" && \
    lake env lean --setup <(lake setup-file "Tests/$t.lean") --run "Tests/$t.lean"
done

# Build native C ABI, Emscripten WASM, and 3-platform Apple XCFramework
./scripts/build-cabi.sh
./scripts/build-wasm.sh
./scripts/build-apple-static.sh

# Pure-Lean HTTP/WebSocket server & 3-way Native/WASM/Server parity benchmarks
.lake/build/bin/ga-server --self-test
node scripts/test-ga-server.mjs
node scripts/bench-cabi-wasm.mjs

# Web Studio (local dev, unit tests, production build)
cd web && npm ci && npm test && npm run build
```

### Sub-Packages (`gallery/` & `bridge/`)
- **`gallery/`**: 2D/3D plots rendered with [LeanPlot](https://github.com/alok/LeanPlot) (`cd gallery && lake build --wfail && lake test` — 673 checks).
- **`bridge/`**: formal equivalence bridge between `Grassmann.Spec` and mathlib's `CliffordAlgebra`/`ExteriorAlgebra`.

---

## Credit & License

- **Core mathematics, API design, and package architecture**: [Michael Reed](https://github.com/chakravala) ([Grassmann.jl](https://github.com/chakravala/Grassmann.jl)); please cite [`CITATION.cff`](CITATION.cff) when using this library.
- **Interactive PGA/CGA conventions, CoffeeShop & Wedge game inspiration**: [Steven De Keninck](https://github.com/enkimute) ([ganja.js](https://github.com/enkimute/ganja.js)).
- **License**: [GNU AGPL v3](LICENSE) (as a port of AGPL-3.0 software).
