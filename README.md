# Grassmann.lean

A Lean 4 port and interactive 3D Geometric Algebra platform built on [Michael Reed](https://github.com/chakravala)'s ⟨Grassmann-Clifford-Hodge⟩ differential geometric algebra ecosystem ([Grassmann.jl](https://github.com/chakravala/Grassmann.jl) — `DirectSum`, `Leibniz`, `AbstractTensors`, `StaticVectors`, `Cartan`, `MeshTopology`, `Adapode`, `Fatou`, `UnitSystems`, `Similitude`, and more), paired with a pure-Lean interactive **Geometric Algebra Studio** inspired by [Steven De Keninck](https://github.com/enkimute)'s [ganja.js](https://github.com/enkimute/ganja.js) CoffeeShop and Wedge game.

- **Live Web Studio**: **[https://grassmann-studio.vercel.app](https://grassmann-studio.vercel.app)** (WebGL2 + WebXR, dedicated Web Worker Lean-compiled WASM, zero server required)
- **Toolchain**: `leanprover/lean4:v4.36.0` (zero external Lean dependencies in the root package)

---

## Architecture — *"It's All in Lean"*

1. **Core Geometric Algebra Engine (`DirectSum/`, `Grassmann/`, `Cartan/`, `MeshTopology/`, …)**:
   - Spaces are values (`ℝ^3`, `S!"-+++"`, `D!"0,1,1,1"`, `S!"∞∅+++"`); elements are indexed by space and grade/parity (`Chain V 2 Float`, `Spinor V Float`, `Multivector V Rat`).
   - Elaboration-time unrolled kernels (`Grassmann.Kernel.Generated.{R2,R3,R4,STA,PGA2,PGA3,CGA2,CGA3}`) run on unboxed `FloatArray`s at C/Julia speed (`interpreteCGA3 circle` **~70 ns**, `motorSlerp` **~56 ns**, 960-tri `sliceMeshByPlane` **~52 µs**, `ALOK-1007` linearity guard in [`scripts/check_packed_linearity.py`](scripts/check_packed_linearity.py); see [`docs/PERF.md`](docs/PERF.md)).
   - **Strictly `Init`-only runtime core**: 98 transitive core runtime modules split via Lean 4.36 `module` + `meta import` depend solely on `Init`.
   - **Kernel-Verified Formal Proofs (`Grassmann/Proofs/`, `Tests/Proofs/Axioms.lean`)**: **83** `#print axioms` `#guard_msgs` audits (`[propext, Classical.choice, Quot.sound]` only; zero `sorry`, zero custom `axiom`, zero `native_decide`) covering Clifford ring/exterior/Hodge/conformal laws, Poincaré duality vs degenerate PGA3 Hodge star, PGA3 Study motors, CGA2/3 null points & Euclidean distances, exact rational `ℝ3` rotors, `STA` (`-+++`) Lorentz boost & spatial rotation Minkowski invariance, and `PGA2`/`PGA3` Wedge projective incidence laws.
   - **3.49M+ Oracle & Property Tests (`Tests/`, `oracle/`)**: pinned Julia goldens + property/unit tests (`3,490,648 passed, 0 failed`).

2. **Interactive `Grassmann.Studio` Engine (33 Strictly `Init`-Only Modules)**:
   - **77 CoffeeShop Presets** (`Grassmann/CoffeeShop/`): 2D/3D PGA, CGA, STA, Dual/Hyperbolic/Elliptic algebras, dual-handle tiltable 3D Stanford Bunny slicing, and flagship physics/relativity/algebraic-surface showstoppers (`pga3d_bouncing_cube`, `pga3d_double_pendulum`, `sta_terrell_penrose`, `sta_maxwell_streamlines`, `pga3d_hopf_streamlines`, **Barth Sextic**, **Dupin Cyclide**, **Involute Gears**), all with KaTeX `formula` + `summary` metadata and interactive `@param` sliders.
   - **6-Stop Guided Geometric Algebra Tour** (`Grassmann/CoffeeShop/Tour.lean`): interactive beginner walkthrough served straight from Lean across Web, macOS, and Apple Vision Pro.
   - **Wedge 2D + 3D Game (`Grassmann/Wedge/`)**: **17** projective geometry puzzle levels (incl. L17 3D Euler Axis Grand Finale), **6** animated tutorials (`T1..T6`), and SplitMix64 lossless 64-bit procedural challenge generation.
   - **LiveScript v2 & Fast 3D Meshing (`Grassmann/Eval/`)**: pure-Lean GA script parser/evaluator with `slider(...)` / `@param` bindings, forward-mode AD surfaces, 2D marching-triangles contours, and an unboxed `ImplicitExpr` RPN bytecode VM + adaptive Marching Tetrahedra (`Gyroid 16³` in **~1.6 ms** native / **~3.0 ms** WASM).
   - **Pure-Lean GPU Shader Compiler (`Grassmann/Codegen/GPUInit.lean`)**: emits straight-line WGSL, GLSL 300 es, and Metal MSL OPNS & implicit raymarching shaders directly from Lean.
   - **Binary `GSIR` v1 Wire Protocol (`Grassmann/Scene/`, [`docs/SCENE_IR_V1.md`](docs/SCENE_IR_V1.md))**: compact binary frames shared verbatim across Web, macOS, and Apple Vision Pro.

3. **Multi-Target Deployment (`c/`, `wasm/`, `web/`, `Grassmann/Server.lean`, [`docs/CABI_WASM_SERVER.md`](docs/CABI_WASM_SERVER.md))**:
   - **Native C ABI (`scripts/build-cabi.sh`)**: standalone `libgrassmann_cabi.dylib` (**5.6 MB**, zero `libleanshared`) + `include/grassmann/cabi.h`.
   - **Zero-UB 8-Byte-Aligned Browser WebAssembly (`scripts/build-wasm.sh`)**: Lean 4.36 → C → Emscripten hybrid `-O3`/`-Oz` WASM (`grassmann.0d2c5243cc.wasm`, **1.52 MB raw / 457.9 KB gz**, content-fingerprinted `wasm-manifest.json`, `~3.0 ms` bytecode Gyroid `16³`).
   - **Apple 3-Platform Static XCFramework (`scripts/build-apple-static.sh`)**: `GrassmannCABI.xcframework` for `macos-arm64`, `xros-arm64-simulator`, and `xros-arm64` powering native macOS + Apple Vision Pro clients.
   - **Pure-Lean Binary Server (`lake exe ga-server`)**: persistent HTTP/1.1 keep-alive + RFC 6455 binary WebSocket server in pure Lean 4.36 (`Std.Internal.UV.TCP`).
   - **WebGL2 / WebXR Studio (`web/`)**: thin Three.js renderer (zero JS geometric algebra math) with KaTeX formula card, visual 77-preset gallery, 6-stop Guided Tour, dynamic `@param` sliders, timeline, GA syntax highlighter, Zen mode, 60fps WebM recorder, and `.grassmann.json` import/export.

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
# Run all 9 pure-Lean Studio test suites
for t in FixpointR4 FixpointR3 Wave6 Studio StudioExpansion StudioParity GPUInit LiveScript Showcase; do
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

# Web Studio (local dev, 35 unit tests, production build)
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
