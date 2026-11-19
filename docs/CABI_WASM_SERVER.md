# Grassmann.lean Init-Only C ABI, Lean 4.36 → WASM, Apple Static Libs & Pure-Lean `ga-server`

*"It's all in Lean"* — unified high-performance native, browser WebAssembly, Apple (`macOS` + `visionOS` + `xrsimulator`) static XCFramework, and local HTTP/WebSocket binary `GSIR` v1 transport layers running the **entire 31-module `Grassmann.Studio` engine** with zero compiler/Std dependencies.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck (`enkimute` / `ganja.js`).

---

## 1. Strictly `Init`-Only 31-Module `Grassmann.Studio` + Native C ABI (`scripts/build-cabi.sh`)

- **Strict `Init`-only Lean leaf**: All **32 modules** (`Grassmann.CABI.{Kernels,Alg,Studio}`, `Grassmann.CABI`, `Grassmann.Scene.*`, `Grassmann.Eval.{Parser,Contour,Engine,Calc,Implicit3D,ImplicitExpr}`, `Grassmann.Wedge.{Types,Levels2D,Levels3D,Tutorials,Engine}`, `Grassmann.Codegen.{GPU,GPUInit}`, `Grassmann.CoffeeShop.{Mesh,Presets,PresetsExtra,PresetsParity,PresetsShowcase,Engine}`, `Grassmann.Studio`) import **ONLY `Init.*`** — zero `Lean.*`, `Lake.*`, `Std.*`, `DirectSum`, `Lean.Data.Json`, or elaborator imports.
- **Full Unified Engine Included**:
  - **74 CoffeeShop presets** (19 base + 28 `PresetsExtra` + 22 `PresetsParity` + 5 `PresetsShowcase` physics/relativity/streamline showstoppers: `pga3d_bouncing_cube`, `pga3d_double_pendulum`, `sta_terrell_penrose`, `sta_maxwell_streamlines`, `pga3d_hopf_streamlines`), all with KaTeX `formula` + `summary` metadata and interactive `@param` sliders (`setParam`).
  - **Live User-Typed 3D Implicit & Parametric Evaluator**:
    - `{"op":"evalImplicit","expr":"...","gpuRaymarch":bool}` — adaptive 6-tet Kuhn Marching Tetrahedra (`gpuRaymarch: false`) OR live `GPUInit` GLSL 300 es / WGSL / Metal MSL raymarching shader compilation (`gpuRaymarch: true`).
    - `{"op":"evalParametric","fx":"...","fy":"...","fz":"..."}` — live user-typed parametric 3D surface mesher.
  - **16 Wedge 2D + 3D PGA puzzle levels + 6 Animated Tutorial Cards (`T1..T6`) + SplitMix64 Procedural Challenge Generator** (`wedgeTutorial` / `wedgeRandom`).
  - **Live GA script parser/evaluator**, forward-mode AD surfaces, marching-triangles 2D contours, **GAlculator**, exact **R3 rational rotors**, and **WGSL / GLSL 300 es / Metal MSL GPU shader codegen (`GPUInit`)**.
- **Public Header & Swift Module**: `include/grassmann/cabi.h` + `include/module.modulemap` (`import GrassmannCABI`; zero `lean_object*` exposed).
- **Runtime Lifecycle & Thread-Safety**:
  - `grassmann_initialize()` — initializes both the Lean runtime and `Grassmann.CABI` (standalone C/WASM/Python hosts).
  - `grassmann_initialize_module()` — initializes **only** `Grassmann.CABI` when the host runtime (e.g. `LeanVisionOSRuntime.xcframework`) has **already** called `lean_initialize_runtime_module()`.
  - `grassmann_attach_thread()` / `grassmann_detach_thread()` — thread-local idempotent attach/detach wrappers around `lean_initialize_thread` / `lean_finalize_thread` for dedicated native OS worker threads (e.g. Swift `Foundation.Thread` / `pthread`; never call Lean C ABI from an arbitrary Swift cooperative `actor` pool thread!).
  - Overflow-guarded batch API (`pointCount > SIZE_MAX / (3 * sizeof(double))` → `GSIR_ERR_BAD_INPUT`) + automated **`ALOK-1007` generated-C linearity check** on `Kernels.c`'s `pga3MotorApplyXYZBatch_go` loop.
- **Canonical `GSIR` v1 Studio API**:
  - `grassmann_studio_create`, `grassmann_studio_destroy`, `grassmann_studio_dispatch_bin`, `grassmann_studio_dispatch_json`, `grassmann_studio_get_frame` (idempotent cached copy on `GSIR_ERR_BUF_SMALL`), `grassmann_studio_preset_catalog` (all 69 presets JSON).

```bash
./scripts/build-cabi.sh
```

---

## 2. Reproducible Lean 4.36 → C → Emscripten WASM Pipeline (`scripts/build-wasm.sh`)

- Compiles **all 31 Init-only Lean 4.36 C modules** + `c/grassmann_cabi.c` + self-contained pure-C99 Lean 4.36 WASM runtime (`wasm/lean_wasm_rt.c` — zero GMP, zero libuv, zero mimalloc, zero OpenSSL, zero C++, full `lean_apply_1..16/m/n`, 64-bit big-Nat/Int + full-precision IEEE-754 `double` literal preservation for 21+ digit constants like `pi`!).
- Emits both canonical assets (`grassmann.wasm`, `grassmann.mjs`, `grassmann_wasm.mjs`) AND **content-fingerprinted immutable-cache-safe assets** (`grassmann.<sha256_10>.wasm`, `grassmann.<sha256_10>.mjs`, and `wasm-manifest.json`) in `wasm/dist/`.

```bash
./scripts/build-wasm.sh
```

---

## 3. Apple 3-Platform Static Libraries & `GrassmannCABI.xcframework` (`scripts/build-apple-static.sh`)

Cross-compiles all 31 Init-only Lean 4.36 `.c` sources + `c/grassmann_cabi.c` matching `LeanVisionOSRuntime.xcframework` (`v4.36.0`, commit `611c117b`, Xcode SDK `27.3`), staging in `.lake/build/apple-staging` and atomically publishing to `.lake/build/apple`:
- `macos-arm64` (`arm64-apple-macos27.0`, `-mmacosx-version-min=27.0`, host `LEAN_MIMALLOC` ON)
- `xros-arm64-simulator` (`arm64-apple-xros2.0-simulator`, `USE_MIMALLOC=OFF`, `USE_GMP=OFF`, zero `mi_`/`gmp` refs)
- `xros-arm64` (`arm64-apple-xros2.0`, `USE_MIMALLOC=OFF`, `USE_GMP=OFF`, zero `mi_`/`gmp` refs)
- Packaged into `.lake/build/apple/GrassmannCABI.xcframework` (`import GrassmannCABI`) and live-linked cleanly against `LeanVisionOSRuntime.xcframework` across all 3 Apple platforms!

```bash
./scripts/build-apple-static.sh
```

---

## 4. Pure-Lean Persistent Binary Server (`lake exe ga-server`)

- **100% Pure Lean 4.36** (`Grassmann/Server.lean`, `Grassmann/Server/Main.lean`) using `Std.Internal.UV.TCP` + `IO.asTask` + `Std.BaseMutex` + pure-Lean SHA-1/Base64 RFC 6455 WebSocket handshake, serving the exact same full 31-module `Grassmann.Studio` engine.
- **Endpoints** (default `http://127.0.0.1:8787`, CORS enabled):
  - `GET /health` → JSON server/protocol metadata
  - `GET /api/presets` → Full **69-preset** Lean CoffeeShop catalog JSON
  - `GET /ws` → RFC 6455 WebSocket (Binary frames → `dispatchBin`, Text frames → `dispatchJson`, replies with Binary `GSIR` v1 frames)
  - `POST /api/session`, `DELETE /api/session/:id`, `GET /api/session/:id/frame`, `POST /api/session/:id/bin`, `POST /api/session/:id/json`
  - Default-session shortcuts: `GET /api/frame`, `POST /api/event/bin` (`/api/dispatch/bin`), `POST /api/event/json` (`/api/dispatch/json`)
  - Static asset serving (`--static <dir>`, auto-detects `./web/dist`, blocks `..` traversal).

```bash
lake build --wfail ga-server
.lake/build/bin/ga-server --self-test
node scripts/test-ga-server.mjs
```

---

## 5. Measured Wave 5A Unified Benchmarks (32 `Init`-Only Modules, 74 Presets + Bytecode MT + `@param`, M4 Max)

| Target | Artifact Size | Key Verified Latency / Metrics |
|---|---|---|
| Native C ABI (`libgrassmann_cabi.dylib`) | **5.4 MB** (`5,677,736 B`, `libc++` + `libSystem` only) | `pga3_motor_compose` **36.0–36.9 ns**, `apply_xyz_batch` **7.46 ns/pt** (`ALOK-1007` PASS), `DragHandle→GSIR` **37.4–43.5 µs/frame**, bytecode Gyroid `16³` **1.74 ms** (**8.4× faster**), `GPUInit` **0.37 ms** |
| Hybrid `-O3`/`-Oz` Emscripten WASM (`grassmann.<hash>.wasm`) | **1.44 MB raw / 434.5 KB gz** (`cbaef49869`, `wasm-manifest.json`) | ALL **74 unique presets** + KaTeX `formula`/`summary` + `@param`/`setParam` + `0x0D FLOW_PARTICLES` + **LiveScript v2**, bytecode Gyroid `16³` (`3959` verts / `7404` tris, `[-1.60,1.60]³`) **3.90 ms avg** (`5.44 ms` cold, **5.1× faster**!), `GPUInit` GLSL3+WGSL+MSL **1.41–1.50 ms**, `motor_compose` **57.2 ns**, `DragHandle→GSIR` **90.1–93.2 µs/frame** (10.7k fps) |
| Apple 3-Platform XCFramework (`GrassmannCABI.xcframework`) | `macos` **6.8 MB**, `xrsim` **7.2 MB**, `xros` **7.3 MB** | Live-linked ZERO warnings against `LeanVisionOSRuntime.xcframework` on ALL 3 platforms (`16M` macOS, `18M` xrsim, `18M` xros), live exec `170,416 B` bunny + `42,331 B` 74-preset catalog |
| Pure-Lean `ga-server` (`lake exe ga-server`) | Standalone native binary | RFC 6455 WS **115.9 µs/frame**, HTTP/1.1 keep-alive **154.6 µs/req**, bytecode Gyroid `16³` **2.30 ms**, `GET /api/presets` (74 presets); 3-way parity (`scripts/bench-cabi-wasm.mjs`) **ALL 14 GSIR SCENES + 7 KERNELS + 74/74 PRESETS IDENTICAL PASS** |

