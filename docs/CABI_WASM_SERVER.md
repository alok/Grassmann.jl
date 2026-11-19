# Grassmann.lean Init-Only C ABI, Lean 4.36 → WASM, Apple Static Libs & Pure-Lean `ga-server`

*"It's all in Lean"* — unified high-performance native, browser WebAssembly, Apple (`macOS` + `visionOS` + `xrsimulator`) static XCFramework, and local HTTP/WebSocket binary `GSIR` v1 transport layers running the **entire 33-module `Grassmann.Studio` engine** with zero compiler/Std dependencies.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck (`enkimute` / `ganja.js`).

---

## 1. Strictly `Init`-Only 33-Module `Grassmann.Studio` + Native C ABI (`scripts/build-cabi.sh`)

- **Strict `Init`-only Lean leaf**: All **33 modules** (`Grassmann.CABI.{Kernels,Alg,Studio}`, `Grassmann.CABI`, `Grassmann.Scene.*`, `Grassmann.Eval.{Parser,Contour,Engine,Calc,Implicit3D,ImplicitExpr}`, `Grassmann.Wedge.{Types,Levels2D,Levels3D,Tutorials,Engine}`, `Grassmann.Codegen.{GPU,GPUInit}`, `Grassmann.CoffeeShop.{Mesh,Presets,PresetsExtra,PresetsParity,PresetsShowcase,Tour,Engine}`, `Grassmann.Studio`) import **ONLY `Init.*`** — zero `Lean.*`, `Lake.*`, `Std.*`, `DirectSum`, `Lean.Data.Json`, or elaborator imports.
- **Full Unified Engine Included**:
  - **77 CoffeeShop presets** (19 base + 28 `PresetsExtra` + 22 `PresetsParity` + 8 `PresetsShowcase` showstoppers incl. `pga3d_bouncing_cube`, `pga3d_double_pendulum`, `sta_terrell_penrose`, `sta_maxwell_streamlines`, `pga3d_hopf_streamlines`, `implicit_barth_sextic`, `cga3d_dupin_cyclide_raymarch`, `pga3d_gears_kinematics`, plus dual-handle 3D bunny tilt slicing), all with KaTeX `formula` + `summary` metadata, interactive `@param` sliders (`setParam`), and a **6-stop Guided GA Tour** (`Grassmann.CoffeeShop.Tour`, `loadTourStop`).
  - **Live User-Typed 3D Implicit & Parametric Evaluator**:
    - `{"op":"evalImplicit","expr":"...","gpuRaymarch":bool,"bound":f}` — adaptive 6-tet Kuhn Marching Tetrahedra bytecode VM (`gpuRaymarch: false`) OR live `GPUInit` GLSL 300 es / WGSL / Metal MSL raymarching shader compilation respecting `bound` (`gpuRaymarch: true`).
    - `{"op":"evalParametric","fx":"...","fy":"...","fz":"..."}` — live user-typed parametric 3D surface mesher.
  - **17 Wedge 2D + 3D PGA puzzle levels (incl. L17 3D Circumcenter + Centroid Euler Axis) + 6 Animated Tutorial Cards (`T1..T6`) + Lossless 64-bit SplitMix64 Procedural Challenge Generator** (`wedgeTutorial` / `wedgeRandom` with `seedStr`).
  - **Live GA script parser/evaluator**, forward-mode AD surfaces, marching-triangles 2D contours, **GAlculator**, exact **R3 rational rotors**, explicit `resetTime` / `seekTime`, and **WGSL / GLSL 300 es / Metal MSL GPU shader codegen (`GPUInit`)**.
- **Public Header & Swift Module**: `include/grassmann/cabi.h` + `include/module.modulemap` (`import GrassmannCABI`; zero `lean_object*` exposed).
- **Runtime Lifecycle & Thread-Safety**:
  - `grassmann_initialize()` — initializes both the Lean runtime and `Grassmann.CABI` (standalone C/WASM/Python hosts).
  - `grassmann_initialize_module()` — initializes **only** `Grassmann.CABI` when the host runtime (e.g. `LeanVisionOSRuntime.xcframework`) has **already** called `lean_initialize_runtime_module()`.
  - `grassmann_attach_thread()` / `grassmann_detach_thread()` — thread-local idempotent attach/detach wrappers around `lean_initialize_thread` / `lean_finalize_thread` for dedicated native OS worker threads (e.g. Swift `Foundation.Thread` / `pthread`; never call Lean C ABI from an arbitrary Swift cooperative `actor` pool thread!).
  - Overflow-guarded batch API (`pointCount > SIZE_MAX / (3 * sizeof(double))` → `GSIR_ERR_BAD_INPUT`) + automated **`ALOK-1007` generated-C linearity check** on `Kernels.c`'s `pga3MotorApplyXYZBatch_go` loop.
- **Canonical `GSIR` v1 Studio API**:
  - `grassmann_studio_create`, `grassmann_studio_destroy`, `grassmann_studio_dispatch_bin`, `grassmann_studio_dispatch_json`, `grassmann_studio_get_frame` (idempotent cached copy on `GSIR_ERR_BUF_SMALL`), `grassmann_studio_preset_catalog` (all 77 presets JSON), `grassmann_studio_tour_catalog` (6-stop Guided Tour JSON).

```bash
./scripts/build-cabi.sh
```

---

## 2. Reproducible Lean 4.36 → C → Emscripten WASM Pipeline (`scripts/build-wasm.sh`)

- Compiles **all 33 Init-only Lean 4.36 C modules** + `c/grassmann_cabi.c` + self-contained pure-C99 Lean 4.36 WASM runtime (`wasm/lean_wasm_rt.c` — zero GMP, zero libuv, zero mimalloc, zero OpenSSL, zero C++, full `lean_apply_1..16/m/n`, 64-bit big-Nat/Int + full-precision IEEE-754 `double` literal preservation for 21+ digit constants like `pi`, **8-byte aligned `wasm32` allocator header** across `lean_wasm_rt.c` & staged `lean.h`, `__builtin_memcpy` 64-bit ctor accessors — verified ZERO misaligned accesses under Clang UBSan `-fsanitize=alignment -fno-sanitize-recover=alignment` and `0 / 6,106,908` live heap allocs!).
- Emits both canonical assets (`grassmann.wasm`, `grassmann.mjs`, `grassmann_wasm.mjs`) AND **content-fingerprinted immutable-cache-safe assets** (`grassmann.<sha256_10>.wasm`, `grassmann.<sha256_10>.mjs` with rewritten binary reference verified via isolated no-`locateFile` import, and `wasm-manifest.json`) in `wasm/dist/`.

```bash
./scripts/build-wasm.sh
```

---

## 3. Apple 3-Platform Static Libraries & `GrassmannCABI.xcframework` (`scripts/build-apple-static.sh`)

Cross-compiles all 33 Init-only Lean 4.36 `.c` sources + `c/grassmann_cabi.c` matching `LeanVisionOSRuntime.xcframework` (`v4.36.0`, commit `611c117b`, Xcode SDK `27.3`), staging in `.lake/build/apple-staging` and atomically publishing to `.lake/build/apple`:
- `macos-arm64` (`arm64-apple-macos27.0`, `-mmacosx-version-min=27.0`, host `LEAN_MIMALLOC` ON)
- `xros-arm64-simulator` (`arm64-apple-xros2.0-simulator`, `USE_MIMALLOC=OFF`, `USE_GMP=OFF`, zero `mi_`/`gmp` refs)
- `xros-arm64` (`arm64-apple-xros2.0`, `USE_MIMALLOC=OFF`, `USE_GMP=OFF`, zero `mi_`/`gmp` refs)
- Packaged into `.lake/build/apple/GrassmannCABI.xcframework` (`import GrassmannCABI`) and live-linked cleanly against `LeanVisionOSRuntime.xcframework` across all 3 Apple platforms!

```bash
./scripts/build-apple-static.sh
```

---

## 4. Pure-Lean Persistent Binary Server (`lake exe ga-server`)

- **100% Pure Lean 4.36** (`Grassmann/Server.lean`, `Grassmann/Server/Main.lean`) using `Std.Internal.UV.TCP` + `IO.asTask` + `Std.BaseMutex` + pure-Lean SHA-1/Base64 RFC 6455 WebSocket handshake, serving the exact same full 33-module `Grassmann.Studio` engine.
- **Endpoints** (default `http://127.0.0.1:8787`, CORS enabled):
  - `GET /health` → JSON server/protocol metadata
  - `GET /api/presets` → Full **77-preset** Lean CoffeeShop catalog JSON
  - `GET /api/tour` → Full **6-stop** Lean Guided GA Tour catalog JSON
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

## 5. Measured Wave 6E Unified Benchmarks (33 `Init`-Only Modules, 77 Presets + 6-Stop Tour + 8B-Aligned Zero-UB WASM, M4 Max)

| Target | Artifact Size | Key Verified Latency / Metrics |
|---|---|---|
| Native C ABI (`libgrassmann_cabi.dylib`) | **5.5 MB** (`5,812,728 B`, `libc++` + `libSystem` only) | `pga3_motor_compose` **36.7–37.6 ns**, `apply_xyz_batch` **7.18 ns/pt** (`ALOK-1007` PASS), `DragHandle→GSIR` **37.75–37.93 µs/frame**, bytecode Gyroid `16³` **1.64 ms**, `GPUInit` **0.35 ms** |
| Hybrid `-O3`/`-Oz` 8B-Aligned Emscripten WASM (`grassmann.<hash>.wasm`) | **1.50 MB raw / 453.1 KB gz** (`e3d4772aca`, `wasm-manifest.json`) | ALL **77 unique presets** + **6-stop Tour** + **17 Wedge levels** + **ALL 6 Dots Round-2 regressions** + **`0 / 6,106,908` misaligned live allocs** (`UBSan` ZERO misaligned accesses!), bytecode Gyroid `16³` (`3959` verts / `7404` tris, `[-1.60,1.60]³`) **3.00 ms avg** (`3.14 ms` cold!), `GPUInit` GLSL3+WGSL+MSL **1.16 ms**, `motor_compose` **54.1–59.5 ns**, `DragHandle→GSIR` **84.17 µs/frame** (11.9k fps) |
| Apple 3-Platform XCFramework (`GrassmannCABI.xcframework`) | `macos` **7.1 MB**, `xrsim` **7.5 MB**, `xros` **7.5 MB** | Live-linked ZERO warnings against `LeanVisionOSRuntime.xcframework` on ALL 3 platforms (`16M` macOS, `18M` xrsim, `18M` xros), live exec `170,840 B` dual-handle bunny + `44,939 B` 77-preset catalog |
| Pure-Lean `ga-server` (`lake exe ga-server`) | Standalone native binary | RFC 6455 WS **110.9 µs/frame**, HTTP/1.1 keep-alive **149.2 µs/req**, bytecode Gyroid `16³` **2.19 ms**, `GET /api/presets` (77 presets) + `GET /api/tour` (6 stops); 3-way parity (`scripts/bench-cabi-wasm.mjs`) **ALL 19 GSIR SCENES + 7 KERNELS + 77/77 PRESETS + 6/6 TOUR STOPS IDENTICAL PASS** |

