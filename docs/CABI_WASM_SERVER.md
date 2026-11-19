# Grassmann.lean Init-Only C ABI, Lean 4.36 → WASM, Apple Static Libs & Pure-Lean `ga-server`

*"It's all in Lean"* — unified high-performance native, browser WebAssembly, Apple (`macOS` + `visionOS` + `xrsimulator`) static XCFramework, and local HTTP/WebSocket binary `GSIR` v1 transport layers running the **entire 25-module `Grassmann.Studio` engine** with zero compiler/Std dependencies.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck (`enkimute` / `ganja.js`).

---

## 1. Strictly `Init`-Only 25-Module `Grassmann.Studio` + Native C ABI (`scripts/build-cabi.sh`)

- **Strict `Init`-only Lean leaf**: All 25 modules (`Grassmann.CABI.{Kernels,Alg,Studio}`, `Grassmann.CABI`, `Grassmann.Scene.*`, `Grassmann.Eval.*`, `Grassmann.Wedge.*`, `Grassmann.Codegen.*`, `Grassmann.CoffeeShop.*`, `Grassmann.Studio`) import **ONLY `Init.*`** — zero `Lean.*`, `Lake.*`, `Std.*`, `DirectSum`, `Lean.Data.Json`, or elaborator imports.
- **Full Unified Engine Included**:
  - **19 CoffeeShop presets** (including the 170 KB sculpted 3D Stanford Bunny `#pga3d_slicing` with live plane slicing + stitched 2D `ContourOverlay`, `pga3d_objects`, `pga3d_physics_top` RK4, `pga3d_origami`, `cga3d_conformal`, `cga3d_cyclide`, `sta_lorentz_boost`, `pga2d_desargues`, etc.)
  - **16 Wedge 2D + 3D PGA puzzle levels** (live `isPreview` ghost gestures, Lean-derived `hold` threshold, projective win detection, undo, scoring, hints)
  - **Live GA script parser/evaluator**, forward-mode AD parametric surfaces, marching-triangles implicit contours, **GAlculator**, exact **R3 rational rotors**, and **WGSL / GLSL / Metal MSL OPNS GPU shader codegen**.
- **Public Header & Swift Module**: `include/grassmann/cabi.h` + `include/module.modulemap` (`import GrassmannCABI`; zero `lean_object*` exposed).
- **Runtime Lifecycle**:
  - `grassmann_initialize()` — initializes both the Lean runtime and `Grassmann.CABI` (for standalone C/WASM/Python hosts).
  - `grassmann_initialize_module()` — initializes **only** the `Grassmann.CABI` Lean module when the host runtime (e.g. `LeanVisionOSRuntime.xcframework` in `LeanCalculator`) has **already** called `lean_initialize_runtime_module()`.
- **Canonical `GSIR` v1 Studio API** (all 5 `#17` refinements enforced):
  - `grassmann_studio_create`, `grassmann_studio_destroy`
  - `grassmann_studio_dispatch_bin`, `grassmann_studio_dispatch_json`
  - `grassmann_studio_get_frame` (idempotent cached-frame copy on `GSIR_ERR_BUF_SMALL`)
  - `grassmann_studio_preset_catalog` (full 19-preset Lean catalog JSON)
  - Single source of truth: `Grassmann/Scene/{Types,Json,Binary}.lean` (8-byte aligned sections & tail-padded `totalByteLen`, CCW front-face winding, unchanged `metaJsonLen = 0` & cached `MESH_ASSETS` delta omission).
- **Direct Packed `double*` Numeric GA Kernels**: STA `Cl(3,1)` (`-+++`), R3 + exact zero-sqrt rational rotors, PGA2, PGA3 (8-double motors + batch XYZ), CGA2, CGA3, and arbitrary `Cl(p, q, r)` (`p + q + r ≤ 6`).

### Measured Native Results (macOS arm64, Lean `v4.36.0`)

| Metric | Before (with `libLean.a`) | Now (25-module Init-only `libgrassmann_cabi.dylib`) |
|---|---|---|
| Standalone dylib size | 182–264 MB | **3.5 MB** (`3,661,400 B`, **52–75× smaller**) |
| External dynamic deps (`otool -L`) | `libleanshared`, `libssl`, `libcrypto` | **ONLY `libc++.1.dylib` & `libSystem.B.dylib`** |
| `pga3_motor_compose` crossing | — | **35.7 ns/call** |
| `pga3_apply_xyz_batch` (1,000 pts) | — | **5.3 ns/pt** (`5.3 µs` / 1,000 pts) |
| Full `DragHandle` → `GSIR` v1 frame | ~10–100 ms (JSON/10Hz) | **24.6 µs/frame** (**40,652 fps max**) |

```bash
./scripts/build-cabi.sh
```

---

## 2. Reproducible Lean 4.36 → C → Emscripten WASM Pipeline (`scripts/build-wasm.sh`)

- Compiles **all 25 Init-only Lean 4.36 C modules** + `c/grassmann_cabi.c` + our self-contained pure-C99 Lean 4.36 WASM runtime (`wasm/lean_wasm_rt.c` — zero GMP, zero libuv, zero mimalloc, zero OpenSSL, zero C++, full `lean_apply_1..16/m/n` closure support, 64-bit big-Nat support on `wasm32`) via `emcc -O3 -ffunction-sections -fdata-sections -Wl,--gc-sections`.
- Outputs `wasm/dist/grassmann.wasm`, `wasm/dist/grassmann.mjs`, and `wasm/dist/grassmann_wasm.mjs`.

### Measured WASM Results (`emcc 7.0.0`, Node v26.13.0)

| Metric | Value |
|---|---|
| `grassmann.wasm` raw size (full 25-module Studio!) | **871 KB** |
| `grassmann.wasm` gzipped size | **238.8 KB** |
| `pga3_motor_compose` (WASM) | **59.7 ns/call** |
| Full `DragHandle` → `GSIR` v1 frame (WASM) | **73.4 µs/frame** (**13,628 fps max**) |
| Verified in Node (`wasm/test_wasm.mjs`) | **All 19 presets** (incl. 170 KB sculpted bunny + OPNS GLSL/WGSL/MSL), `pga3d_objects` delta cache, **Wedge 2D/3D** (L1/L9/L10/L16 + live `isPreview` + L1 solve), `evalScript`, `evalSurface`, `evalEquations` (marching-triangles), `calcEval` |

```bash
./scripts/build-wasm.sh
```

---

## 3. Apple 3-Platform Static Libraries & `GrassmannCABI.xcframework` (`scripts/build-apple-static.sh`)

Cross-compiles all 25 Init-only Lean 4.36 `.c` sources + `c/grassmann_cabi.c` matching `LeanVisionOSRuntime.xcframework` (`v4.36.0`, commit `611c117b`, Xcode SDK `27.3`):

| Slice | Target Triple | Runtime ABI (`config.h`) | Archive Size | Live Link w/ `LeanVisionOSRuntime` |
|---|---|---|---|---|
| `macos-arm64` | `arm64-apple-macos27.0` (`-mmacosx-version-min=27.0`) | Host `LEAN_MIMALLOC` ON | **2.9 MB** | **PASS** (13 MB linked smoke, executes 170 KB bunny!) |
| `xros-arm64-simulator` | `arm64-apple-xros2.0-simulator` | `USE_MIMALLOC=OFF`, `USE_GMP=OFF` | **3.1 MB** | **PASS** (15 MB linked binary, zero `mi_`/`gmp` refs) |
| `xros-arm64` | `arm64-apple-xros2.0` | `USE_MIMALLOC=OFF`, `USE_GMP=OFF` | **3.1 MB** | **PASS** (15 MB linked binary, zero `mi_`/`gmp` refs) |

Packaged automatically with `include/grassmann/cabi.h` + `include/module.modulemap` (`import GrassmannCABI`) into:
- `.lake/build/apple/GrassmannCABI.xcframework`
- `.lake/build/apple/{macos-arm64,xros-arm64-simulator,xros-arm64}/libgrassmann_cabi.a`

> **Host Integration Note (`LeanCalculator` / `LeanVisionOS`)**: When embedding `GrassmannCABI.xcframework` alongside `LeanVisionOSRuntime.xcframework` in the same process, call `grassmann_initialize_module()` (instead of `grassmann_initialize()`) after `LeanVisionOS` starts the Lean runtime, avoiding duplicate `lean_initialize_runtime_module()` calls.

```bash
./scripts/build-apple-static.sh
```

---

## 4. Pure-Lean Persistent Binary Server (`lake exe ga-server`)

- **100% Pure Lean 4.36** (`Grassmann/Server.lean`, `Grassmann/Server/Main.lean`) using `Std.Internal.UV.TCP` + `IO.asTask` + `Std.BaseMutex` + pure-Lean SHA-1/Base64 RFC 6455 WebSocket handshake, serving the exact same full 25-module `Grassmann.Studio` engine.
- **Endpoints** (default `http://127.0.0.1:8787`, CORS enabled):
  - `GET /health` → JSON server/protocol metadata
  - `GET /api/presets` → Full 19-preset Lean CoffeeShop catalog JSON
  - `GET /ws` → RFC 6455 WebSocket (Binary frames → `dispatchBin`, Text frames → `dispatchJson`, replies with Binary `GSIR` v1 frames)
  - `POST /api/session`, `DELETE /api/session/:id`, `GET /api/session/:id/frame`, `POST /api/session/:id/bin`, `POST /api/session/:id/json`
  - Default-session shortcuts: `GET /api/frame`, `POST /api/event/bin` (`/api/dispatch/bin`), `POST /api/event/json` (`/api/dispatch/json`)
  - Static asset serving (`--static <dir>`, auto-detects `./web/dist`, blocks `..` traversal).

### Measured Server Latency (`scripts/test-ga-server.mjs`)

| Transport | Roundtrip Latency | Throughput |
|---|---|---|
| RFC 6455 WebSocket binary `GSIR` v1 | **87.1 µs/frame** | **11,483 fps max** |
| HTTP/1.1 keep-alive binary `GSIR` v1 | **116.8 µs/req** | **8,562 req/s** |

```bash
lake build --wfail ga-server
.lake/build/bin/ga-server --self-test
node scripts/test-ga-server.mjs
```
