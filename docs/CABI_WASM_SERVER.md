# Grassmann.lean Init-Only C ABI, Lean 4.36 → WASM & Pure-Lean `ga-server`

*"It's all in Lean"* — high-performance native, browser WebAssembly, and local HTTP/WebSocket binary `GSIR` v1 transport layers for **Grassmann.lean** and **LeanCalculator**.

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck (`enkimute` / `ganja.js`).

---

## 1. Init-Only Standalone Native C ABI (`scripts/build-cabi.sh`)

- **Strict `Init`-only Lean leaf**: `Grassmann/CABI/{Kernels,ScenePack,Studio}.lean` and `Grassmann/CABI.lean` import **ONLY `Init.*`** — zero `Lean.*`, `Lake.*`, `Std.*`, `Lean.Data.Json`, or elaborator/codegen imports.
- **Public Header**: `include/grassmann/cabi.h` (clean C11 / C++17 / Swift C-interop; zero `lean_object*` exposed).
- **C Shim**: `c/grassmann_cabi.c` (caller-owned `double*` and `uint8_t*` buffers, zero per-frame allocations, thread-safe studio mutex on native builds).
- **Canonical `GSIR` v1 Studio API** (all 5 `#17` refinements enforced):
  - `grassmann_studio_create`, `grassmann_studio_destroy`
  - `grassmann_studio_dispatch_bin`, `grassmann_studio_dispatch_json`
  - `grassmann_studio_get_frame` (idempotent cached-frame copy on `GSIR_ERR_BUF_SMALL` — zero double-mutation or lost delta `MESH_ASSETS`!)
  - 8-byte aligned section directory & `0x0B MESH_ASSETS` records, CCW front-face winding, `metaJsonLen = 0` unchanged hot-frame delta, `forceFullSnapshot` (`flags` b0), `WedgeGesture` `isPreview` + Lean-derived `hold` (`‖dir‖ < 0.1`), `CAMERA.flags` (`b0=isOrtho`), ganja motor wire order `(s, e01, e02, e03, e12, e13, e23, e0123)`.
- **Direct Packed Numeric GA Kernels** (zero string/JSON roundtrip):
  - STA `Cl(3,1)` (`-+++`, preserving `ALOK-950` invariants + Lorentz boost + spatial wedge)
  - R3 `Cl(3,0,0)` + exact zero-sqrt rational rotor (`apply_rational_rotor`, `rational_rotor_cayley`)
  - PGA2 `Cl(2,0,1)` & PGA3 `Cl(3,0,1)` (full 16-blade + specialized 8-float motors: `compose`, `reverse`, `is_unit`, `normalize` [Study], `inverse`, `exp`, `log`, `slerp`, `to_mat4`, `apply_xyz`, `apply_xyz_batch`)
  - CGA2 `Cl(3,1)` & CGA3 `Cl(4,1)` (`up`, `down`, `dual_sphere`, `dual_plane`, `mul`, `wedge`, `left_contract`, `sandwich`)
  - Generic `Cl(p, q, r)` (`p + q + r ≤ 6`, up to 64 basis blades).

### Measured Native Results (macOS arm64, Lean `v4.36.0`)

| Metric | Before (with `libLean.a`) | Now (Init-only `libgrassmann_cabi.dylib`) |
|---|---|---|
| Standalone dylib size | 182–264 MB | **2.5 MB** (`2,615,032 B`, **73–105× smaller**) |
| External dynamic deps (`otool -L`) | `libleanshared`, `libssl`, `libcrypto` | **ONLY `libc++.1.dylib` & `libSystem.B.dylib`** |
| `pga3_motor_compose` crossing | — | **35.8 ns/call** |
| `pga3_apply_xyz_batch` (1,000 pts) | — | **4.9 ns/pt** (`4.92 µs` / 1000 pts) |
| Full `DragHandle` → `GSIR` v1 frame | ~10–100 ms (JSON/10Hz) | **15.90 µs/frame** (**62,899 fps max**) |

```bash
./scripts/build-cabi.sh
```

---

## 2. Reproducible Lean 4.36 → C → Emscripten WASM Pipeline (`scripts/build-wasm.sh`)

- **How it works**:
  1. `lake build --wfail Grassmann.CABI.*:c` emits genuine Lean 4.36 C sources.
  2. Official `<lean/lean.h>` and `<lean/version.h>` are staged from `$(lean --print-prefix)` with `#define LEAN_EMSCRIPTEN 1` (zero external `~/lean4` repo required!).
  3. `emcc -O3` compiles the Lean-generated `.c` files + `c/grassmann_cabi.c` + our self-contained pure-C99 Lean 4.36 WASM runtime (`wasm/lean_wasm_rt.c` — zero GMP, zero libuv, zero mimalloc, zero OpenSSL, zero C++, zero leaks, 64-bit big-Nat support on `wasm32`) into `wasm/dist/grassmann.wasm` + `wasm/dist/grassmann.mjs` + `wasm/dist/grassmann_wasm.mjs`.

### Measured WASM Results (`emcc 7.0.0`, Node v26.13.0)

| Metric | Value |
|---|---|
| `grassmann.wasm` raw size | **235 KB** |
| `grassmann.wasm` gzipped size | **73.2 KB** |
| `pga3_motor_compose` (WASM) | **49.6 ns/call** |
| Full `DragHandle` → `GSIR` v1 frame (WASM) | **7.06 µs/frame** (**141,556 fps max**) |

```bash
./scripts/build-wasm.sh
```

---

## 3. Pure-Lean Persistent Binary Server (`lake exe ga-server`)

- **100% Pure Lean 4.36** (`Grassmann/Server.lean`, `Grassmann/Server/Main.lean`) using `Std.Internal.UV.TCP` + `IO.asTask` concurrent workers + `Std.BaseMutex` + pure-Lean SHA-1/Base64 RFC 6455 WebSocket handshake. Zero Python, zero C socket shims, zero per-request process spawning.
- **Endpoints** (default `http://127.0.0.1:8787`, CORS enabled):
  - `GET /health` → JSON server/protocol metadata
  - `GET /ws` → RFC 6455 WebSocket (dedicated session per connection; Binary frames → `dispatchBin`, Text frames → `dispatchJson`, replies with Binary `GSIR` v1 frames)
  - `POST /api/session`, `DELETE /api/session/:id`, `GET /api/session/:id/frame`, `POST /api/session/:id/bin`, `POST /api/session/:id/json`
  - Default-session shortcuts: `GET /api/frame`, `POST /api/event/bin` (`/api/dispatch/bin`), `POST /api/event/json` (`/api/dispatch/json`)
  - Static asset serving (`--static <dir>`, auto-detects `./web/dist`, blocks `..` traversal).

### Measured Server Latency (`scripts/test-ga-server.mjs`)

| Transport | Roundtrip Latency | Throughput |
|---|---|---|
| RFC 6455 WebSocket binary `GSIR` v1 | **86.1 µs/frame** | **11,613 fps max** |
| HTTP/1.1 keep-alive binary `GSIR` v1 | **120.7 µs/req** | **8,285 req/s** |

```bash
lake build --wfail ga-server
.lake/build/bin/ga-server --self-test
node scripts/test-ga-server.mjs
```
