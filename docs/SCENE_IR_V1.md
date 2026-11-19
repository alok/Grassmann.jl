# Canonical `SceneIR` v1 Contract (`GSIR`)

**Status**: Canonical Wave 1 Contract — **LOCKED** (incorporates all 5 `@verifier-core` #17 fixes; shared by `Grassmann/Scene`, `Grassmann/CABI`, WebGPU/WebGL2 Studio, and visionOS/macOS RealityKit/Metal `LeanCalculator`).
**Principle**: *"It's all in Lean."* Zero GA math, normal computation, contour/intersection extraction, CGA round classification, mesh slicing, or Wedge rules in JS/TS or Swift. Clients send thin `InputEvent`s and render packed little-endian `GSIR` binary frames directly into GPU buffers (`Float32Array`/`BigUint64Array` / `MTLBuffer` / `LowLevelMesh`).

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck (`enkimute` / `ganja.js`).

---

## 1. Supported Algebras, Conventions & Modes

- Arbitrary Clifford/Geometric Algebra `Cl(p, q, r)` (`p, q, r : UInt8`, optional `conformalWitt : Bool` for native `S"∞∅+…+"`).
- First-class built-ins:
  - `STA` `Cl(3,1)` (`S"-+++"`, preserving `ALOK-950` exact invariants)
  - `R3` `Cl(3,0,0)` (`ℝ3`, including exact R3 rational rotor checks)
  - `PGA2` `Cl(2,0,1)` (`D"0,1,1"`), `PGA3` `Cl(3,0,1)` (`D"0,1,1,1"`)
  - `CGA2` `S"∞∅++"` / `Cl(3,1)`, `CGA3` `S"∞∅+++"` / `Cl(4,1)`
  - `Complex` `Cl(0,1)`, `Dual` `Cl(0,0,1)`, `Quaternion` `Cl(0,2)`
- **PGA3 Motor Wire Order**: Always **ganja order** `(s, e01, e02, e03, e12, e13, e23, e0123)` (NOT bitmask order where `e12` precedes `e03`). Consistent across `Scene`, `CABI`, Web, and visionOS.
- **Triangle Winding**: All mesh `indices` use **right-handed CCW front-face winding** (matching WebGL2/WebGPU/RealityKit default front-face culling).
- **Handle Hit-Testing**: `handleId = 0` is a **valid** handle ID; clients MUST gate hit-testing on the `draggable` flag bit, never on `handleId != 0`.
- `modeKind : UInt8`: `0 = CoffeeShop`, `1 = Wedge2D`, `2 = Wedge3D`, `3 = Calculator`, `4 = Surface`.

---

## 2. Binary Frame Wire Layout (`GSIR` v1 — Little-Endian, **8-Byte Aligned Sections**)

### 2.1 Fixed Header (64 bytes, 8-byte aligned)

| Offset | Type | Field | Description |
|---:|---|---|---|
| `0` | `u32` | `magic` | `0x52495347` (`"GSIR"` ASCII) |
| `4` | `u16` | `version` | `1` |
| `6` | `u16` | `flags` | bit0=`is2D`, bit1=`gridEnabled`, bit2=`darkTheme`, bit3=`hasWedgeHud`, bit4=`hasCalcState`, bit5=`hasContourOverlay`, bit6=`hasOpnsShader` |
| `8` | `u64` | `frameSeq` | Monotonic frame sequence number |
| `16` | `f32` | `simTime` | Simulation clock in seconds |
| `20` | `u8[4]` | `sigMode` | `[p, q, r, modeKind]` |
| `24` | `f32` | `gridSize` | Half-extent of world coordinate grid |
| `28` | `u32` | `sectionCount` | Number of 16-byte directory entries following header |
| `32` | `u32` | `totalByteLen` | Total frame length in bytes (multiple of 8) |
| `36` | `u32` | `metaJsonOffset` | **8-byte aligned** offset to UTF-8 JSON metadata chunk |
| `40` | `u32` | `metaJsonLen` | Exact UTF-8 byte length of JSON metadata (`0` = metadata unchanged since last frame!) |
| `44` | `u8[20]` | `reserved` | Zero-filled |

### 2.2 Section Directory (`sectionCount × 16` bytes at offset `64`)

Each entry: `{ kind : u32, count : u32, byteOffset : u32, byteLen : u32 }`. Every `byteOffset` is **8-byte aligned** (safe for JS `BigUint64Array` and ARM64 Swift `load(as: UInt64.self)`). Unknown section kinds MUST be safely skipped by clients.

### 2.3 Packed Binary Sections

All vectors are right-handed 3D Euclidean `(x, y, z)`; colors are linear/sRGB `rgba : f32[4]` in `[0, 1]`; `labelIdx = 0xFFFFFFFF` means no label.

| Kind | Name | Record Stride & Exact Layout (all LE `f32`/`u32`/`u64`) |
|---:|---|---|
| `0x01` | `CAMERA` | `112 B` (`count=1`): `motor: f32[8]` `(s,e01,e02,e03,e12,e13,e23,e0123)`, `viewMat4: f32[16]` (col-major), `fovDeg: f32`, `distance: f32`, `orthoScale: f32`, `flags: u32` (`b0=isOrtho`) |
| `0x02` | `POINTS` | `44 B × N`: `handleId: u32`, `flags: u32` (b0=draggable, b1=selected, b2=target, b3=hint, b4=hollow), `pos: f32[3]`, `radius: f32`, `rgba: f32[4]`, `labelIdx: u32` |
| `0x03` | `SEGMENTS` | `48 B × N`: `a: f32[3]`, `b: f32[3]`, `width: f32`, `rgba: f32[4]`, `flags: u32` (b0=dashed, b1=arrow, b2=draggable, b3=selected, b4=target, b5=hint; hi16=`handleId`) |
| `0x04` | `LINES` | `52 B × N`: `origin: f32[3]`, `dir: f32[3]` (unit), `clip: f32`, `width: f32`, `rgba: f32[4]`, `flags: u32` (b0=dashed, b1=draggable, b2=selected, b3=target, b4=hint; hi16=`handleId`) |
| `0x05` | `PLANES` | `64 B × N`: `center: f32[3]`, `u: f32[3]`, `v: f32[3]` (orthonormal tangent basis), `extent: f32`, `rgba: f32[4]`, `flags: u32` (b0=gridLines, b1=draggable, b2=selected, b3=target, b4=hint; hi16=`handleId`), `labelIdx: u32` |
| `0x06` | `CIRCLES` | `68 B × N`: `center: f32[3]`, `u: f32[3]`, `v: f32[3]`, `radius: f32`, `width: f32`, `rgba: f32[4]`, `flags: u32` (b0=imaginary/dashed), `labelIdx: u32` |
| `0x07` | `SPHERES` | `40 B × N`: `center: f32[3]`, `radius: f32`, `rgba: f32[4]`, `flags: u32` (b0=imaginary/wireframe), `labelIdx: u32` |
| `0x08` | `POINT_PAIRS` | `48 B × N`: `p1: f32[3]`, `p2: f32[3]`, `radius: f32`, `rgba: f32[4]`, `flags: u32` (b0=imaginary/hollow, b1=showLink) |
| `0x09` | `BIVECTOR_DISKS` | `60 B × N`: `origin: f32[3]`, `u: f32[3]`, `v: f32[3]`, `area: f32`, `rgba: f32[4]`, `flags: u32` (b0=parallelogram[0]/disk[1], b1=orientationArrow) |
| `0x0A` | `MESH_REFS` | `136 B × N` (8-byte aligned): `meshId: u64`, `dirtyHash: u64`, `motor: f32[8]`, `modelMat4: f32[16]` (col-major), `rgba: f32[4]`, `flags: u32` (b0=wireframe, b1=doubleSided, b2=useVertexColors), `pad: u32` |
| `0x0B` | `MESH_ASSETS` | Variable (`count` meshes, delta-uploaded only on new/changed `dirtyHash`, **each mesh record padded to 8-byte boundary**): per mesh `32 B` header `{ meshId: u64, dirtyHash: u64, vertCount: u32, idxCount: u32, flags: u32 (b0=hasColors), pad: u32 }` followed by `positions: f32[vertCount*3]`, `normals: f32[vertCount*3]`, optional `colors: f32[vertCount*4]`, `indices: u32[idxCount]` (CCW front-face winding), plus `4 B` zero pad if `idxCount` is odd! |
| `0x0C` | `CURVES` | Variable (`count` polylines): per curve `28 B` header `{ ptCount: u32, width: f32, rgba: f32[4], flags: u32 (b0=closed, b1=dashed) }` followed by `xyz: f32[ptCount*3]` |
| `0x0D` | `FLOW_PARTICLES` | Variable (`count` fields): per field `28 B` header `{ particleCount: u32, pointSize: f32, rgba: f32[4], speed: f32 }` followed by `starts: f32[particleCount*3]`, `ends: f32[particleCount*3]` |
| `0x0E` | `LABELS` | `36 B × N`: `pos: f32[3]`, `rgba: f32[4]`, `textIdx: u32`, `flags: u32` (b0=isLatex, b1=billboard) |
| `0x0F` | `CONTOUR_OVERLAY` | Single block: `24 B` header `{ minX, maxX, minY, maxY: f32, curveCount: u32, intersectionCount: u32 }`, then `curveCount` 2D polylines (`28 B` header `{ ptCount: u32, rgba: f32[4], width: f32, flags: u32 }` + `xy: f32[ptCount*2]`), then `intersectionCount` points (`28 B` each: `{ x, y: f32, rgba: f32[4], labelIdx: u32 }`) |
| `0x10` | `OPNS_UNIFORMS` | Variable (`count` implicit blades): per item `44 B` header `{ shaderIdx: u32, grade: u32, coeffCount: u32, thresh: f32, maxSteps: u32, stepSize: f32, rgba: f32[4], flags: u32 (b0=isIPNS) }` followed by `coeffs: f32[coeffCount]` |
| `0x11` | `INSPECT_COEFFS` | Variable (`count` entries): per entry `12 B` header `{ entryIdx: u32, grade: u32, coeffCount: u32 }` followed by `coeffs: f32[coeffCount]` |

---

## 3. UTF-8 JSON Metadata Chunk (`metaJson`, Init-Only Zero-Dep Emitter)

When `metaJsonLen == 0`, clients retain the previously received `metaJson` (zero JSON parse per frame at 90fps!). When `opnsShaders` omits previously sent shader bodies (sending only `{"hash":"..."}`), clients look up the cached compiled shader by `hash`.

No `Lean.Data.Json` dependency in runtime! Emitted by `Grassmann/Scene/Json.lean`.

```json
{
  "version": 1,
  "algebra": {
    "name": "PGA3",
    "p": 3, "q": 0, "r": 1,
    "conformalWitt": false,
    "basisNames": ["1", "e0", "e1", "e2", "e3", "e01", "..."],
    "basisMetric": [1, 0, 1, 1, 1, 0, "..."]
  },
  "presetId": "pga3d_slicing",
  "title": "3D PGA Mesh Slicing",
  "labels": ["Cut Plane", "Contour"],
  "inspect": [
    { "idx": 0, "name": "cut", "grade": 1, "formatted": "0.5e0 + 1.0e2", "editable": true }
  ],
  "opnsShaders": [
    { "hash": "cga3_g4_opns", "wgsl": "...", "glsl": "...", "msl": "..." }
  ],
  "calc": {
    "mode": "STA",
    "display": "1.0 + 0.5e12",
    "history": ["A = e1 + e2"],
    "registers": [{ "slot": "x1", "formatted": "..." }]
  },
  "wedge": {
    "is3D": false, "level": 7, "totalLevels": 16,
    "title": "Find the orthocenter",
    "goal": "Reconstruct the red target point",
    "tutorialText": "",
    "moves": 3, "score": 958, "elapsedMs": 12400,
    "lastOp": "join", "previewOp": "", "hintText": "Drag A & B apart",
    "solved": false, "canUndo": true
  },
  "diagnostics": []
}
```

---

## 4. Client → Lean `InputEvent` Protocol (Binary & JSON)

### 4.1 Binary `InputEvent` Fast Path (for 60–90fps interactive gestures / ticks)
Header `4 B`: `{ kind : u8, flags : u8 (b0=forceFullSnapshot), payloadLen : u16 }`:
- `0x01 DragHandle`: `handleId: u32, x: f32, y: f32, z: f32` (16 B)
- `0x02 Tick`: `dt: f32, timeSec: f32` (8 B)
- `0x04 EditCoeff`: `entryIdx: u32, bladeIdx: u32, value: f32` (12 B)
- `0x06 WedgeGesture`: `idA: u32, idB: u32, dirA: f32[3], dirB: f32[3], holdA: u8, holdB: u8, flags: u16 (b0=isPreview)` (36 B). Note: Lean derives `hold` from `‖dir‖ < 0.1` (or explicit spatial pinch-hold bit) and computes `isPreview` without mutating `moves`!
- `0x07 WedgeAction`: `action: u8 (0=undo,1=reset,2=next,3=prev,4=toggle3D,5=hint,6=gotoLevel), pad: u8[3], arg: u32` (8 B)
- `0x09 SetCamera`: `motor: f32[8], fovDeg: f32, distance: f32` (40 B)
- `0x0A SlicePlane`: `motor: f32[8]` (32 B)
- `0x0C Snapshot`: empty payload (`0 B`) — forces full `MESH_ASSETS` + `metaJson` + `opnsShaders` emission.

### 4.2 JSON `InputEvent` Control Path (all events, incl. strings; optional `"forceFullSnapshot": true`)
- `{"op":"dragHandle","id":1,"pos":[x,y,z]}`
- `{"op":"tick","dt":0.016,"t":1.23}`
- `{"op":"evalScript","algebra":"PGA3","code":"..."}`
- `{"op":"evalSurface","expr":"sin(x*2+t)*cos(y*2)","bounds":[-2,2,-2,2],"gridN":48}`
- `{"op":"editCoeff","entryIdx":0,"bladeIdx":1,"val":0.5}`
- `{"op":"loadPreset","id":"pga3d_slicing"}`
- `{"op":"wedgeGesture","idA":0,"idB":1,"dirA":[dx,dy,dz],"dirB":[dx,dy,dz],"holdA":false,"holdB":false,"isPreview":false}`
- `{"op":"wedgeAction","action":"undo|reset|next|prev|toggle3D|hint|goto","arg":0}`
- `{"op":"calcKey","key":"..."}` / `{"op":"calcEval","mode":"STA","expr":"..."}`
- `{"op":"setCamera","motor":[...],"fovDeg":45,"distance":5}`
- `{"op":"slicePlane","motor":[...]}`
- `{"op":"evalEquations","equations":["x^2+y^2-1","y-x"],"bounds":[-2,2,-2,2],"gridN":48}`
- `{"op":"snapshot"}`

---

## 5. C ABI Contract (Init-Only, Caller-Owned Buffer, Idempotent Read)

```c
#define GSIR_OK             0
#define GSIR_ERR_BAD_HANDLE -1
#define GSIR_ERR_BAD_INPUT  -2
#define GSIR_ERR_BUF_SMALL  -3   /* *outLen receives required byte size */

uint64_t grassmann_studio_create(void);
void     grassmann_studio_destroy(uint64_t session);

/* Applies event ONCE, caches encoded GSIR frame on session, copies into outBuf.
 * If outCap < frameSize, returns GSIR_ERR_BUF_SMALL with *outLen = frameSize;
 * caller grows outBuf and calls grassmann_studio_get_frame (NEVER re-dispatches!). */
int32_t  grassmann_studio_dispatch_bin(
           uint64_t session,
           const uint8_t* eventBuf, uint32_t eventLen,
           uint8_t* outBuf, uint32_t outCap, uint32_t* outLen);
int32_t  grassmann_studio_dispatch_json(
           uint64_t session,
           const char* eventJson, uint32_t eventLen,
           uint8_t* outBuf, uint32_t outCap, uint32_t* outLen);

/* Idempotent copy of the session's last encoded GSIR frame (zero state mutation). */
int32_t  grassmann_studio_get_frame(
           uint64_t session,
           uint8_t* outBuf, uint32_t outCap, uint32_t* outLen);
```
