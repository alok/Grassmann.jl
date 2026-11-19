/**
 * wasm/grassmann_wasm.mjs — Clean zero-dep ES module loader for compiled
 * Lean 4.36 Grassmann.lean WebAssembly (`grassmann.wasm`).
 *
 * Exposes:
 *   - `loadGrassmannWasm(opts)` -> `GrassmannWasm`
 *   - `wasm.createStudioSession()` -> `StudioSession` speaking exact GSIR v1
 *     with reusable pre-allocated WASM scratch buffers (zero per-frame malloc!)
 *   - Direct typed-array GA kernels (`staMul`, `r3ApplyRationalRotor`,
 *     `pga3MotorCompose`, `pga3MotorApplyXYZBatch`, `cga3Up`, `clMul`, ...)
 */

const GSIR_OK = 0;
const GSIR_ERR_BUF_SMALL = -3;

export class StudioSession {
  constructor(mod, sid, initialCap = 262144) {
    this.mod = mod;
    this.sid = sid; // BigInt (uint64_t)
    this.outCap = initialCap;
    this.outPtr = mod._malloc(this.outCap);
    this.inCap = 4096;
    this.inPtr = mod._malloc(this.inCap);
    this.outLenPtr = mod._malloc(4);
    this._encoder = new TextEncoder();
    this._destroyed = false;
  }

  _ensureIn(len) {
    if (len > this.inCap) {
      this.mod._free(this.inPtr);
      this.inCap = Math.max(len, this.inCap * 2);
      this.inPtr = this.mod._malloc(this.inCap);
    }
  }

  _ensureOut(len) {
    if (len > this.outCap) {
      this.mod._free(this.outPtr);
      this.outCap = Math.max(len, this.outCap * 2);
      this.outPtr = this.mod._malloc(this.outCap);
    }
  }

  _copyOut(len) {
    const view = new Uint8Array(this.mod.HEAPU8.buffer, this.outPtr, len);
    return view.slice(); // Detached ArrayBuffer-backed copy safe across memory growth
  }

  /** Idempotently read the current cached GSIR v1 frame as Uint8Array. */
  getFrame() {
    if (this._destroyed) throw new Error("StudioSession already destroyed");
    let rc = this.mod._grassmann_studio_get_frame(
      this.sid, this.outPtr, this.outCap, this.outLenPtr
    );
    let len = this.mod.HEAPU32[this.outLenPtr >>> 2];
    if (rc === GSIR_ERR_BUF_SMALL) {
      this._ensureOut(len);
      rc = this.mod._grassmann_studio_get_frame(
        this.sid, this.outPtr, this.outCap, this.outLenPtr
      );
      len = this.mod.HEAPU32[this.outLenPtr >>> 2];
    }
    if (rc !== GSIR_OK) throw new Error(`grassmann_studio_get_frame failed: ${rc}`);
    return this._copyOut(len);
  }

  /** Dispatch a packed binary GSIR InputEvent (Uint8Array) -> Uint8Array GSIR v1 frame. */
  dispatchBin(eventBytes) {
    if (this._destroyed) throw new Error("StudioSession already destroyed");
    this._ensureIn(eventBytes.byteLength);
    this.mod.HEAPU8.set(eventBytes, this.inPtr);
    let rc = this.mod._grassmann_studio_dispatch_bin(
      this.sid, this.inPtr, eventBytes.byteLength,
      this.outPtr, this.outCap, this.outLenPtr
    );
    let len = this.mod.HEAPU32[this.outLenPtr >>> 2];
    if (rc === GSIR_ERR_BUF_SMALL) {
      this._ensureOut(len);
      /* Idempotent read of cached frame — never double-mutates! */
      rc = this.mod._grassmann_studio_get_frame(
        this.sid, this.outPtr, this.outCap, this.outLenPtr
      );
      len = this.mod.HEAPU32[this.outLenPtr >>> 2];
    }
    if (rc !== GSIR_OK) throw new Error(`grassmann_studio_dispatch_bin failed: ${rc}`);
    return this._copyOut(len);
  }

  /** Dispatch a JSON InputEvent (string or object) -> Uint8Array GSIR v1 frame. */
  dispatchJson(event) {
    if (this._destroyed) throw new Error("StudioSession already destroyed");
    const jsonStr = typeof event === "string" ? event : JSON.stringify(event);
    const bytes = this._encoder.encode(jsonStr);
    this._ensureIn(bytes.byteLength);
    this.mod.HEAPU8.set(bytes, this.inPtr);
    let rc = this.mod._grassmann_studio_dispatch_json(
      this.sid, this.inPtr, bytes.byteLength,
      this.outPtr, this.outCap, this.outLenPtr
    );
    let len = this.mod.HEAPU32[this.outLenPtr >>> 2];
    if (rc === GSIR_ERR_BUF_SMALL) {
      this._ensureOut(len);
      rc = this.mod._grassmann_studio_get_frame(
        this.sid, this.outPtr, this.outCap, this.outLenPtr
      );
      len = this.mod.HEAPU32[this.outLenPtr >>> 2];
    }
    if (rc !== GSIR_OK) throw new Error(`grassmann_studio_dispatch_json failed: ${rc}`);
    return this._copyOut(len);
  }

  destroy() {
    if (this._destroyed) return;
    this._destroyed = true;
    this.mod._grassmann_studio_destroy(this.sid);
    this.mod._free(this.outPtr);
    this.mod._free(this.inPtr);
    this.mod._free(this.outLenPtr);
  }
}

export class GrassmannWasm {
  constructor(mod) {
    this.mod = mod;
    // Reusable scratch buffers for zero-malloc direct GA calls (up to 64 doubles each)
    this._a = mod._malloc(64 * 8);
    this._b = mod._malloc(64 * 8);
    this._o = mod._malloc(64 * 8);
  }

  version() {
    return this.mod._grassmann_cabi_version() >>> 0;
  }

  createStudioSession() {
    const sid = this.mod._grassmann_studio_create();
    if (!sid) throw new Error("grassmann_studio_create returned 0");
    return new StudioSession(this.mod, sid);
  }

  _callBin(fn, a, b, nIn, nOut = nIn) {
    this.mod.HEAPF64.set(a, this._a >>> 3);
    this.mod.HEAPF64.set(b, this._b >>> 3);
    const rc = fn(this._a, this._b, this._o);
    if (rc !== GSIR_OK) throw new Error(`WASM kernel error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + nOut);
  }

  staMul(a, b) { return this._callBin(this.mod._grassmann_sta_mul, a, b, 16); }
  staWedge(a, b) { return this._callBin(this.mod._grassmann_sta_wedge, a, b, 16); }
  staSandwich(r, x) { return this._callBin(this.mod._grassmann_sta_sandwich, r, x, 16); }
  staSpatialWedge(a, b) { return this._callBin(this.mod._grassmann_sta_spatial_wedge, a, b, 16, 12); }
  staBoostRotor(phi, ux, uy, uz) {
    const rc = this.mod._grassmann_sta_boost_rotor(phi, ux, uy, uz, this._o);
    if (rc !== GSIR_OK) throw new Error(`staBoostRotor error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 16);
  }

  r3ApplyRationalRotor(rotor4, xyz) {
    this.mod.HEAPF64.set(rotor4, this._a >>> 3);
    this.mod.HEAPF64.set(xyz, this._b >>> 3);
    const rc = this.mod._grassmann_r3_apply_rational_rotor(this._a, this._b, this._o);
    if (rc !== GSIR_OK) throw new Error(`r3ApplyRationalRotor error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 4);
  }

  pga3MakeRotor(ax, ay, az, angle) {
    const rc = this.mod._grassmann_pga3_make_rotor(ax, ay, az, angle, this._o);
    if (rc !== GSIR_OK) throw new Error(`pga3MakeRotor error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 8);
  }

  pga3MakeTranslator(tx, ty, tz) {
    const rc = this.mod._grassmann_pga3_make_translator(tx, ty, tz, this._o);
    if (rc !== GSIR_OK) throw new Error(`pga3MakeTranslator error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 8);
  }

  pga3MotorCompose(a, b) { return this._callBin(this.mod._grassmann_pga3_motor_compose, a, b, 8); }
  pga3MotorToMat4(m) {
    this.mod.HEAPF64.set(m, this._a >>> 3);
    const rc = this.mod._grassmann_pga3_motor_to_mat4(this._a, this._o);
    if (rc !== GSIR_OK) throw new Error(`pga3MotorToMat4 error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 16);
  }

  cga3Up(x, y, z) {
    const rc = this.mod._grassmann_cga3_up(x, y, z, this._o);
    if (rc !== GSIR_OK) throw new Error(`cga3Up error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 32);
  }

  cga3Down(p) {
    this.mod.HEAPF64.set(p, this._a >>> 3);
    const rc = this.mod._grassmann_cga3_down(this._a, this._o);
    if (rc !== GSIR_OK) throw new Error(`cga3Down error ${rc}`);
    return this.mod.HEAPF64.slice(this._o >>> 3, (this._o >>> 3) + 3);
  }
}

/**
 * Load and initialize the compiled Lean 4.36 Grassmann WASM module.
 * Works in browsers (Vite/Vercel) and Node.js.
 */
export async function loadGrassmannWasm(moduleOpts = {}) {
  const { default: createGrassmannRaw } = await import("./grassmann_raw.mjs");
  const mod = await createGrassmannRaw(moduleOpts);
  const rc = mod._grassmann_initialize();
  if (rc !== GSIR_OK) {
    throw new Error(`grassmann_initialize failed with status ${rc}`);
  }
  return new GrassmannWasm(mod);
}
