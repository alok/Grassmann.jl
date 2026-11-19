import assert from "node:assert/strict";
import { loadGrassmannWasm } from "./dist/grassmann_wasm.mjs";

function assertNear(a, b, tol = 1e-10, msg = "") {
  assert.ok(Math.abs(a - b) <= tol, `${msg}: got ${a}, expected ${b} (tol ${tol})`);
}

function parseGSIR(bytes) {
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  assert.equal(dv.getUint32(0, true), 0x52495347, "GSIR magic");
  assert.equal(dv.getUint16(4, true), 1, "GSIR version");
  const flags = dv.getUint16(6, true);
  const frameSeq = dv.getBigUint64(8, true);
  const simTime = dv.getFloat32(16, true);
  const sectionCount = dv.getUint32(28, true);
  const totalByteLen = dv.getUint32(32, true);
  const metaJsonOffset = dv.getUint32(36, true);
  const metaJsonLen = dv.getUint32(40, true);
  assert.equal(totalByteLen, bytes.byteLength, "totalByteLen");
  const sections = [];
  for (let i = 0; i < sectionCount; i++) {
    const off = 64 + i * 16;
    const kind = dv.getUint32(off, true);
    const count = dv.getUint32(off + 4, true);
    const byteOffset = dv.getUint32(off + 8, true);
    const byteLen = dv.getUint32(off + 12, true);
    assert.equal(byteOffset % 8, 0, `section 0x${kind.toString(16)} byteOffset 8-byte aligned`);
    if (kind === 0x0A || kind === 0x0B) {
      // Verify BigUint64Array slicing does not throw RangeError (#17 fix #1)!
      const u64 = new BigUint64Array(bytes.buffer, bytes.byteOffset + byteOffset, 2);
      assert.ok(u64[0] > 0n, "meshId > 0");
    }
    sections.push({ kind, count, byteOffset, byteLen });
  }
  let meta = null;
  if (metaJsonLen > 0) {
    assert.equal(metaJsonOffset % 8, 0, "metaJsonOffset 8-byte aligned");
    const txt = new TextDecoder().decode(
      bytes.subarray(metaJsonOffset, metaJsonOffset + metaJsonLen)
    );
    meta = JSON.parse(txt);
  }
  return { flags, frameSeq, simTime, sections, meta, metaJsonLen };
}

const g = await loadGrassmannWasm();
assert.equal(g.version(), 0x00020000);

// 1. STA Cl(3,1) -+++ boost invariance
const boost = g.staBoostRotor(0.75, 1, 0, 0);
const v = new Float64Array(16);
v[1] = 2.0; v[2] = 0.5; v[4] = -0.3; v[8] = 0.7;
const origNorm = -v[1]*v[1] + v[2]*v[2] + v[4]*v[4] + v[8]*v[8];
const vb = g.staSandwich(boost, v);
const vb2 = g.staMul(vb, vb);
assertNear(vb2[0], origNorm, 1e-11, "WASM STA Lorentz invariance");

// 2. R3 rational rotor
const r3Out = g.r3ApplyRationalRotor([1, 0.5, -0.25, 0.75], [1, 2, -3]);
assertNear(r3Out[0]**2 + r3Out[1]**2 + r3Out[2]**2, 14, 1e-12, "WASM R3 rational rotor norm");

// 3. PGA3 motor compose + mat4
const rot = g.pga3MakeRotor(0, 0, 1, Math.PI / 2);
const tr = g.pga3MakeTranslator(1, 2, 3);
const mot = g.pga3MotorCompose(tr, rot);
const mat = g.pga3MotorToMat4(mot);
assertNear(mat[12], 1, 1e-12, "WASM PGA3 mat4 tx");
assertNear(mat[13], 2, 1e-12, "WASM PGA3 mat4 ty");
assertNear(mat[14], 3, 1e-12, "WASM PGA3 mat4 tz");

// 4. CGA3 up/down roundtrip
const p = g.cga3Up(1.5, -2.25, 0.75);
const back = g.cga3Down(p);
assertNear(back[0], 1.5, 1e-12, "WASM CGA3 down.x");
assertNear(back[1], -2.25, 1e-12, "WASM CGA3 down.y");
assertNear(back[2], 0.75, 1e-12, "WASM CGA3 down.z");

// 5. Full GSIR v1 StudioSession lifecycle in compiled Lean WASM!
const sess = g.createStudioSession();
const f0 = parseGSIR(sess.getFrame());
assert.equal(f0.frameSeq, 1n);
assert.equal(f0.meta.presetId, "pga3d_slicing");
assert.ok(f0.sections.some(s => s.kind === 0x0B), "initial frame has MESH_ASSETS");
assert.ok(f0.sections.some(s => s.kind === 0x0F), "pga3d_slicing has CONTOUR_OVERLAY");

// Hot binary Tick -> delta omits MESH_ASSETS & metaJsonLen == 0
const tick = new Uint8Array(12);
const tdv = new DataView(tick.buffer);
tick[0] = 0x02; tick[1] = 0x00;
tdv.setUint16(2, 8, true);
tdv.setFloat32(4, 0.016, true);
tdv.setFloat32(8, 0.5, true);
const f1 = parseGSIR(sess.dispatchBin(tick));
assert.equal(f1.frameSeq, 2n);
assert.equal(f1.metaJsonLen, 0, "hot tick omits unchanged metaJson");
assert.ok(!f1.sections.some(s => s.kind === 0x0B), "hot tick omits cached MESH_ASSETS");

// JSON presets + evalSurface
for (const ev of [
  { op: "loadPreset", id: "sta_wedge_lab" },
  { op: "loadPreset", id: "cga3d_spheres" },
  { op: "loadPreset", id: "r3_rational_rotor" },
  { op: "loadPreset", id: "wedge_2d" },
  { op: "loadPreset", id: "wedge_3d" },
  { op: "evalSurface", expr: "sin(x*x+y*y-t)*0.5", gridN: 24 },
]) {
  const fr = parseGSIR(sess.dispatchJson(ev));
  assert.ok(fr.meta !== null, `meta present for ${JSON.stringify(ev)}`);
}

// Benchmarks in WASM!
const N_MOTOR = 200000;
const t0 = performance.now();
for (let i = 0; i < N_MOTOR; i++) {
  g.mod._grassmann_pga3_motor_compose(g._a, g._b, g._o);
}
const dtMotor = performance.now() - t0;
console.log(`[wasm bench] pga3_motor_compose:     ${((dtMotor * 1e6) / N_MOTOR).toFixed(1)} ns/call (${N_MOTOR} iters)`);

sess.dispatchJson({ op: "loadPreset", id: "sta_wedge_lab" });
const drag = new Uint8Array(20);
const ddv = new DataView(drag.buffer);
drag[0] = 0x01; ddv.setUint16(2, 16, true); ddv.setUint32(4, 0, true);
const N_FRAMES = 5000;
const t1 = performance.now();
let lastSize = 0;
for (let i = 0; i < N_FRAMES; i++) {
  ddv.setFloat32(8, (i % 100) * 0.01, true);
  const frame = sess.dispatchBin(drag);
  lastSize = frame.byteLength;
}
const dtFrames = performance.now() - t1;
console.log(`[wasm bench] studio_drag_gsir_frame: ${((dtFrames * 1e3) / N_FRAMES).toFixed(2)} us/frame (${lastSize} B/frame, ${Math.round(N_FRAMES / (dtFrames / 1000))} fps max)`);

sess.destroy();
console.log("[wasm test] ALL CHECKS PASSED!");
