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

// 5. Full Preset Catalog (ALL 19 CoffeeShop Presets!)
const catalog = g.presetCatalog();
assert.ok(Array.isArray(catalog) && catalog.length >= 19, `expected >= 19 presets, got ${catalog.length}`);
console.log(`[wasm test] loaded full Lean preset catalog: ${catalog.length} presets`);

// 6. Full Unified Grassmann.Studio Session in WASM!
const sess = g.createStudioSession();
const f0 = parseGSIR(sess.getFrame());
assert.equal(f0.frameSeq, 1n);
assert.equal(f0.meta.presetId, "pga3d_slicing");
assert.ok(f0.sections.some(s => s.kind === 0x0B), "initial sculpted bunny frame has MESH_ASSETS");
assert.ok(f0.sections.some(s => s.kind === 0x0F), "pga3d_slicing has CONTOUR_OVERLAY");

// Exercise EVERY SINGLE preset in the catalog in compiled Lean WASM!
let foundOpnsGlsl = false;
for (const item of catalog) {
  const fr = parseGSIR(sess.dispatchJson({ op: "loadPreset", id: item.id }));
  assert.ok(fr.meta !== null, `meta present for preset ${item.id}`);
  assert.equal(fr.meta.presetId, item.id, `presetId matches ${item.id}`);
  if (item.id === "cga3d_opns_cyclide") {
    assert.ok(fr.meta.opnsShaders && fr.meta.opnsShaders.length > 0, "OPNS shader emitted");
    assert.ok(fr.meta.opnsShaders[0].glsl.includes("product_len"), "GLSL OPNS shader valid");
    assert.ok(fr.meta.opnsShaders[0].wgsl.includes("@fragment"), "WGSL OPNS shader valid");
    assert.ok(fr.meta.opnsShaders[0].msl.includes("metal_stdlib"), "MSL OPNS shader valid");
    foundOpnsGlsl = true;
  }
}
assert.ok(foundOpnsGlsl, "verified cga3d_opns_cyclide WGSL/GLSL/MSL shader emission in WASM");

// Hot binary Tick on static-mesh pga3d_objects -> omits BOTH MESH_ASSETS & metaJson!
const obj0 = parseGSIR(sess.dispatchJson({ op: "loadPreset", id: "pga3d_objects" }));
assert.ok(obj0.sections.some(s => s.kind === 0x0B), "pga3d_objects initial load has MESH_ASSETS");
const tick = new Uint8Array(12);
const tdv = new DataView(tick.buffer);
tick[0] = 0x02; tick[1] = 0x00;
tdv.setUint16(2, 8, true);
tdv.setFloat32(4, 0.016, true);
tdv.setFloat32(8, 0.5, true);
const obj1 = parseGSIR(sess.dispatchBin(tick));
assert.equal(obj1.metaJsonLen, 0, "hot tick omits unchanged metaJson");
assert.ok(!obj1.sections.some(s => s.kind === 0x0B), "hot tick omits cached MESH_ASSETS");

// Wedge 2D (L1 & L9) + Wedge 3D (L10 & L16) + live WedgeGesture preview & commit!
for (const [preset, lvl] of [["wedge_2d", 1], ["wedge_2d", 9], ["wedge_3d", 10], ["wedge_3d", 16]]) {
  sess.dispatchJson({ op: "loadPreset", id: preset });
  const wl = parseGSIR(sess.dispatchJson({ op: "wedgeAction", action: "goto", arg: lvl }));
  assert.ok(wl.meta.wedge, `wedge HUD present for L${lvl}`);
  assert.equal(wl.meta.wedge.level, lvl, `wedge level ${lvl}`);
}
// Binary WedgeGesture on Level 1 (givens A=id 2 at (-1,0), B=id 3 at (1,0.5)):
// Push A & B apart with isPreview=1 (ghost Join preview, moves stays 0!)
sess.dispatchJson({ op: "loadPreset", id: "wedge_2d" });
const wg = new Uint8Array(40);
const wdv = new DataView(wg.buffer);
wg[0] = 0x06; wg[1] = 0; wdv.setUint16(2, 36, true);
wdv.setUint32(4, 2, true); wdv.setUint32(8, 3, true);
wdv.setFloat32(12, -1.0, true); wdv.setFloat32(24, 1.0, true);
wdv.setUint16(38, 1, true); // isPreview = 1
const wPrev = parseGSIR(sess.dispatchBin(wg));
assert.ok(wPrev.meta === null || wPrev.meta.wedge.moves === 0, "WedgeGesture isPreview does not increment moves");
// Commit Join gesture (isPreview = 0) solves Level 1 in 1 move!
wdv.setUint16(38, 0, true);
const wCommit = parseGSIR(sess.dispatchBin(wg));
assert.ok(wCommit.meta && wCommit.meta.wedge.moves === 1, "WedgeGesture commit increments moves to 1");
assert.equal(wCommit.meta.wedge.solved, true, "WedgeGesture Join solves Level 1!");

// Live evalScript, evalSurface, evalEquations (marching-triangles contours!), calcEval, editCoeff
const sScript = parseGSIR(sess.dispatchJson({ op: "evalScript", algebra: "PGA3", code: "let P = point(1,2,3); let Q = point(-1,0,1); let L = P & Q" }));
assert.equal(sScript.meta.diagnostics.length, 0, "evalScript zero diagnostics");
assert.ok(sScript.sections.some(s => s.kind === 0x04), "evalScript emitted PGA3 line");

const sSurf = parseGSIR(sess.dispatchJson({ op: "evalSurface", expr: "sin(x*x+y*y-t)*0.5", bounds: [-2, 2, -2, 2], gridN: 24 }));
assert.ok(sSurf.sections.some(s => s.kind === 0x0B), "evalSurface emitted CCW mesh");

const sEq = parseGSIR(sess.dispatchJson({ op: "evalEquations", equations: ["x^2+y^2-1", "y-x"], bounds: [-2, 2, -2, 2], gridN: 32 }));
assert.ok(sEq.sections.some(s => s.kind === 0x0F), "evalEquations emitted marching-triangles CONTOUR_OVERLAY");

const sCalc = parseGSIR(sess.dispatchJson({ op: "calcEval", mode: "STA", expr: "e1 * e2" }));
assert.ok(sCalc.meta.calc && sCalc.meta.calc.display.length > 0, "calcEval produced display");

// Benchmarks in WASM!
const N_MOTOR = 200000;
const t0 = performance.now();
for (let i = 0; i < N_MOTOR; i++) {
  g.mod._grassmann_pga3_motor_compose(g._a, g._b, g._o);
}
const dtMotor = performance.now() - t0;
console.log(`[wasm bench] pga3_motor_compose:     ${((dtMotor * 1e6) / N_MOTOR).toFixed(1)} ns/call (${N_MOTOR} iters)`);

sess.dispatchJson({ op: "loadPreset", id: "sta_lorentz_boost" });
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
console.log("[wasm test] ALL 19 PRESETS + WEDGE 2D/3D + EVAL + CONTOURS + OPNS SHADERS PASSED IN WASM!");
