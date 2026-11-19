import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { loadGrassmannWasm } from "./dist/grassmann_wasm.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// 0. Verify content-fingerprinted wasm-manifest.json + hashed asset load!
const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, "dist/wasm-manifest.json"), "utf8"));
assert.equal(manifest.version, 1, "wasm-manifest version");
assert.equal(manifest.presetCount, 74, "wasm-manifest presetCount");
assert.ok(/^[0-9a-f]{10}$/.test(manifest.hash), "wasm-manifest 10-hex hash");
assert.ok(fs.existsSync(path.join(__dirname, "dist", manifest.wasmFile)), "fingerprinted .wasm exists");
assert.ok(fs.existsSync(path.join(__dirname, "dist", manifest.loaderFile)), "fingerprinted .mjs exists");
{
  const { default: createFp } = await import(`./dist/${manifest.loaderFile}`);
  const fpMod = await createFp();
  assert.equal(fpMod._grassmann_initialize(), 0, "fingerprinted WASM initializes cleanly");
}

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

// 5. Full Preset Catalog (ALL 74 CoffeeShop Presets — 69 + 5 Wave 4B Showcase!)
const catalog = g.presetCatalog();
assert.equal(catalog.length, 74, `expected 74 presets, got ${catalog.length}`);
const uniqueIds = new Set(catalog.map(p => p.id));
assert.equal(uniqueIds.size, 74, "zero duplicate preset IDs across 74-preset catalog");
console.log(`[wasm test] loaded full Lean preset catalog: ${catalog.length} presets (74 unique)`);

// 6. Full Unified Grassmann.Studio Session in WASM!
const sess = g.createStudioSession();
const f0Raw = sess.getFrame();
const f0 = parseGSIR(f0Raw);
assert.equal(f0.frameSeq, 1n);
assert.equal(f0.meta.presetId, "pga3d_slicing");
const meshSec = f0.sections.find(s => s.kind === 0x0B);
const contourSec = f0.sections.find(s => s.kind === 0x0F);
assert.ok(meshSec, "initial sculpted bunny frame has MESH_ASSETS");
assert.ok(contourSec, "pga3d_slicing has CONTOUR_OVERLAY");
// Regression check (#89): verify full 360-deg pi precision -> sculpted bunny spans > 1.4 units
// AND slice contour overlay has non-empty polylines!
{
  const dv = new DataView(f0Raw.buffer, f0Raw.byteOffset, f0Raw.byteLength);
  const vCount = dv.getUint32(meshSec.byteOffset + 16, true);
  let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity, minZ = Infinity, maxZ = -Infinity;
  const posOff = meshSec.byteOffset + 32;
  for (let i = 0; i < vCount; i++) {
    const vx = dv.getFloat32(posOff + i * 12, true);
    const vy = dv.getFloat32(posOff + i * 12 + 4, true);
    const vz = dv.getFloat32(posOff + i * 12 + 8, true);
    if (vx < minX) minX = vx; if (vx > maxX) maxX = vx;
    if (vy < minY) minY = vy; if (vy > maxY) maxY = vy;
    if (vz < minZ) minZ = vz; if (vz > maxZ) maxZ = vz;
  }
  const spanX = maxX - minX, spanY = maxY - minY, spanZ = maxZ - minZ;
  assert.ok(spanX > 1.5 && spanY > 0.9 && spanZ > 0.9, `bunny mesh full 360-deg span expected >(1.5,0.9,0.9), got (${spanX.toFixed(3)}, ${spanY.toFixed(3)}, ${spanZ.toFixed(3)})`);
  const polyCount = dv.getUint32(contourSec.byteOffset + 16, true);
  assert.ok(polyCount > 0, `pga3d_slicing bunny contour has polylines (got ${polyCount})`);
  assert.ok(typeof f0.meta.script === "string" && f0.meta.script.length > 20, "pga3d_slicing populates editable metaJson.script");
  console.log(`[wasm test] sculpted bunny verified: ${vCount} verts, span=(${spanX.toFixed(2)}, ${spanY.toFixed(2)}, ${spanZ.toFixed(2)}), ${polyCount} slice contours, script=${f0.meta.script.length} chars`);
}

// Exercise EVERY SINGLE preset (all 74!) + verify KaTeX formula & summary in compiled Lean WASM!
let foundOpnsGlsl = false;
let showcaseVerified = 0;
for (const item of catalog) {
  const frRaw = sess.dispatchJson({ op: "loadPreset", id: item.id });
  const fr = parseGSIR(frRaw);
  assert.ok(fr.meta !== null, `meta present for preset ${item.id}`);
  assert.equal(fr.meta.presetId, item.id, `presetId matches ${item.id}`);
  assert.ok(typeof fr.meta.formula === "string" && fr.meta.formula.length > 0, `KaTeX formula present for ${item.id}`);
  assert.ok(typeof fr.meta.summary === "string" && fr.meta.summary.length > 0, `summary present for ${item.id}`);
  if (["pga3d_bouncing_cube", "pga3d_double_pendulum", "sta_terrell_penrose", "sta_maxwell_streamlines", "pga3d_hopf_streamlines"].includes(item.id)) {
    assert.ok(Array.isArray(fr.meta.params) && fr.meta.params.length >= 2, `showcase @param sliders present for ${item.id}`);
    if (item.id === "sta_maxwell_streamlines" || item.id === "pga3d_hopf_streamlines") {
      assert.ok(fr.sections.some(s => s.kind === 0x0D), `${item.id} emits 0x0D FLOW_PARTICLES`);
    }
    showcaseVerified++;
  }
  if (item.id === "cga3d_opns_cyclide") {
    assert.ok(fr.meta.opnsShaders && fr.meta.opnsShaders.length > 0, "OPNS shader emitted");
    assert.ok(fr.meta.opnsShaders[0].glsl.includes("uniform mat4 projectionMatrix;"), "GLSL3 has projectionMatrix");
    assert.ok(fr.meta.opnsShaders[0].glsl.includes("product_len"), "GLSL OPNS shader valid");
    assert.ok(fr.meta.opnsShaders[0].wgsl.includes("@fragment"), "WGSL OPNS shader valid");
    assert.ok(fr.meta.opnsShaders[0].msl.includes("gsir_lean_opns_compute"), "MSL OPNS shader valid");
    // Regression check (#89): verify b[4] == 1.0 (quadratic 0.5*(x^2+y^2+z^2) bounded sphere term!)
    const opnsSec = fr.sections.find(s => s.kind === 0x10);
    assert.ok(opnsSec, "cga3d_opns_cyclide has 0x10 OPNS_UNIFORMS");
    const odv = new DataView(frRaw.buffer, frRaw.byteOffset, frRaw.byteLength);
    // OpnsUniforms record: shaderIdx(4)+grade(4)+coeffCount(4)+thresh(4)+maxSteps(4)+stepSize(4)+rgba(16)+flags(4) = 44B header, then float coeffs[]
    const coeffCount = odv.getUint32(opnsSec.byteOffset + 8, true);
    assert.equal(coeffCount, 5, "CGA3 grade-4 sphere has 5 coefficients");
    const b4 = odv.getFloat32(opnsSec.byteOffset + 44 + 4 * 4, true);
    assertNear(b4, 1.0, 1e-5, "cga3d_opns_cyclide b[4] quadratic sphere coeff == 1.0");
    foundOpnsGlsl = true;
  }
}
assert.equal(showcaseVerified, 5, "verified all 5 Wave 4B showstopper physics/relativity/streamline presets");
assert.ok(foundOpnsGlsl, "verified cga3d_opns_cyclide GPUInit WGSL/GLSL3/MSL shader emission in WASM");

// Live @param / setParam verification on sta_terrell_penrose & pga3d_bouncing_cube!
{
  const tp0 = parseGSIR(sess.dispatchJson({ op: "loadPreset", id: "sta_terrell_penrose" }));
  const beta0 = tp0.meta.params.find(p => p.name === "beta");
  assert.ok(beta0, "sta_terrell_penrose exposes beta @param");
  const tp1 = parseGSIR(sess.dispatchJson({ op: "setParam", name: "beta", value: 0.85 }));
  const beta1 = tp1.meta.params.find(p => p.name === "beta");
  assertNear(beta1.value, 0.85, 1e-4, "setParam updated sta_terrell_penrose beta to 0.85");
  const bc0 = parseGSIR(sess.dispatchJson({ op: "loadPreset", id: "pga3d_bouncing_cube" }));
  assert.ok(bc0.meta.params.some(p => p.name === "gravity"), "pga3d_bouncing_cube exposes gravity @param");
  const bc1 = parseGSIR(sess.dispatchJson({ op: "setParam", name: "gravity", value: 15.0 }));
  assertNear(bc1.meta.params.find(p => p.name === "gravity").value, 15.0, 1e-4, "setParam updated gravity to 15.0");
}

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

// Live LiveScript v2 execution: multi-statement + fn + for loop + hex color + reactive DragHandle!
const liveCode = [
  "@basis PGA3",
  "fn mid(a, b) = (a + b) * 0.5",
  "let A = point(-1.0, 0.0, 0.0)",
  "let B = point(1.0, 0.5, 0.0)",
  "let L = A & B",
  "let M = mid(A, B)",
  "let pts = [point(cos(i * 0.8), sin(i * 0.8), 0.2) for i in 0..4]",
  "graph([0x44aaff, A, B, L, M, pts])"
].join("\n");
const sScriptRaw = sess.dispatchJson({ op: "evalScript", algebra: "PGA3", code: liveCode });
const sScript = parseGSIR(sScriptRaw);
assert.equal(sScript.meta.diagnostics.length, 0, "LiveScript v2 zero diagnostics");
assert.ok(sScript.sections.some(s => s.kind === 0x02), "LiveScript v2 emitted draggable points");
assert.ok(sScript.sections.some(s => s.kind === 0x04), "LiveScript v2 emitted PGA3 line L = A & B");
// Reactive DragHandle on script handle 0 (A) updates point coordinates live in WASM!
const ptSecBefore = sScript.sections.find(s => s.kind === 0x02);
const ptDvBefore = new DataView(sScriptRaw.buffer, sScriptRaw.byteOffset, sScriptRaw.byteLength);
const hId0 = ptDvBefore.getUint32(ptSecBefore.byteOffset + 0, true);
const scriptDrag = new Uint8Array(20);
const sddv = new DataView(scriptDrag.buffer);
scriptDrag[0] = 0x01; sddv.setUint16(2, 16, true); sddv.setUint32(4, hId0, true);
sddv.setFloat32(8, 0.75, true); sddv.setFloat32(12, 1.25, true); sddv.setFloat32(16, -0.5, true);
const sDraggedRaw = sess.dispatchBin(scriptDrag);
const sDragged = parseGSIR(sDraggedRaw);
// POINTS record layout: handleId(+0), flags(+4), pos.x(+8), pos.y(+12), pos.z(+16), ...
const ptSecAfter = sDragged.sections.find(s => s.kind === 0x02);
const ptDvAfter = new DataView(sDraggedRaw.buffer, sDraggedRaw.byteOffset, sDraggedRaw.byteLength);
const draggedX = ptDvAfter.getFloat32(ptSecAfter.byteOffset + 8, true);
const draggedY = ptDvAfter.getFloat32(ptSecAfter.byteOffset + 12, true);
const draggedZ = ptDvAfter.getFloat32(ptSecAfter.byteOffset + 16, true);
assertNear(draggedX, 0.75, 1e-4, "LiveScript v2 reactive DragHandle updated point.x");
assertNear(draggedY, 1.25, 1e-4, "LiveScript v2 reactive DragHandle updated point.y");
assertNear(draggedZ, -0.5, 1e-4, "LiveScript v2 reactive DragHandle updated point.z");
// Also verify #pga3d_slicing's editable metaJson.script executes cleanly via evalScript!
const bunnyScriptRes = parseGSIR(sess.dispatchJson({ op: "evalScript", algebra: "PGA3", code: f0.meta.script }));
assert.equal(bunnyScriptRes.meta.diagnostics.length, 0, "#pga3d_slicing metaJson.script executes with 0 diagnostics");

const sSurf = parseGSIR(sess.dispatchJson({ op: "evalSurface", expr: "sin(x*x+y*y-t)*0.5", bounds: [-2, 2, -2, 2], gridN: 24 }));
assert.ok(sSurf.sections.some(s => s.kind === 0x0B), "evalSurface emitted CCW mesh");

const sEq = parseGSIR(sess.dispatchJson({ op: "evalEquations", equations: ["x^2+y^2-1", "y-x"], bounds: [-2, 2, -2, 2], gridN: 32 }));
assert.ok(sEq.sections.some(s => s.kind === 0x0F), "evalEquations emitted marching-triangles CONTOUR_OVERLAY");

// User-typed 3D Implicit Equation (Kuhn Marching Tetrahedra mesh + symmetric bounds + cleared stale contour!)
const gyroidExpr = "cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)";
const tImp0 = performance.now();
const sImpRaw = sess.dispatchJson({ op: "evalImplicit", expr: gyroidExpr, gpuRaymarch: false, gridN: 16 });
const dtImpMesh = performance.now() - tImp0;
const sImpMesh = parseGSIR(sImpRaw);
assert.equal(sImpMesh.meta.diagnostics.length, 0, "evalImplicit mesh zero diagnostics");
assert.ok(!sImpMesh.sections.some(s => s.kind === 0x0F), "evalImplicit cleared stale CONTOUR_OVERLAY");
const gyMeshSec = sImpMesh.sections.find(s => s.kind === 0x0B);
assert.ok(gyMeshSec, "evalImplicit mesh emitted CCW MESH_ASSETS");
{
  const gdv = new DataView(sImpRaw.buffer, sImpRaw.byteOffset, sImpRaw.byteLength);
  const gVerts = gdv.getUint32(gyMeshSec.byteOffset + 16, true);
  let gx0 = Infinity, gx1 = -Infinity, gy0 = Infinity, gy1 = -Infinity, gz0 = Infinity, gz1 = -Infinity;
  const gPos = gyMeshSec.byteOffset + 32;
  for (let i = 0; i < gVerts; i++) {
    const x = gdv.getFloat32(gPos + i * 12, true);
    const y = gdv.getFloat32(gPos + i * 12 + 4, true);
    const z = gdv.getFloat32(gPos + i * 12 + 8, true);
    if (x < gx0) gx0 = x; if (x > gx1) gx1 = x;
    if (y < gy0) gy0 = y; if (y > gy1) gy1 = y;
    if (z < gz0) gz0 = z; if (z > gz1) gz1 = z;
  }
  assert.ok(gx0 < -1.0 && gx1 > 1.0 && gy0 < -1.0 && gy1 > 1.0 && gz0 < -1.0 && gz1 > 1.0,
    `symmetric Gyroid expected spanning [-1,+1]^3, got x=[${gx0.toFixed(2)},${gx1.toFixed(2)}] y=[${gy0.toFixed(2)},${gy1.toFixed(2)}] z=[${gz0.toFixed(2)},${gz1.toFixed(2)}]`);
  // Measure warmed 5x average for bytecode Marching Tetrahedra in WASM!
  const tWarm0 = performance.now();
  for (let k = 0; k < 5; k++) sess.dispatchJson({ op: "evalImplicit", expr: gyroidExpr, gpuRaymarch: false, gridN: 16 });
  const dtWarm = (performance.now() - tWarm0) / 5;
  console.log(`[wasm bench] evalImplicit gyroid 16^3: ${dtWarm.toFixed(2)} ms avg (${dtImpMesh.toFixed(2)} ms cold; ${sImpMesh.meta.inspect[0].formatted}, sym=[${gx0.toFixed(2)},${gx1.toFixed(2)}])`);
}

// User-typed 3D Implicit Equation (GPUInit GLSL3 + WGSL + Metal MSL raymarcher!)
const tGpu0 = performance.now();
const sImpGpu = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: gyroidExpr, gpuRaymarch: true }));
const dtImpGpu = performance.now() - tGpu0;
assert.equal(sImpGpu.meta.diagnostics.length, 0, "evalImplicit gpuRaymarch zero diagnostics");
assert.ok(sImpGpu.sections.some(s => s.kind === 0x10), "evalImplicit gpuRaymarch emitted 0x10 OPNS_UNIFORMS");
assert.ok(sImpGpu.meta.opnsShaders && sImpGpu.meta.opnsShaders.length === 1, "evalImplicit gpuRaymarch emitted opnsShaders[0]");
assert.ok(sImpGpu.meta.opnsShaders[0].glsl.includes("uniform mat4 projectionMatrix;"), "implicit GLSL3 declares projectionMatrix");
assert.ok(sImpGpu.meta.opnsShaders[0].wgsl.includes("@fragment"), "implicit WGSL valid");
assert.ok(sImpGpu.meta.opnsShaders[0].msl.includes("gsir_lean_opns_compute"), "implicit MSL valid");
console.log(`[wasm bench] evalImplicit GPU shader:  ${dtImpGpu.toFixed(2)} ms (GLSL3+WGSL+MSL)`);

// User-typed 3D Parametric Surface
const sParam = parseGSIR(sess.dispatchJson({
  op: "evalParametric",
  fx: "(1.1 + 0.42*cos(v))*cos(u)",
  fy: "0.42*sin(v)",
  fz: "(1.1 + 0.42*cos(v))*sin(u)",
  nu: 32, nv: 18
}));
assert.equal(sParam.meta.diagnostics.length, 0, "evalParametric zero diagnostics");
assert.ok(sParam.sections.some(s => s.kind === 0x0B), "evalParametric emitted CCW MESH_ASSETS");

// Wedge Tutorials (T1..T6 animated cards!) + Procedural Challenge Generator (2D & 3D)
for (const tid of ["T1", "T2", "T3", "T4", "T5", "T6"]) {
  const wt = parseGSIR(sess.dispatchJson({ op: "wedgeTutorial", id: tid }));
  assert.ok(wt.meta && wt.meta.wedge, `wedgeTutorial ${tid} has wedge HUD`);
  assert.ok(wt.sections.some(s => s.kind === 0x03), `wedgeTutorial ${tid} emits animated gesture arrow segments`);
}
for (const [dim, diff, seed] of [[2, 0, 11], [2, 2, 22], [3, 0, 33], [3, 2, 44]]) {
  const wr = parseGSIR(sess.dispatchJson({ op: "wedgeRandom", dim, difficulty: diff, seed }));
  assert.ok(wr.meta && wr.meta.wedge, `wedgeRandom dim=${dim} diff=${diff} has wedge HUD`);
  assert.equal(wr.meta.wedge.is3D, dim === 3, `wedgeRandom is3D matches dim=${dim}`);
}

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
console.log("[wasm test] ALL 74 PRESETS + @PARAM + KATEX + BYTECODE IMPLICIT3D/GPU + LIVESCRIPT V2 + WEDGE PASSED IN WASM!");
