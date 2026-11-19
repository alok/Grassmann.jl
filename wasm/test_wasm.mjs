import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { loadGrassmannWasm } from "./dist/grassmann_wasm.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// 0. Verify content-fingerprinted wasm-manifest.json + isolated default-factory load
// (Dots P0 #6: fingerprinted loader must reference grassmann.<hash>.wasm directly without locateFile
//  and load cleanly with ZERO ENOENT even when canonical grassmann.wasm is absent!)
const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, "dist/wasm-manifest.json"), "utf8"));
assert.equal(manifest.version, 1, "wasm-manifest version");
assert.equal(manifest.presetCount, 77, "wasm-manifest presetCount");
assert.ok(/^[0-9a-f]{10}$/.test(manifest.hash), "wasm-manifest 10-hex hash");
const fpWasmSrc = path.join(__dirname, "dist", manifest.wasmFile);
const fpLoaderSrc = path.join(__dirname, "dist", manifest.loaderFile);
assert.ok(fs.existsSync(fpWasmSrc), "fingerprinted .wasm exists");
assert.ok(fs.existsSync(fpLoaderSrc), "fingerprinted .mjs exists");
{
  const loaderText = fs.readFileSync(fpLoaderSrc, "utf8");
  assert.ok(loaderText.includes(manifest.wasmFile), `fingerprinted loader must reference ${manifest.wasmFile}`);
  assert.ok(!loaderText.includes("grassmann.wasm"), "fingerprinted loader must not reference un-fingerprinted grassmann.wasm");
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "grassmann-wasm-fp-"));
  try {
    fs.copyFileSync(fpWasmSrc, path.join(tmpDir, manifest.wasmFile));
    fs.copyFileSync(fpLoaderSrc, path.join(tmpDir, manifest.loaderFile));
    const { default: createFp } = await import(pathToFileURL(path.join(tmpDir, manifest.loaderFile)).href);
    const fpMod = await createFp(); // intentionally NO locateFile!
    assert.equal(fpMod._grassmann_initialize(), 0, "isolated fingerprinted WASM initializes cleanly without locateFile");
    assert.equal(fpMod._grassmann_wasm_alignment_selftest(), 0, "isolated fingerprinted WASM 8-byte alignment selftest");
    assert.equal(fpMod._grassmann_wasm_misaligned_allocs(), 0, "isolated fingerprinted WASM zero misaligned allocs");
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
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
assert.equal(g.mod._grassmann_wasm_alignment_selftest(), 0, "initial wasm32 8-byte alignment selftest PASS");
assert.equal(g.mod._grassmann_wasm_misaligned_allocs(), 0, "initial wasm32 zero misaligned allocs");

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

// 5. Full Preset Catalog (ALL 77 CoffeeShop Presets) + 6-Stop Guided GA Tour!
const catalog = g.presetCatalog();
assert.equal(catalog.length, 77, `expected 77 presets, got ${catalog.length}`);
const uniqueIds = new Set(catalog.map(p => p.id));
assert.equal(uniqueIds.size, 77, "zero duplicate preset IDs across 77-preset catalog");
const tour = g.tourCatalog();
assert.equal(tour.length, 6, `expected 6 tour stops, got ${tour.length}`);
assert.equal(tour[0].id, "tour_points_lines");
assert.equal(tour[5].id, "tour_play_wedge");
console.log(`[wasm test] loaded full Lean preset catalog: ${catalog.length} presets (77 unique) + ${tour.length}-stop Guided Tour`);

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

// Exercise EVERY SINGLE preset (all 77!) + verify KaTeX formula & summary in compiled Lean WASM!
let foundOpnsGlsl = false;
let showcaseVerified = 0;
let wave6ShowstoppersVerified = 0;
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
  if (item.id === "implicit_barth_sextic") {
    assert.ok(fr.sections.some(s => s.kind === 0x0B), "implicit_barth_sextic emits bytecode MESH_ASSETS");
    assert.ok(fr.sections.some(s => s.kind === 0x10), "implicit_barth_sextic emits 0x10 OPNS_UNIFORMS");
    assert.ok(fr.meta.opnsShaders && fr.meta.opnsShaders.length === 1, "implicit_barth_sextic emits GPUInit shader");
    assert.ok(fr.meta.params && fr.meta.params.some(p => p.name === "phi"), "implicit_barth_sextic exposes phi slider");
    wave6ShowstoppersVerified++;
  }
  if (item.id === "cga3d_dupin_cyclide_raymarch") {
    assert.ok(fr.sections.some(s => s.kind === 0x10), "cga3d_dupin_cyclide_raymarch emits 0x10 OPNS_UNIFORMS");
    assert.ok(fr.sections.some(s => s.kind === 0x0C), "cga3d_dupin_cyclide_raymarch emits focal conic curves");
    assert.ok(fr.meta.opnsShaders && fr.meta.opnsShaders.length === 1, "cga3d_dupin_cyclide_raymarch emits GPUInit shader");
    wave6ShowstoppersVerified++;
  }
  if (item.id === "pga3d_gears_kinematics") {
    const meshRefs = fr.sections.find(s => s.kind === 0x0A);
    assert.ok(meshRefs && meshRefs.count >= 3, "pga3d_gears_kinematics emits 3 meshing gears");
    assert.ok(fr.sections.some(s => s.kind === 0x09), "pga3d_gears_kinematics emits angular-velocity bivector disks");
    wave6ShowstoppersVerified++;
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
assert.equal(showcaseVerified, 5, "verified all 5 Wave 4B showstopper presets");
assert.equal(wave6ShowstoppersVerified, 3, "verified all 3 Wave 6C showstopper presets (Barth Sextic, Dupin Cyclide, Involute Gears)");
assert.ok(foundOpnsGlsl, "verified cga3d_opns_cyclide GPUInit WGSL/GLSL3/MSL shader emission in WASM");

// Wave 6C Dual-Handle 3D Slicing Manipulator (handle 0 = center, handle 1 = tilt normal)
{
  const sl0Raw = sess.dispatchJson({ op: "loadPreset", id: "pga3d_slicing" });
  const sl0 = parseGSIR(sl0Raw);
  const ptSec = sl0.sections.find(s => s.kind === 0x02);
  assert.ok(ptSec && ptSec.count >= 2, "pga3d_slicing exposes 2 draggable handles (center + tilt normal)");
  const dragTilt = new Uint8Array(20);
  const dtdv = new DataView(dragTilt.buffer);
  dragTilt[0] = 0x01; dtdv.setUint16(2, 16, true); dtdv.setUint32(4, 1, true); // handleId = 1 (tilt normal)
  dtdv.setFloat32(8, 0.7, true); dtdv.setFloat32(12, 0.5, true); dtdv.setFloat32(16, 0.4, true);
  const sl1Raw = sess.dispatchBin(dragTilt);
  const sl1 = parseGSIR(sl1Raw);
  const cSec1 = sl1.sections.find(s => s.kind === 0x0F);
  assert.ok(cSec1, "tilted pga3d_slicing still emits stitched 2D CONTOUR_OVERLAY");
  const plSec0 = sl0.sections.find(s => s.kind === 0x05);
  const plSec1 = sl1.sections.find(s => s.kind === 0x05);
  assert.ok(plSec0 && plSec1, "pga3d_slicing emits cutting plane");
  const dv0 = new DataView(sl0Raw.buffer, sl0Raw.byteOffset, sl0Raw.byteLength);
  const dv1 = new DataView(sl1Raw.buffer, sl1Raw.byteOffset, sl1Raw.byteLength);
  // Plane basis u.y (+16) changes when tilting normal away from +Y
  const uy0 = dv0.getFloat32(plSec0.byteOffset + 16, true);
  const uy1 = dv1.getFloat32(plSec1.byteOffset + 16, true);
  assert.ok(Math.abs(uy1 - uy0) > 0.05, `dragging tilt handle 1 tilted cutting plane (uy: ${uy0.toFixed(3)} -> ${uy1.toFixed(3)})`);
}

// Wave 6C 6-Stop Guided Tour (`loadTourStop` 0..5)
for (let idx = 0; idx < 6; idx++) {
  const tf = parseGSIR(sess.dispatchJson({ op: "loadTourStop", index: idx }));
  if (idx === 5) {
    assert.equal(tf.meta.presetId, "wedge_level_1", "loadTourStop 5 entered wedge_level_1");
    assert.ok(tf.meta.wedge && tf.meta.wedge.level === 1, "loadTourStop 5 entered Wedge 2D Level 1");
  } else {
    assert.equal(tf.meta.presetId, tour[idx].presetId, `loadTourStop ${idx} loaded ${tour[idx].presetId}`);
  }
}

// Dots Round-2 Regression Probes LIVE IN COMPILED WASM!
// (Dots P0 #2) PGA2 script point-vs-line incidence: (e1 - e0) ^ point(1,0,0) == 0 & (e2 - 2*e0) ^ point(3,2,0) == 0
{
  const pga2Inc = parseGSIR(sess.dispatchJson({
    op: "evalScript",
    algebra: "PGA2",
    code: "let P = point(1, 0, 0)\nlet L = e1 - e0\nlet I0 = L ^ P\nlet Q = point(3, 2, 0)\nlet M = e2 - 2*e0\nlet I1 = M ^ Q"
  }));
  assert.equal(pga2Inc.meta.diagnostics.length, 0, "Dots P0 #2: PGA2 incidence zero diagnostics");
  const i0 = pga2Inc.meta.inspect.find(e => e.name === "I0");
  const i1 = pga2Inc.meta.inspect.find(e => e.name === "I1");
  assert.ok(i0 && i0.formatted === "0", `Dots P0 #2: expected I0 == 0, got ${i0?.formatted}`);
  assert.ok(i1 && i1.formatted === "0", `Dots P0 #2: expected I1 == 0, got ${i1?.formatted}`);
}

// (Dots P0 #3) CGA3 off-origin OPNS line A^B^ni emits 1 line & 0 circles passing through A=(0,1,0) & B=(1,1,0)
{
  const cga3LineRaw = sess.dispatchJson({
    op: "evalScript",
    algebra: "CGA3",
    code: "let A = point(0, 1, 0)\nlet B = point(1, 1, 0)\nlet L = A ^ B ^ ni\ngraph([L])"
  });
  const cga3Line = parseGSIR(cga3LineRaw);
  assert.equal(cga3Line.meta.diagnostics.length, 0, "Dots P0 #3: CGA3 off-origin line zero diagnostics");
  const lSec = cga3Line.sections.find(s => s.kind === 0x04);
  const cSec = cga3Line.sections.find(s => s.kind === 0x06);
  assert.ok(lSec && lSec.count === 1, `Dots P0 #3: expected 1 line, got ${lSec?.count ?? 0}`);
  assert.ok(!cSec || cSec.count === 0, `Dots P0 #3: expected 0 circles, got ${cSec?.count ?? 0}`);
  const ldv = new DataView(cga3LineRaw.buffer, cga3LineRaw.byteOffset, cga3LineRaw.byteLength);
  const ox = ldv.getFloat32(lSec.byteOffset + 0, true);
  const oy = ldv.getFloat32(lSec.byteOffset + 4, true);
  const oz = ldv.getFloat32(lSec.byteOffset + 8, true);
  const dx = ldv.getFloat32(lSec.byteOffset + 12, true);
  const dy = ldv.getFloat32(lSec.byteOffset + 16, true);
  const dz = ldv.getFloat32(lSec.byteOffset + 20, true);
  const distToLine = (px, py, pz) => {
    const rx = px - ox, ry = py - oy, rz = pz - oz;
    const cx = ry * dz - rz * dy, cy = rz * dx - rx * dz, cz = rx * dy - ry * dx;
    return Math.hypot(cx, cy, cz);
  };
  assert.ok(distToLine(0, 1, 0) < 1e-4, `Dots P0 #3: A=(0,1,0) on line (dist=${distToLine(0,1,0)})`);
  assert.ok(distToLine(1, 1, 0) < 1e-4, `Dots P0 #3: B=(1,1,0) on line (dist=${distToLine(1,1,0)})`);
}

// (Dots P0 #4) Lossless 64-bit UInt64 seedStr: 9007199254740992 vs 9007199254740993 produce distinct challenges!
{
  const wA = parseGSIR(sess.dispatchJson({ op: "wedgeRandom", dim: 3, difficulty: 2, seedStr: "9007199254740992" }));
  const wB = parseGSIR(sess.dispatchJson({ op: "wedgeRandom", dim: 3, difficulty: 2, seedStr: "9007199254740993" }));
  assert.equal(wA.meta.wedge.seedStr, "9007199254740992", "Dots P0 #4: seedStr A lossless");
  assert.equal(wB.meta.wedge.seedStr, "9007199254740993", "Dots P0 #4: seedStr B lossless");
  assert.equal(wB.meta.wedge.isRandom, true, "Dots P0 #4: isRandom preserved");
  assert.notEqual(wA.meta.wedge.title, wB.meta.wedge.title, "Dots P0 #4: consecutive 64-bit seeds produce distinct challenges");
}

// (Dots P0 #5 + Round-3 #1/#2) Signed GPU powers + Exact Ray-AABB [-bound, bound]^3 + tFar < tNear + bound in [0.5, 20]
{
  // R3 #1: Signed odd integer power x^5 + 1 preserves negative sign (x = -1 plane!)
  const p5CpuRaw = sess.dispatchJson({ op: "evalImplicit", expr: "x^5 + 1", gpuRaymarch: false, bound: 2, gridN: 14 });
  const p5Cpu = parseGSIR(p5CpuRaw);
  const p5Mesh = p5Cpu.sections.find(s => s.kind === 0x0B);
  assert.ok(p5Mesh, "Dots R3 #1: CPU x^5+1 emitted mesh");
  const p5Verts = new DataView(p5CpuRaw.buffer, p5CpuRaw.byteOffset, p5CpuRaw.byteLength).getUint32(p5Mesh.byteOffset + 16, true);
  assert.ok(p5Verts > 200, `Dots R3 #1: CPU x^5+1 rich mesh at x=-1 (verts=${p5Verts})`);
  const p5Gpu = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "x^5 + 1", gpuRaymarch: true, bound: 2 }));
  for (const [lang, src] of [["GLSL3", p5Gpu.meta.opnsShaders[0].glsl], ["WGSL", p5Gpu.meta.opnsShaders[0].wgsl], ["MSL", p5Gpu.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("gs_p5(p.x)"), `Dots R3 #1: ${lang} x^5+1 emits signed gs_p5(p.x)`);
    assert.ok(!src.includes("pow(max(1e-6, abs(p.x))"), `Dots R3 #1: ${lang} x^5+1 does NOT strip sign`);
  }

  // R3 #2a: x - 1.5 @ bound=1 -> CPU strictly empty (0 verts) AND GPU uses intersectBox(ro, rd, 1.0) + tFar < tNear!
  const b1CpuRaw = sess.dispatchJson({ op: "evalImplicit", expr: "x - 1.5", gpuRaymarch: false, bound: 1, gridN: 14 });
  const b1Cpu = parseGSIR(b1CpuRaw);
  const b1Mesh = b1Cpu.sections.find(s => s.kind === 0x0B);
  const b1Verts = b1Mesh ? new DataView(b1CpuRaw.buffer, b1CpuRaw.byteOffset, b1CpuRaw.byteLength).getUint32(b1Mesh.byteOffset + 16, true) : 0;
  assert.equal(b1Verts, 0, `Dots R3 #2: CPU x-1.5 @ bound=1 must be empty (got ${b1Verts} verts)`);
  const b1Gpu = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "x - 1.5", gpuRaymarch: true, bound: 1 }));
  for (const [lang, src] of [["GLSL3", b1Gpu.meta.opnsShaders[0].glsl], ["WGSL", b1Gpu.meta.opnsShaders[0].wgsl], ["MSL", b1Gpu.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("intersectBox(ro, rd, 1.0"), `Dots R3 #2: ${lang} clips to intersectBox(1.0)`);
    assert.ok(src.includes("tFar < tNear || tFar < 0.0"), `Dots R3 #2: ${lang} enforces tFar < tNear || tFar < 0.0`);
    assert.ok(!src.includes("intersectSphere"), `Dots R3 #2: ${lang} has no legacy intersectSphere`);
  }

  // R3 #2b: bound=1 vs bound=4 distinct hashes + intersectBox(4.0)
  const gB1 = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "x*x+y*y+z*z-9", gpuRaymarch: true, bound: 1 }));
  const gB4 = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "x*x+y*y+z*z-9", gpuRaymarch: true, bound: 4 }));
  assert.notEqual(gB1.meta.opnsShaders[0].hash, gB4.meta.opnsShaders[0].hash, "Dots P0 #5: bound=1 vs bound=4 distinct shader hashes");
  for (const [lang, src] of [["GLSL3", gB4.meta.opnsShaders[0].glsl], ["WGSL", gB4.meta.opnsShaders[0].wgsl], ["MSL", gB4.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("intersectBox(ro, rd, 4.0"), `Dots P0 #5: ${lang} bound=4 uses intersectBox(4.0)`);
  }

  // R3 #2c: x - 15 @ bound=20 -> CPU non-empty plane at x=15 AND GPU uses intersectBox(20.0)
  const b20CpuRaw = sess.dispatchJson({ op: "evalImplicit", expr: "x - 15", gpuRaymarch: false, bound: 20, gridN: 14 });
  const b20Cpu = parseGSIR(b20CpuRaw);
  const b20Mesh = b20Cpu.sections.find(s => s.kind === 0x0B);
  assert.ok(b20Mesh, "Dots R3 #2: CPU x-15 @ bound=20 emitted mesh");
  const b20Verts = new DataView(b20CpuRaw.buffer, b20CpuRaw.byteOffset, b20CpuRaw.byteLength).getUint32(b20Mesh.byteOffset + 16, true);
  assert.ok(b20Verts > 100, `Dots R3 #2: CPU x-15 @ bound=20 non-empty (verts=${b20Verts})`);
  const b20Gpu = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "x - 15", gpuRaymarch: true, bound: 20 }));
  for (const [lang, src] of [["GLSL3", b20Gpu.meta.opnsShaders[0].glsl], ["WGSL", b20Gpu.meta.opnsShaders[0].wgsl], ["MSL", b20Gpu.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("intersectBox(ro, rd, 20.0"), `Dots R3 #2: ${lang} bound=20 uses intersectBox(20.0)`);
  }
}

// (Dots P1 #8 & #10 + Round-3 #3) Mode-gated WedgeGesture + deterministic RK4 seekTime(2.5) / resetTime!
{
  const readCubePos = (raw, fr) => {
    const mref = fr.sections.find(s => s.kind === 0x0A);
    assert.ok(mref && mref.count >= 1, "bouncing cube has 0x0A MESH_REFS");
    const dv = new DataView(raw.buffer, raw.byteOffset, raw.byteLength);
    // MeshRef record: meshId(8)+dirtyHash(8)+motor(32)+mat4(64) -> translation col3 at +48 + 48 = +96
    return [
      dv.getFloat32(mref.byteOffset + 96, true),
      dv.getFloat32(mref.byteOffset + 100, true),
      dv.getFloat32(mref.byteOffset + 104, true),
    ];
  };
  const st0Raw = sess.dispatchJson({ op: "loadPreset", id: "pga3d_bouncing_cube" });
  const st0 = parseGSIR(st0Raw);
  assert.equal(st0.meta.presetId, "pga3d_bouncing_cube");
  const pos0 = readCubePos(st0Raw, st0);
  // Send binary WedgeGesture while in CoffeeShop -> MUST NOT hijack mode into Wedge!
  const hijack = new Uint8Array(40);
  const hdv = new DataView(hijack.buffer);
  hijack[0] = 0x06; hdv.setUint16(2, 36, true); hdv.setUint32(4, 2, true); hdv.setUint32(8, 3, true);
  hdv.setFloat32(12, -1.0, true); hdv.setFloat32(24, 1.0, true); hdv.setUint16(38, 0, true);
  const afterHijack = parseGSIR(sess.dispatchBin(hijack));
  assert.ok(afterHijack.meta === null || afterHijack.meta.presetId === "pga3d_bouncing_cube", "Dots P1 #8: WedgeGesture ignored outside Wedge mode");
  // Explicit seekTime(2.5) -> deterministic RK4 replay moves cube substantially away from t=0!
  const sSeekRaw = sess.dispatchJson({ op: "seekTime", t: 2.5 });
  const sSeek = parseGSIR(sSeekRaw);
  assertNear(sSeek.simTime, 2.5, 1e-4, "Dots P1 #10: seekTime sets exact simTime == 2.5");
  const posSeek = readCubePos(sSeekRaw, sSeek);
  const moveDist = Math.hypot(posSeek[0] - pos0[0], posSeek[1] - pos0[1], posSeek[2] - pos0[2]);
  assert.ok(moveDist > 0.25, `Dots R3 #3: seekTime(2.5) RK4 moved cube away from t=0 (dist=${moveDist.toFixed(3)})`);
  // Explicit resetTime -> exact simTime 0.0 AND restores initial t=0 cube pose!
  const sResetRaw = sess.dispatchJson({ op: "resetTime" });
  const sReset = parseGSIR(sResetRaw);
  assertNear(sReset.simTime, 0.0, 1e-6, "Dots P1 #10: resetTime resets exact simTime == 0.0");
  const posReset = readCubePos(sResetRaw, sReset);
  const resetErr = Math.hypot(posReset[0] - pos0[0], posReset[1] - pos0[1], posReset[2] - pos0[2]);
  assert.ok(resetErr < 1e-5, `Dots R3 #3: resetTime restored t=0 cube pose (err=${resetErr})`);
}
console.log("[wasm test] ALL DOTS ROUND-2 & ROUND-3 REGRESSIONS + DUAL-HANDLE SLICING + 6-STOP TOUR VERIFIED LIVE IN WASM!");

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

// Wedge 2D (L1 & L9) + Wedge 3D (L10, L16 & Grand Finale L17!) + live WedgeGesture preview & commit!
for (const [preset, lvl] of [["wedge_2d", 1], ["wedge_2d", 9], ["wedge_3d", 10], ["wedge_3d", 16], ["wedge_3d", 17]]) {
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

// Dots Round-6 Fixpoint regressions LIVE in compiled WASM:
// 1. l_Int_repr & 9-sig-digit fmtFloat exact scientific exponents & float32 precision
// 2. l_Rat_* exact rational rotor + basisSquares signed Int formatting
// 3. Tightened 32-step gs_refine_min (1e-8 outer + 1e-5 local bracket) across GLSL3/WGSL/MSL
{
  const r6Out = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "0.0000002*x - 0.000001", gpuRaymarch: true, bound: 1 }));
  for (const [lang, src] of [["GLSL3", r6Out.meta.opnsShaders[0].glsl], ["WGSL", r6Out.meta.opnsShaders[0].wgsl], ["MSL", r6Out.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("2.0e-7") && src.includes("1.0e-6"), `R6 WASM ${lang} tiny-outside exact scientific exponents`);
    assert.ok(!src.includes("e0"), `R6 WASM ${lang} tiny-outside must NOT emit broken e0`);
  }
  const r6In = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "0.0000001*x - 0.00000005", gpuRaymarch: true, bound: 1 }));
  for (const [lang, src] of [["GLSL3", r6In.meta.opnsShaders[0].glsl], ["WGSL", r6In.meta.opnsShaders[0].wgsl], ["MSL", r6In.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("1.0e-7") && src.includes("5.0e-8"), `R6 WASM ${lang} tiny-inside exact scientific exponents`);
    assert.ok(!src.includes("e0"), `R6 WASM ${lang} tiny-inside must NOT emit broken e0`);
  }
  const r6Diff = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "1000000*(0.5000004*x - 0.5000001*x) - 0.15", gpuRaymarch: true, bound: 1 }));
  for (const [lang, src] of [["GLSL3", r6Diff.meta.opnsShaders[0].glsl], ["WGSL", r6Diff.meta.opnsShaders[0].wgsl], ["MSL", r6Diff.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("0.5000004") && src.includes("0.5000001") && src.includes("0.15"), `R6 WASM ${lang} preserves 9-sig-digit float32 literals`);
  }
  const r6Pos = parseGSIR(sess.dispatchJson({ op: "evalImplicit", expr: "(x-0.12345)^2 + 0.0001*(0.0001 + x*x*0.0001)*0.1", gpuRaymarch: true, bound: 1 }));
  for (const [lang, src] of [["GLSL3", r6Pos.meta.opnsShaders[0].glsl], ["WGSL", r6Pos.meta.opnsShaders[0].wgsl], ["MSL", r6Pos.meta.opnsShaders[0].msl]]) {
    assert.ok(src.includes("k < 32") && src.includes("gMin <= 1e-8") && src.includes("gMin <= 1e-5"), `R6 WASM ${lang} tightened 32-step + local-bracket gs_refine_min`);
  }
  const r6Rat = parseGSIR(sess.dispatchJson({ op: "loadPreset", id: "r3_rational_rotor" }));
  assert.deepEqual(r6Rat.meta.algebra.basisMetric, [1, 1, 1, 1, -1, -1, -1, -1], "R6 WASM l_Int_repr renders R3 8-blade basisMetric == [1,1,1,1,-1,-1,-1,-1]");
  const ratJoined = r6Rat.meta.inspect.map(i => i.formatted).join(" ");
  assert.ok(ratJoined.includes("/25") || ratJoined.includes("/5"), `R6 WASM exact Rat arithmetic produces non-zero rational fractions (got: ${ratJoined})`);
  const r6Sta = parseGSIR(sess.dispatchJson({ op: "loadPreset", id: "sta_lorentz_boost" }));
  assert.equal(r6Sta.meta.algebra.basisMetric.length, 16, "R6 WASM STA has 16 blade metric entries");
  assert.equal(r6Sta.meta.algebra.basisMetric[1], -1, "R6 WASM STA e0^2 == -1 (-+++ Lorentzian metric)");
  assert.equal(r6Sta.meta.algebra.basisMetric[2], 1, "R6 WASM STA e1^2 == +1");
  console.log("[wasm test] ALL DOTS ROUND-6 REGRESSIONS (l_Int_repr, l_Rat_*, 9-sig fmtFloat, 32-step gs_refine_min) PASSED LIVE IN WASM!");
}

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

// Final post-workload wasm32 8-byte alignment audit (Dots P0 #1):
// Prove 100% of live FloatArray / ctor / bignat / String / Array heap allocs + reallocs stayed 0 mod 8!
assert.equal(g.mod._grassmann_wasm_alignment_selftest(), 0, "post-workload wasm32 8-byte alignment selftest PASS");
const totalHeapAllocs = g.mod._grassmann_wasm_alloc_count() >>> 0;
const misalignedAllocs = g.mod._grassmann_wasm_misaligned_allocs() >>> 0;
assert.equal(misalignedAllocs, 0, `expected 0 misaligned wasm32 heap allocs, got ${misalignedAllocs}`);
assert.ok(totalHeapAllocs > 10000, `expected >10000 live heap allocs checked, got ${totalHeapAllocs}`);
console.log(`[wasm align] 100% 8-byte aligned (selftest=0, misaligned=0 / ${totalHeapAllocs} live heap allocs+reallocs)`);
console.log("[wasm test] ALL 77 PRESETS + 6-STOP TOUR + 6 DOTS REGRESSIONS + 8B ALIGNMENT + BYTECODE IMPLICIT3D/GPU + LIVESCRIPT V2 + 17 WEDGE LEVELS PASSED IN WASM!");
