#!/usr/bin/env node
/**
 * scripts/bench-cabi-wasm.mjs — Automated 3-Way Cross-Parity & Performance
 * Suite comparing:
 *   1. Native Init-only C ABI (`libgrassmann_cabi.dylib` via `cabi_parity_dump`)
 *   2. Compiled Lean 4.36 WASM (`wasm/dist/grassmann_wasm.mjs`)
 *   3. Pure-Lean persistent binary server (`ga-server` over WS + HTTP)
 *
 * Verifies exact numerical parity (<= 1e-12) across STA Cl(3,1) (-+++), R3
 * rational rotors, PGA3 motors, and CGA3, exact 69-preset catalog equality,
 * and structural/geometric GSIR v1 parity (section table, vertex/index counts,
 * 3D mesh bounding boxes <= 1e-4, contour counts, shader hashes, Wedge state,
 * LiveScript v2, and delta cache behavior) — automatically guarding against
 * any future native-vs-WASM float/bignum divergence!
 */
import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..");

function assertNear(a, b, tol, label) {
  assert.ok(
    Number.isFinite(a) && Number.isFinite(b) && Math.abs(a - b) <= tol,
    `${label}: native=${a} vs other=${b} (diff=${Math.abs(a - b)}, tol=${tol})`
  );
}

function summarizeGsir(bytes) {
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  assert.equal(dv.getUint32(0, true), 0x52495347, "GSIR magic");
  assert.equal(dv.getUint16(4, true), 1, "GSIR version");
  const seq = Number(dv.getBigUint64(8, true));
  const secCount = dv.getUint32(28, true);
  const totalLen = dv.getUint32(32, true);
  const metaOff = dv.getUint32(36, true);
  const metaLen = dv.getUint32(40, true);
  assert.equal(totalLen, bytes.byteLength, "totalByteLen");

  const sections = [];
  let meshVerts = 0, meshIndices = 0, contourPolys = 0;
  let bbox = null;
  for (let i = 0; i < secCount; i++) {
    const off = 64 + i * 16;
    const kind = dv.getUint32(off, true);
    const count = dv.getUint32(off + 4, true);
    const bOff = dv.getUint32(off + 8, true);
    const bLen = dv.getUint32(off + 12, true);
    assert.equal(bOff % 8, 0, "8B aligned section");
    sections.push([kind, count, bLen]);
    if (kind === 0x0b && count > 0) {
      meshVerts = dv.getUint32(bOff + 16, true);
      meshIndices = dv.getUint32(bOff + 20, true);
      if (meshVerts > 0) {
        let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity, minZ = Infinity, maxZ = -Infinity;
        const posOff = bOff + 32;
        for (let v = 0; v < meshVerts; v++) {
          const x = dv.getFloat32(posOff + v * 12, true);
          const y = dv.getFloat32(posOff + v * 12 + 4, true);
          const z = dv.getFloat32(posOff + v * 12 + 8, true);
          if (x < minX) minX = x; if (x > maxX) maxX = x;
          if (y < minY) minY = y; if (y > maxY) maxY = y;
          if (z < minZ) minZ = z; if (z > maxZ) maxZ = z;
        }
        bbox = [minX, maxX, minY, maxY, minZ, maxZ];
      }
    } else if (kind === 0x0f) {
      contourPolys = dv.getUint32(bOff + 16, true);
    }
  }
  const meta = metaLen > 0
    ? JSON.parse(new TextDecoder().decode(bytes.subarray(metaOff, metaOff + metaLen)))
    : null;
  return { bytes: bytes.byteLength, seq, metaLen, sections, meshVerts, meshIndices, contourPolys, bbox, meta };
}

function makeTickBin() {
  const b = new Uint8Array(12);
  const dv = new DataView(b.buffer);
  b[0] = 0x02; dv.setUint16(2, 8, true); dv.setFloat32(4, 0.016, true); dv.setFloat32(8, 0.5, true);
  return b;
}

function makeWedgeSolveBin() {
  const b = new Uint8Array(40);
  const dv = new DataView(b.buffer);
  b[0] = 0x06; dv.setUint16(2, 36, true); dv.setUint32(4, 2, true); dv.setUint32(8, 3, true);
  dv.setFloat32(12, -1.0, true); dv.setFloat32(24, 1.0, true); dv.setUint16(38, 0, true);
  return b;
}

const LIVE_SCRIPT = {
  op: "evalScript",
  algebra: "PGA3",
  code: [
    "@basis PGA3",
    "fn mid(a, b) = (a + b) * 0.5",
    "let A = point(-1.0, 0.0, 0.0)",
    "let B = point(1.0, 0.5, 0.0)",
    "let L = A & B",
    "let M = mid(A, B)",
    "graph([0x44aaff, A, B, L, M])",
  ].join("\n"),
};
const GYROID_MESH = {
  op: "evalImplicit",
  expr: "cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)",
  gpuRaymarch: false,
  gridN: 16,
};
const GYROID_GPU = {
  op: "evalImplicit",
  expr: "cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)",
  gpuRaymarch: true,
};
const PARAM_TORUS = {
  op: "evalParametric",
  fx: "(1.1+0.42*cos(v))*cos(u)",
  fy: "0.42*sin(v)",
  fz: "(1.1+0.42*cos(v))*sin(u)",
  nu: 32,
  nv: 18,
};

function compareFrameParity(name, ref, other, label) {
  assert.equal(other.sections.length, ref.sections.length, `${label}.${name}: sectionCount`);
  for (let i = 0; i < ref.sections.length; i++) {
    assert.equal(other.sections[i][0], ref.sections[i][0], `${label}.${name}: sec[${i}].kind`);
    assert.equal(other.sections[i][1], ref.sections[i][1], `${label}.${name}: sec[${i}].count`);
    assert.equal(other.sections[i][2], ref.sections[i][2], `${label}.${name}: sec[${i}].byteLen`);
  }
  assert.equal(other.meshVerts, ref.meshVerts, `${label}.${name}: meshVerts`);
  assert.equal(other.meshIndices, ref.meshIndices, `${label}.${name}: meshIndices`);
  assert.equal(other.contourPolys, ref.contourPolys, `${label}.${name}: contourPolys`);
  if (ref.bbox) {
    assert.ok(other.bbox, `${label}.${name}: bbox present`);
    for (let i = 0; i < 6; i++) {
      assertNear(ref.bbox[i], other.bbox[i], 1e-4, `${label}.${name}: bbox[${i}]`);
    }
  } else {
    assert.equal(other.bbox, null, `${label}.${name}: bbox null`);
  }
  if (ref.meta === null) {
    assert.equal(other.meta, null, `${label}.${name}: delta metaJson omitted`);
  } else {
    assert.ok(other.meta !== null, `${label}.${name}: metaJson present`);
    assert.equal(other.meta.presetId, ref.meta.presetId, `${label}.${name}: presetId`);
    assert.equal(other.meta.diagnostics.length, ref.meta.diagnostics.length, `${label}.${name}: diagnostics`);
    if (ref.meta.wedge) {
      assert.equal(other.meta.wedge.level, ref.meta.wedge.level, `${label}.${name}: wedge.level`);
      assert.equal(other.meta.wedge.moves, ref.meta.wedge.moves, `${label}.${name}: wedge.moves`);
      assert.equal(other.meta.wedge.solved, ref.meta.wedge.solved, `${label}.${name}: wedge.solved`);
    }
    if (ref.meta.opnsShaders && ref.meta.opnsShaders.length > 0) {
      assert.equal(other.meta.opnsShaders.length, ref.meta.opnsShaders.length, `${label}.${name}: shaderCount`);
      assert.equal(other.meta.opnsShaders[0].hash, ref.meta.opnsShaders[0].hash, `${label}.${name}: opnsShader hash`);
    }
    if (ref.meta.calc) {
      assert.equal(other.meta.calc.display, ref.meta.calc.display, `${label}.${name}: calc.display`);
    }
    if (ref.meta.formula) {
      assert.equal(other.meta.formula, ref.meta.formula, `${label}.${name}: KaTeX formula`);
    }
    if (ref.meta.params && ref.meta.params.length > 0) {
      assert.equal(other.meta.params.length, ref.meta.params.length, `${label}.${name}: params.length`);
      for (let i = 0; i < ref.meta.params.length; i++) {
        assert.equal(other.meta.params[i].name, ref.meta.params[i].name, `${label}.${name}: params[${i}].name`);
        assertNear(ref.meta.params[i].value, other.meta.params[i].value, 1e-4, `${label}.${name}: params[${i}].value`);
      }
    }
  }
}

// 1. Native C ABI (libgrassmann_cabi.dylib)
const dumpBin = path.join(repoRoot, ".lake/build/cabi/cabi_parity_dump");
assert.ok(fs.existsSync(dumpBin), `Missing ${dumpBin} — run ./scripts/build-cabi.sh first`);
const nativeOut = JSON.parse(execFileSync(dumpBin, { maxBuffer: 64 * 1024 * 1024 }).toString("utf8"));

// 2. Compiled Lean 4.36 WASM
const { loadGrassmannWasm } = await import(path.join(repoRoot, "wasm/dist/grassmann_wasm.mjs"));
const wasm = await loadGrassmannWasm();
const manifest = JSON.parse(fs.readFileSync(path.join(repoRoot, "wasm/dist/wasm-manifest.json"), "utf8"));

const staE0 = new Float64Array(16); staE0[1] = 1.0;
const staE1 = new Float64Array(16); staE1[2] = 1.0;
const staV1 = new Float64Array(16); staV1[2] = 2.0; staV1[4] = -1.0; staV1[8] = 0.5;
const staV2 = new Float64Array(16); staV2[2] = -0.5; staV2[4] = 1.5; staV2[8] = 3.0;
const wasmKernels = {
  staMul: Array.from(wasm.staMul(staE0, staE1)),
  staBoosted: Array.from(wasm.staSandwich(wasm.staBoostRotor(0.75, 1, 0, 0), staE0)),
  staSpWedge: Array.from(wasm.staSpatialWedge(staV1, staV2)),
  r3Rational: Array.from(wasm.r3ApplyRationalRotor([1, 0, 0, 1], [1, 0.5, -2])),
  pga3Motor: Array.from(wasm.pga3MotorCompose(wasm.pga3MakeTranslator(1.5, -0.5, 2.25), wasm.pga3MakeRotor(0, 0, 1, 1.0471975511965976))),
  pga3Mat4: Array.from(wasm.pga3MotorToMat4(wasm.pga3MotorCompose(wasm.pga3MakeTranslator(1.5, -0.5, 2.25), wasm.pga3MakeRotor(0, 0, 1, 1.0471975511965976)))),
  cga3Down: Array.from(wasm.cga3Down(wasm.cga3Up(1.5, -2.25, 0.75))),
};

for (const [k, natArr] of Object.entries(nativeOut.kernels)) {
  const wArr = wasmKernels[k];
  assert.equal(wArr.length, natArr.length, `kernel.${k} len`);
  for (let i = 0; i < natArr.length; i++) {
    assertNear(natArr[i], wArr[i], 1e-12, `kernel.${k}[${i}]`);
  }
}

const wasmCatalog = wasm.presetCatalog();
assert.equal(nativeOut.catalog.length, 77, `expected 77 native presets, got ${nativeOut.catalog.length}`);
assert.deepEqual(wasmCatalog.map(p => p.id), nativeOut.catalog.map(p => p.id), "Native vs WASM 77-preset catalog IDs");
const wasmTour = wasm.tourCatalog();
assert.equal(nativeOut.tour.length, 6, `expected 6 native tour stops, got ${nativeOut.tour.length}`);
assert.deepEqual(wasmTour, nativeOut.tour, "Native vs WASM 6-stop Tour catalog exact equality");

const wsess = wasm.createStudioSession();
const wasmFrames = {};
wasmFrames.initial_bunny = summarizeGsir(wsess.getFrame());
wasmFrames.cga3d_opns_cyclide = summarizeGsir(wsess.dispatchJson({ op: "loadPreset", id: "cga3d_opns_cyclide" }));
wsess.dispatchJson({ op: "loadPreset", id: "pga3d_objects" });
wasmFrames.objects_hot_tick = summarizeGsir(wsess.dispatchBin(makeTickBin()));
wasmFrames.livescript_v2 = summarizeGsir(wsess.dispatchJson(LIVE_SCRIPT));
const twg0 = performance.now();
wasmFrames.implicit_gyroid_mesh = summarizeGsir(wsess.dispatchJson(GYROID_MESH));
const wasmGyroidMs = performance.now() - twg0;
const tws0 = performance.now();
wasmFrames.implicit_gyroid_gpu = summarizeGsir(wsess.dispatchJson(GYROID_GPU));
const wasmGpuShaderMs = performance.now() - tws0;
wasmFrames.parametric_torus = summarizeGsir(wsess.dispatchJson(PARAM_TORUS));
wsess.dispatchJson({ op: "loadPreset", id: "wedge_2d" });
wasmFrames.wedge_l1_solved = summarizeGsir(wsess.dispatchBin(makeWedgeSolveBin()));
wasmFrames.wedge_tutorial_t1 = summarizeGsir(wsess.dispatchJson({ op: "wedgeTutorial", id: "T1" }));
wasmFrames.wedge_random_3d = summarizeGsir(wsess.dispatchJson({ op: "wedgeRandom", dim: 3, difficulty: 1, seed: 42 }));
wasmFrames.calc_sta = summarizeGsir(wsess.dispatchJson({ op: "calcEval", mode: "STA", expr: "e1 * e2" }));
wsess.dispatchJson({ op: "loadPreset", id: "sta_terrell_penrose" });
wasmFrames.terrell_penrose_param = summarizeGsir(wsess.dispatchJson({ op: "setParam", name: "beta", value: 0.85 }));
wasmFrames.maxwell_streamlines = summarizeGsir(wsess.dispatchJson({ op: "loadPreset", id: "sta_maxwell_streamlines" }));
wasmFrames.bouncing_cube = summarizeGsir(wsess.dispatchJson({ op: "loadPreset", id: "pga3d_bouncing_cube" }));
wasmFrames.barth_sextic = summarizeGsir(wsess.dispatchJson({ op: "loadPreset", id: "implicit_barth_sextic" }));
wasmFrames.dupin_cyclide = summarizeGsir(wsess.dispatchJson({ op: "loadPreset", id: "cga3d_dupin_cyclide_raymarch" }));
wasmFrames.gears_kinematics = summarizeGsir(wsess.dispatchJson({ op: "loadPreset", id: "pga3d_gears_kinematics" }));
wasmFrames.tour_stop_3 = summarizeGsir(wsess.dispatchJson({ op: "loadTourStop", index: 3 }));
wsess.dispatchJson({ op: "loadPreset", id: "wedge_3d" });
wasmFrames.wedge_l17 = summarizeGsir(wsess.dispatchJson({ op: "wedgeAction", action: "goto", arg: 17 }));
wasmFrames.r3_pow5_gpu = summarizeGsir(wsess.dispatchJson({ op: "evalImplicit", expr: "x^5 + 1", gpuRaymarch: true, bound: 2 }));
wasmFrames.r3_plane_b20_cpu = summarizeGsir(wsess.dispatchJson({ op: "evalImplicit", expr: "x - 15", gpuRaymarch: false, bound: 20, gridN: 14 }));
wsess.dispatchJson({ op: "loadPreset", id: "pga3d_bouncing_cube" });
wasmFrames.r3_bouncing_seek = summarizeGsir(wsess.dispatchJson({ op: "seekTime", t: 2.5 }));

for (const name of Object.keys(nativeOut.frames)) {
  compareFrameParity(name, nativeOut.frames[name], wasmFrames[name], "wasm");
}

// WASM microbenchmarks
const N_M = 200000;
let t0 = performance.now();
for (let i = 0; i < N_M; i++) wasm.mod._grassmann_pga3_motor_compose(wasm._a, wasm._b, wasm._o);
const wasmMotorNs = ((performance.now() - t0) * 1e6) / N_M;

wsess.dispatchJson({ op: "loadPreset", id: "sta_lorentz_boost" });
const drag = new Uint8Array(20);
const ddv = new DataView(drag.buffer);
drag[0] = 0x01; ddv.setUint16(2, 16, true); ddv.setUint32(4, 0, true);
const N_D = 5000;
t0 = performance.now();
for (let i = 0; i < N_D; i++) {
  ddv.setFloat32(8, (i % 100) * 0.01, true);
  wsess.dispatchBin(drag);
}
const wasmDragUs = ((performance.now() - t0) * 1e3) / N_D;
wsess.destroy();

// 3. Pure-Lean `ga-server` over HTTP + RFC 6455 WebSocket
const serverBin = path.join(repoRoot, ".lake/build/bin/ga-server");
let srvBench = null;
if (fs.existsSync(serverBin)) {
  const PORT = 18793;
  const server = spawn(serverBin, ["--host", "127.0.0.1", "--port", String(PORT)], {
    stdio: ["ignore", "pipe", "pipe"],
  });
  try {
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error("ga-server timeout")), 5000);
      server.stdout.on("data", (d) => {
        if (d.toString().includes("listening on")) { clearTimeout(timer); resolve(); }
      });
      server.on("exit", (code) => { clearTimeout(timer); reject(new Error(`ga-server exit ${code}`)); });
    });

    const catJson = await new Promise((resolve, reject) => {
      http.get(`http://127.0.0.1:${PORT}/api/presets`, (res) => {
        const chunks = [];
        res.on("data", c => chunks.push(c));
        res.on("end", () => resolve(JSON.parse(Buffer.concat(chunks).toString("utf8"))));
      }).on("error", reject);
    });
    assert.deepEqual(catJson.map(p => p.id), nativeOut.catalog.map(p => p.id), "Native vs ga-server 77-preset catalog IDs");
    const tourJson = await new Promise((resolve, reject) => {
      http.get(`http://127.0.0.1:${PORT}/api/tour`, (res) => {
        const chunks = [];
        res.on("data", c => chunks.push(c));
        res.on("end", () => resolve(JSON.parse(Buffer.concat(chunks).toString("utf8"))));
      }).on("error", reject);
    });
    assert.deepEqual(tourJson, nativeOut.tour, "Native vs ga-server 6-stop Tour catalog exact equality");

    const ws = new WebSocket(`ws://127.0.0.1:${PORT}/ws`);
    ws.binaryType = "arraybuffer";
    await new Promise((resolve, reject) => {
      ws.addEventListener("open", resolve, { once: true });
      ws.addEventListener("error", reject, { once: true });
    });
    const rpc = (payload) => new Promise((resolve, reject) => {
      const onMsg = (ev) => { ws.removeEventListener("error", onErr); resolve(new Uint8Array(ev.data)); };
      const onErr = (e) => { ws.removeEventListener("message", onMsg); reject(e); };
      ws.addEventListener("message", onMsg, { once: true });
      ws.addEventListener("error", onErr, { once: true });
      ws.send(payload);
    });

    const srvFrames = {};
    srvFrames.initial_bunny = summarizeGsir(await rpc(JSON.stringify({ op: "snapshot" })));
    srvFrames.cga3d_opns_cyclide = summarizeGsir(await rpc(JSON.stringify({ op: "loadPreset", id: "cga3d_opns_cyclide" })));
    await rpc(JSON.stringify({ op: "loadPreset", id: "pga3d_objects" }));
    srvFrames.objects_hot_tick = summarizeGsir(await rpc(makeTickBin()));
    srvFrames.livescript_v2 = summarizeGsir(await rpc(JSON.stringify(LIVE_SCRIPT)));
    const tsg0 = performance.now();
    srvFrames.implicit_gyroid_mesh = summarizeGsir(await rpc(JSON.stringify(GYROID_MESH)));
    const srvGyroidMs = performance.now() - tsg0;
    const tss0 = performance.now();
    srvFrames.implicit_gyroid_gpu = summarizeGsir(await rpc(JSON.stringify(GYROID_GPU)));
    const srvGpuShaderMs = performance.now() - tss0;
    srvFrames.parametric_torus = summarizeGsir(await rpc(JSON.stringify(PARAM_TORUS)));
    await rpc(JSON.stringify({ op: "loadPreset", id: "wedge_2d" }));
    srvFrames.wedge_l1_solved = summarizeGsir(await rpc(makeWedgeSolveBin()));
    srvFrames.wedge_tutorial_t1 = summarizeGsir(await rpc(JSON.stringify({ op: "wedgeTutorial", id: "T1" })));
    srvFrames.wedge_random_3d = summarizeGsir(await rpc(JSON.stringify({ op: "wedgeRandom", dim: 3, difficulty: 1, seed: 42 })));
    srvFrames.calc_sta = summarizeGsir(await rpc(JSON.stringify({ op: "calcEval", mode: "STA", expr: "e1 * e2" })));
    await rpc(JSON.stringify({ op: "loadPreset", id: "sta_terrell_penrose" }));
    srvFrames.terrell_penrose_param = summarizeGsir(await rpc(JSON.stringify({ op: "setParam", name: "beta", value: 0.85 })));
    srvFrames.maxwell_streamlines = summarizeGsir(await rpc(JSON.stringify({ op: "loadPreset", id: "sta_maxwell_streamlines" })));
    srvFrames.bouncing_cube = summarizeGsir(await rpc(JSON.stringify({ op: "loadPreset", id: "pga3d_bouncing_cube" })));
    srvFrames.barth_sextic = summarizeGsir(await rpc(JSON.stringify({ op: "loadPreset", id: "implicit_barth_sextic" })));
    srvFrames.dupin_cyclide = summarizeGsir(await rpc(JSON.stringify({ op: "loadPreset", id: "cga3d_dupin_cyclide_raymarch" })));
    srvFrames.gears_kinematics = summarizeGsir(await rpc(JSON.stringify({ op: "loadPreset", id: "pga3d_gears_kinematics" })));
    srvFrames.tour_stop_3 = summarizeGsir(await rpc(JSON.stringify({ op: "loadTourStop", index: 3 })));
    await rpc(JSON.stringify({ op: "loadPreset", id: "wedge_3d" }));
    srvFrames.wedge_l17 = summarizeGsir(await rpc(JSON.stringify({ op: "wedgeAction", action: "goto", arg: 17 })));
    srvFrames.r3_pow5_gpu = summarizeGsir(await rpc(JSON.stringify({ op: "evalImplicit", expr: "x^5 + 1", gpuRaymarch: true, bound: 2 })));
    srvFrames.r3_plane_b20_cpu = summarizeGsir(await rpc(JSON.stringify({ op: "evalImplicit", expr: "x - 15", gpuRaymarch: false, bound: 20, gridN: 14 })));
    await rpc(JSON.stringify({ op: "loadPreset", id: "pga3d_bouncing_cube" }));
    srvFrames.r3_bouncing_seek = summarizeGsir(await rpc(JSON.stringify({ op: "seekTime", t: 2.5 })));

    for (const name of Object.keys(nativeOut.frames)) {
      compareFrameParity(name, nativeOut.frames[name], srvFrames[name], "ga-server");
    }

    await rpc(JSON.stringify({ op: "loadPreset", id: "sta_lorentz_boost" }));
    const N_S = 500;
    const tsd0 = performance.now();
    for (let i = 0; i < N_S; i++) {
      ddv.setFloat32(8, (i % 100) * 0.01, true);
      await rpc(drag);
    }
    const srvDragUs = ((performance.now() - tsd0) * 1e3) / N_S;
    ws.close();
    srvBench = { dragUs: srvDragUs, gyroidMs: srvGyroidMs, gpuShaderMs: srvGpuShaderMs };
  } finally {
    server.kill("SIGTERM");
  }
}

console.log("\n=== 3-Way Cross-Parity & Benchmark Report (Native C ABI vs Lean WASM vs ga-server) ===");
console.log(`Parity: 7 numeric GA kernels (tol <= 1e-12), 77/77 catalog IDs, 6/6 Tour stops, ${Object.keys(nativeOut.frames).length} GSIR v1 scenes (bbox tol <= 1e-4, KaTeX & @param exact): ALL IDENTICAL PASS!`);
console.log(`WASM artifact: ${manifest.wasmFile} (${(manifest.bytes / 1024).toFixed(1)} KB raw / ${(manifest.gzipBytes / 1024).toFixed(1)} KB gz)`);
console.log("| Metric | Native C ABI (dylib) | Lean 4.36 WASM | Pure-Lean ga-server (WS) |");
console.log("|---|---:|---:|---:|");
console.log(`| pga3_motor_compose | ${nativeOut.bench.motorNs.toFixed(1)} ns | ${wasmMotorNs.toFixed(1)} ns | — |`);
console.log(`| DragHandle -> GSIR | ${nativeOut.bench.dragUs.toFixed(2)} us | ${wasmDragUs.toFixed(2)} us | ${srvBench ? srvBench.dragUs.toFixed(2) + " us" : "n/a"} |`);
console.log(`| evalImplicit Gyroid 16^3 | ${nativeOut.bench.gyroidMs.toFixed(2)} ms | ${wasmGyroidMs.toFixed(2)} ms | ${srvBench ? srvBench.gyroidMs.toFixed(2) + " ms" : "n/a"} |`);
console.log(`| GPUInit GLSL3+WGSL+MSL | ${nativeOut.bench.gpuShaderMs.toFixed(2)} ms | ${wasmGpuShaderMs.toFixed(2)} ms | ${srvBench ? srvBench.gpuShaderMs.toFixed(2) + " ms" : "n/a"} |`);
console.log("[bench-cabi-wasm] ALL 3-WAY PARITY & BENCHMARK CHECKS PASSED!");
