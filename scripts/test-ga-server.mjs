#!/usr/bin/env node
/**
 * scripts/test-ga-server.mjs — End-to-end verification & latency benchmark
 * for the pure-Lean `ga-server` (HTTP/1.1 keep-alive + RFC 6455 WebSocket +
 * binary GSIR v1 + static assets + CORS).
 */
import assert from "node:assert/strict";
import http from "node:http";
import { spawn } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..");
const binPath = path.join(repoRoot, ".lake/build/bin/ga-server");
const PORT = 18787;
const BASE = `http://127.0.0.1:${PORT}`;

function parseGSIR(bytes) {
  const dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  assert.equal(dv.getUint32(0, true), 0x52495347, "GSIR magic");
  assert.equal(dv.getUint16(4, true), 1, "GSIR version");
  const frameSeq = dv.getBigUint64(8, true);
  const sectionCount = dv.getUint32(28, true);
  const totalByteLen = dv.getUint32(32, true);
  const metaJsonOffset = dv.getUint32(36, true);
  const metaJsonLen = dv.getUint32(40, true);
  assert.equal(totalByteLen, bytes.byteLength, "totalByteLen");
  for (let i = 0; i < sectionCount; i++) {
    const off = 64 + i * 16;
    const byteOffset = dv.getUint32(off + 8, true);
    assert.equal(byteOffset % 8, 0, "section 8-byte aligned");
  }
  const meta = metaJsonLen > 0
    ? JSON.parse(new TextDecoder().decode(bytes.subarray(metaJsonOffset, metaJsonOffset + metaJsonLen)))
    : null;
  return { frameSeq, sectionCount, metaJsonLen, meta };
}

function makeDragEvent(handleId, x, y, z) {
  const buf = new Uint8Array(20);
  const dv = new DataView(buf.buffer);
  buf[0] = 0x01; // DragHandle
  buf[1] = 0x00;
  dv.setUint16(2, 16, true);
  dv.setUint32(4, handleId, true);
  dv.setFloat32(8, x, true);
  dv.setFloat32(12, y, true);
  dv.setFloat32(16, z, true);
  return buf;
}

function makeTickEvent(dt, t, forceFull = false) {
  const buf = new Uint8Array(12);
  const dv = new DataView(buf.buffer);
  buf[0] = 0x02;
  buf[1] = forceFull ? 1 : 0;
  dv.setUint16(2, 8, true);
  dv.setFloat32(4, dt, true);
  dv.setFloat32(8, t, true);
  return buf;
}

function httpReq(agent, method, reqPath, body = null, contentType = "application/octet-stream") {
  return new Promise((resolve, reject) => {
    const headers = {};
    if (body !== null) {
      headers["Content-Type"] = contentType;
      headers["Content-Length"] = Buffer.byteLength(body);
    }
    const req = http.request({
      hostname: "127.0.0.1",
      port: PORT,
      path: reqPath,
      method,
      headers,
      agent,
    }, (res) => {
      const chunks = [];
      res.on("data", (c) => chunks.push(c));
      res.on("end", () => resolve({
        status: res.statusCode,
        headers: res.headers,
        body: Buffer.concat(chunks),
      }));
    });
    req.on("error", reject);
    if (body !== null) req.write(body);
    req.end();
  });
}

const server = spawn(binPath, ["--host", "127.0.0.1", "--port", String(PORT), "--static", path.join(repoRoot, "wasm")], {
  stdio: ["ignore", "pipe", "pipe"],
});

await new Promise((resolve, reject) => {
  const timeout = setTimeout(() => {
    server.kill("SIGKILL");
    reject(new Error("ga-server failed to start in time"));
  }, 5000);
  server.stdout.on("data", (chunk) => {
    const text = chunk.toString();
    process.stdout.write(text);
    if (text.includes("listening on")) {
      clearTimeout(timeout);
      resolve();
    }
  });
  server.stderr.on("data", (chunk) => process.stderr.write(chunk));
  server.on("exit", (code) => {
    clearTimeout(timeout);
    reject(new Error(`ga-server exited prematurely with code ${code}`));
  });
});

const agent = new http.Agent({ keepAlive: true, maxSockets: 4 });

try {
  // 1. Health & CORS
  const health = await httpReq(agent, "GET", "/health");
  assert.equal(health.status, 200);
  assert.equal(health.headers["access-control-allow-origin"], "*");
  const hjson = JSON.parse(health.body.toString("utf8"));
  assert.equal(hjson.ok, true);
  assert.equal(hjson.protocol, "GSIR/1");

  const opt = await httpReq(agent, "OPTIONS", "/api/frame");
  assert.equal(opt.status, 204);

  // 1b. Full Lean preset catalog endpoint (/api/presets — all 69 presets!)
  const cat = await httpReq(agent, "GET", "/api/presets");
  assert.equal(cat.status, 200);
  const catalog = JSON.parse(cat.body.toString("utf8"));
  assert.ok(Array.isArray(catalog) && catalog.length === 69, `expected 69 presets, got ${catalog.length}`);
  assert.equal(new Set(catalog.map((p) => p.id)).size, 69, "all 69 preset IDs unique");
  assert.ok(catalog.some((p) => p.id === "pga3d_slicing"));
  assert.ok(catalog.some((p) => p.id === "pga3d_slicing_hq"));
  assert.ok(catalog.some((p) => p.id === "implicit_gyroid"));
  assert.ok(catalog.some((p) => p.id === "sta_lorentz_boost"));

  // 2. Session lifecycle + binary GSIR frames (sculpted bunny + pga3d_objects delta cache + STA)
  const cr = await httpReq(agent, "POST", "/api/session");
  assert.equal(cr.status, 200);
  const { session } = JSON.parse(cr.body.toString("utf8"));
  assert.ok(session > 0);

  const fr0 = await httpReq(agent, "GET", `/api/session/${session}/frame`);
  assert.equal(fr0.status, 200);
  assert.equal(fr0.headers["content-type"], "application/octet-stream");
  assert.ok(fr0.body.byteLength >= 100000, `expected sculpted bunny GSIR >= 100KB, got ${fr0.body.byteLength}`);
  const g0 = parseGSIR(new Uint8Array(fr0.body.buffer, fr0.body.byteOffset, fr0.body.byteLength));
  assert.equal(g0.meta.presetId, "pga3d_slicing");

  // Load pga3d_objects, then verify hot Tick omits unchanged metaJson AND cached MESH_ASSETS
  const objLoad = await httpReq(agent, "POST", `/api/session/${session}/json`,
    Buffer.from(JSON.stringify({ op: "loadPreset", id: "pga3d_objects" })), "application/json");
  assert.equal(objLoad.status, 200);
  const fr1 = await httpReq(agent, "POST", `/api/session/${session}/bin`, Buffer.from(makeTickEvent(0.016, 0.5)));
  assert.equal(fr1.status, 200);
  const g1 = parseGSIR(new Uint8Array(fr1.body.buffer, fr1.body.byteOffset, fr1.body.byteLength));
  assert.equal(g1.metaJsonLen, 0, "HTTP hot tick omits unchanged metaJson");

  const fr2 = await httpReq(agent, "POST", `/api/session/${session}/json`,
    Buffer.from(JSON.stringify({ op: "loadPreset", id: "sta_lorentz_boost" })), "application/json");
  assert.equal(fr2.status, 200);
  const g2 = parseGSIR(new Uint8Array(fr2.body.buffer, fr2.body.byteOffset, fr2.body.byteLength));
  assert.equal(g2.meta.presetId, "sta_lorentz_boost");

  const del = await httpReq(agent, "DELETE", `/api/session/${session}`);
  assert.equal(del.status, 200);
  const afterDel = await httpReq(agent, "GET", `/api/session/${session}/frame`);
  assert.equal(afterDel.status, 404);

  // 3. Default convenience routes (used by web-studio ServerTransport)
  const defFr = await httpReq(agent, "GET", "/api/frame");
  assert.equal(defFr.status, 200);
  parseGSIR(new Uint8Array(defFr.body.buffer, defFr.body.byteOffset, defFr.body.byteLength));
  const evJson = await httpReq(agent, "POST", "/api/event/json",
    Buffer.from(JSON.stringify({ op: "loadPreset", id: "sta_lorentz_boost" })), "application/json");
  assert.equal(evJson.status, 200);

  // 4. Static asset serving + path traversal rejection
  const stFile = await httpReq(agent, "GET", "/grassmann_wasm.mjs");
  assert.equal(stFile.status, 200);
  assert.ok(stFile.headers["content-type"].includes("javascript"));
  const trav = await httpReq(agent, "GET", "/../lakefile.toml");
  assert.equal(trav.status, 403);

  // 5. HTTP/1.1 Keep-Alive Latency Benchmark (500 binary DragHandle roundtrips)
  const N_HTTP = 500;
  const tHttp0 = performance.now();
  for (let i = 0; i < N_HTTP; i++) {
    const res = await httpReq(agent, "POST", "/api/event/bin", Buffer.from(makeDragEvent(0, i * 0.005, 0.3, 0.1)));
    assert.equal(res.status, 200);
  }
  const dtHttp = performance.now() - tHttp0;
  console.log(`[ga-server bench] HTTP/1.1 keep-alive binary GSIR: ${((dtHttp * 1000) / N_HTTP).toFixed(1)} us/req (${N_HTTP} reqs)`);

  // 6. Live RFC 6455 WebSocket Binary GSIR Test & Benchmark!
  const ws = new WebSocket(`ws://127.0.0.1:${PORT}/ws`);
  ws.binaryType = "arraybuffer";
  await new Promise((resolve, reject) => {
    ws.addEventListener("open", resolve, { once: true });
    ws.addEventListener("error", reject, { once: true });
  });

  const wsRpc = (payload) => new Promise((resolve, reject) => {
    const onMsg = (ev) => {
      ws.removeEventListener("error", onErr);
      resolve(new Uint8Array(ev.data));
    };
    const onErr = (err) => {
      ws.removeEventListener("message", onMsg);
      reject(err);
    };
    ws.addEventListener("message", onMsg, { once: true });
    ws.addEventListener("error", onErr, { once: true });
    ws.send(payload);
  });

  const ws0 = parseGSIR(await wsRpc(JSON.stringify({ op: "loadPreset", id: "sta_lorentz_boost" })));
  assert.equal(ws0.meta.presetId, "sta_lorentz_boost");

  const N_WS = 500;
  const tWs0 = performance.now();
  let lastBytes = 0;
  for (let i = 0; i < N_WS; i++) {
    const frame = await wsRpc(makeDragEvent(0, i * 0.005, 0.2, 0.1));
    lastBytes = frame.byteLength;
    assert.equal(frame[0], 0x47); // 'G' of GSIR
  }
  const dtWs = performance.now() - tWs0;
  console.log(`[ga-server bench] WebSocket binary GSIR roundtrip:  ${((dtWs * 1000) / N_WS).toFixed(1)} us/frame (${lastBytes} B/frame, ${Math.round(N_WS / (dtWs / 1000))} fps max)`);

  ws.close();
  console.log("[ga-server e2e] ALL HTTP + WEBSOCKET + STATIC + SECURITY CHECKS PASSED!");
} finally {
  agent.destroy();
  server.kill("SIGTERM");
}
