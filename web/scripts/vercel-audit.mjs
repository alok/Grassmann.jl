#!/usr/bin/env node
// Live HTTPS Vercel Production Audit for Grassmann Studio
// Verifies:
//   1. Exact Vercel HTTP headers (must-revalidate on wasm-manifest.json, immutable + application/wasm on fingerprinted WASM, ZERO COOP/COEP)
//   2. Cold load -> Lean WASM Worker boots with 69 presets, 0 console/shader/page errors
//   3. Warm reload (browser HTTP cache enabled) -> 69 presets, 0 errors
//   4. Live HTTPS visual screenshots: Sculpted Bunny + GA Syntax Highlighted Editor, GPUInit OPNS Gyroid, Accessible Single-Hand Wedge Solve, Gallery Daylight

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright-core';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WEB_DIR = path.resolve(__dirname, '..');
const OUT_DIR = path.join(WEB_DIR, 'artifacts', 'vercel-audit');

const targetUrl = process.argv[2] || process.env.VERCEL_URL;
if (!targetUrl) {
  console.error('Usage: node scripts/vercel-audit.mjs <https://grassmann-studio.vercel.app>');
  process.exit(1);
}
const BASE_URL = targetUrl.replace(/\/+$/, '');

function findChrome() {
  const candidates = [
    process.env.CHROME_PATH,
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/Applications/Chromium.app/Contents/MacOS/Chromium',
  ].filter(Boolean);
  for (const c of candidates) {
    if (fs.existsSync(c)) return c;
  }
  throw new Error('No local Chrome/Chromium found');
}

function assert(cond, msg) {
  if (!cond) throw new Error(`ASSERTION FAILED: ${msg}`);
}

async function measureCanvas(page) {
  return page.evaluate(() => {
    const canvas = document.querySelector('canvas.gs-webgl-canvas');
    if (!canvas) return { ok: false, reason: 'no canvas' };
    const off = document.createElement('canvas');
    off.width = 128;
    off.height = 80;
    const ctx = off.getContext('2d');
    ctx.drawImage(canvas, 0, 0, off.width, off.height);
    const data = ctx.getImageData(0, 0, off.width, off.height).data;
    let sum = 0;
    let sumSq = 0;
    const buckets = new Set();
    const n = data.length / 4;
    for (let i = 0; i < data.length; i += 4) {
      const r = data[i], g = data[i + 1], b = data[i + 2];
      const lum = 0.2126 * r + 0.7152 * g + 0.0722 * b;
      sum += lum;
      sumSq += lum * lum;
      buckets.add(`${r >> 4},${g >> 4},${b >> 4}`);
    }
    const mean = sum / n;
    const variance = sumSq / n - mean * mean;
    return {
      ok: buckets.size >= 6 && variance > 15,
      distinctColors: buckets.size,
      variance: Math.round(variance * 10) / 10,
      meanLum: Math.round(mean * 10) / 10,
    };
  });
}

async function verifyHeaders() {
  const manifestUrl = `${BASE_URL}/wasm/wasm-manifest.json`;
  const mResp = await fetch(manifestUrl);
  assert(mResp.ok, `GET ${manifestUrl} failed: HTTP ${mResp.status}`);
  const mCC = (mResp.headers.get('cache-control') || '').toLowerCase();
  assert(mCC.includes('must-revalidate'), `Expected must-revalidate on wasm-manifest.json, got: ${mCC}`);
  assert(!mCC.includes('immutable'), `wasm-manifest.json MUST NOT be immutable, got: ${mCC}`);
  assert(!mResp.headers.get('cross-origin-embedder-policy'), 'Unexpected COEP header on manifest');
  assert(!mResp.headers.get('cross-origin-opener-policy'), 'Unexpected COOP header on manifest');

  const manifest = await mResp.json();
  assert(manifest.hash && manifest.wasmFile, `Invalid manifest JSON: ${JSON.stringify(manifest)}`);

  const wasmUrl = `${BASE_URL}/wasm/${manifest.wasmFile}`;
  const wResp = await fetch(wasmUrl, { method: 'HEAD' });
  assert(wResp.ok, `HEAD ${wasmUrl} failed: HTTP ${wResp.status}`);
  const wCT = (wResp.headers.get('content-type') || '').toLowerCase();
  const wCC = (wResp.headers.get('cache-control') || '').toLowerCase();
  assert(wCT.includes('application/wasm'), `Expected application/wasm on ${wasmUrl}, got: ${wCT}`);
  assert(wCC.includes('immutable'), `Expected immutable cache on fingerprinted ${wasmUrl}, got: ${wCC}`);

  console.log(`[vercel] HTTP Headers PASS | manifest="${mCC}" | ${manifest.wasmFile}="${wCT}; ${wCC}"`);
  return manifest;
}

async function main() {
  fs.mkdirSync(OUT_DIR, { recursive: true });
  const manifest = await verifyHeaders();

  const browser = await chromium.launch({
    executablePath: findChrome(),
    headless: true,
    args: ['--use-gl=angle', '--use-angle=swiftshader-webgl', '--enable-webgl', '--ignore-gpu-blocklist'],
  });

  try {
    const context = await browser.newContext({ viewport: { width: 1440, height: 900 } });
    const page = await context.newPage();

    const consoleErrors = [];
    const consoleWarnings = [];
    const pageErrors = [];
    page.on('console', (m) => {
      if (m.type() === 'error') consoleErrors.push(m.text());
      if (
        m.type() === 'warning' &&
        /shader|webgl|glsl/i.test(m.text()) &&
        !/GPU stall due to ReadPixels/i.test(m.text())
      ) {
        consoleWarnings.push(m.text());
      }
    });
    page.on('pageerror', (e) => pageErrors.push(e.message));

    // 1. Cold HTTPS Load -> verify 69 presets + Web Worker WASM + GA syntax highlight + Sculpted Bunny
    await page.goto(BASE_URL, { waitUntil: 'networkidle' });
    await page.waitForTimeout(1000);

    const sCold = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sCold.transportKind === 'wasm', `Cold load expected wasm, got ${sCold.transportKind}`);
    assert(sCold.transportLabel.includes(manifest.hash), `Expected worker hash ${manifest.hash}, got ${sCold.transportLabel}`);
    assert(sCold.presetCount >= 69, `Cold load expected >=69 presets, got ${sCold.presetCount}`);

    // Verify GA syntax highlight tokens rendered in Code Editor
    const tokCount = await page.locator('.gs-editor-highlight .tok-kw, .gs-editor-highlight .tok-op, .gs-editor-highlight .tok-num').count();
    assert(tokCount >= 5, `Expected GA syntax highlighted tokens in editor, got ${tokCount}`);

    const c1 = await measureCanvas(page);
    assert(c1.ok, `Cold load canvas blank: ${JSON.stringify(c1)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'vercel-01-bunny-ide.png') });
    console.log(`[vercel] 1. Cold HTTPS Load PASS | ${sCold.presetCount} presets | ${sCold.transportLabel} | tokens=${tokCount} | canvas=`, c1);

    // 2. Warm Reload (browser HTTP cache enabled!) -> verify zero stale-cache failure
    await page.reload({ waitUntil: 'networkidle' });
    await page.waitForTimeout(800);
    const sWarm = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sWarm.transportKind === 'wasm' && sWarm.presetCount >= 69, `Warm reload failed: ${JSON.stringify(sWarm)}`);
    console.log(`[vercel] 2. Warm Cached Reload PASS | ${sWarm.presetCount} presets | ${sWarm.transportLabel}`);

    // 3. Live GPUInit GLSL3 OPNS Gyroid over HTTPS
    await page.locator('.gs-mode-btn', { hasText: 'LeanCalculator 3D' }).click();
    await page.locator('.gs-subtab-btn', { hasText: /^Imp 3D$/ }).click();
    await page.locator('.gs-btn-primary', { hasText: 'Evaluate Implicit 3D in Lean' }).click();
    await page.waitForTimeout(700);
    const c2 = await measureCanvas(page);
    assert(c2.ok, `OPNS Gyroid blank: ${JSON.stringify(c2)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'vercel-02-opns-gyroid.png') });
    console.log(`[vercel] 3. Live GPUInit OPNS Gyroid PASS | canvas=`, c2);

    // 4. Accessible Single-Hand Wedge 2D L1 Solve (Click A -> Click B -> Click Join button -> SOLVED!)
    await page.locator('.gs-mode-btn', { hasText: 'Wedge 2D/3D' }).click();
    await page.waitForTimeout(600);
    const sW = await page.evaluate(() => window.__grassmannStudio.getState());
    const draggables = sW.points.filter((p) => p.draggable);
    const pA = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), draggables[0].handleId);
    const pB = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), draggables[1].handleId);
    await page.mouse.click(pA.clientX, pA.clientY);
    await page.waitForTimeout(120);
    await page.mouse.click(pB.clientX, pB.clientY);
    await page.waitForTimeout(150);
    assert(await page.locator('.gs-wedge-armed').isVisible(), 'Expected accessible single-hand Armed bar visible after clicking A & B');
    await page.locator('.gs-wedge-op-btn[data-wedge-op="join"]').click();
    await page.waitForTimeout(450);
    const sWSolved = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sWSolved.wedge?.solved === true, `Expected accessible single-hand Join to solve L1, got ${JSON.stringify(sWSolved.wedge)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'vercel-03-wedge-solved.png') });
    console.log(`[vercel] 4. Accessible Single-Hand Wedge Solve PASS | moves=${sWSolved.wedge.moves} score=${sWSolved.wedge.score}`);

    // 5. Gallery Daylight Theme on Sculpted Bunny
    await page.locator('.gs-mode-btn', { hasText: 'CoffeeShop IDE' }).click();
    await page.locator('[data-preset-id="pga3d_slicing"]').click();
    await page.locator('.gs-theme-btn').click();
    await page.waitForTimeout(600);
    await page.screenshot({ path: path.join(OUT_DIR, 'vercel-04-daylight.png') });
    console.log('[vercel] 5. Gallery Daylight Screenshot Captured');

    assert(consoleErrors.length === 0, `Console errors: ${JSON.stringify(consoleErrors)}`);
    assert(consoleWarnings.length === 0, `WebGL/Shader warnings: ${JSON.stringify(consoleWarnings)}`);
    assert(pageErrors.length === 0, `Page errors: ${JSON.stringify(pageErrors)}`);
    console.log(`[vercel] ALL LIVE HTTPS PRODUCTION CHECKS PASSED on ${BASE_URL} (0 console/shader/page errors)!`);
  } finally {
    await browser.close();
  }
}

main().catch((err) => {
  console.error('[vercel] FAILED:', err);
  process.exit(1);
});
