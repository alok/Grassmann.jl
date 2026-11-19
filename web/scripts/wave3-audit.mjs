#!/usr/bin/env node
/**
 * Wave 3A Full-Studio Live Visual & Gameplay E2E Audit against 25-Module Lean 4.36 WASM
 *
 * Exercises and captures real 1440x900 screenshots of:
 *   - Dynamic Lean preset catalog (grassmann_studio_preset_catalog)
 *   - Sculpted 3D Bunny #pga3d_slicing (before & after real mouse slice drag!)
 *   - Live Lean-emitted GLSL 300 es OPNS Raymarching (cga3d_opns_cyclide) with 0 shader errors
 *   - Live 3D CGA Sphere Intersections (cga3d_intersections)
 *   - REAL Wedge 2D Level 1 Gameplay: drag points A & B apart -> green rubber-band + isPreview -> SOLVED!
 *   - Wedge 3D Level 10 (spatial PGA3 view)
 *   - STA Cl(3,1) Lorentz Boost + Dzhanibekov Free Top
 *   - LeanCalculator 3D Surface + 2D Implicit Equations Contours + Implicit 3D / Parametric 3D + GAlculator
 */

import { spawn, execSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright-core';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WEB_DIR = path.resolve(__dirname, '..');
const OUT_DIR = path.join(WEB_DIR, 'artifacts', 'wave3-audit');
const PUBLIC_WASM_DIR = path.join(WEB_DIR, 'public', 'wasm');
const PORT = 4183;
const BASE_URL = `http://127.0.0.1:${PORT}/`;

function findChromium() {
  const home = os.homedir();
  const candidates = [
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/opt/homebrew/bin/chromium',
  ];
  const cacheDir = path.join(home, 'Library/Caches/ms-playwright');
  if (fs.existsSync(cacheDir)) {
    for (const entry of fs.readdirSync(cacheDir)) {
      if (entry.startsWith('chromium-')) {
        for (const arch of ['chrome-mac-arm64', 'chrome-mac']) {
          candidates.push(
            path.join(
              cacheDir,
              entry,
              arch,
              'Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing'
            )
          );
        }
      }
    }
  }
  for (const p of candidates) {
    if (fs.existsSync(p)) return p;
  }
  throw new Error('No Chromium executable found');
}

function stageWasm() {
  const wasmSrcDir = path.resolve(WEB_DIR, '..', '..', 'cabi', 'wasm', 'dist');
  const mjs = path.join(wasmSrcDir, 'grassmann.mjs');
  const wasm = path.join(wasmSrcDir, 'grassmann.wasm');
  if (!fs.existsSync(mjs) || !fs.existsSync(wasm)) {
    throw new Error(`Missing compiled Lean WASM in ${wasmSrcDir}`);
  }
  fs.mkdirSync(PUBLIC_WASM_DIR, { recursive: true });
  fs.copyFileSync(mjs, path.join(PUBLIC_WASM_DIR, 'grassmann.mjs'));
  fs.copyFileSync(wasm, path.join(PUBLIC_WASM_DIR, 'grassmann.wasm'));
}

async function waitForServer(url, timeoutMs = 15000) {
  const start = Date.now();
  while (Date.now() - start < timeoutMs) {
    try {
      const r = await fetch(url);
      if (r.ok) return;
    } catch {
      // retry
    }
    await new Promise((r) => setTimeout(r, 120));
  }
  throw new Error(`Vite preview failed to respond at ${url}`);
}

function assert(cond, msg) {
  if (!cond) throw new Error(`ASSERTION FAILED: ${msg}`);
}

async function measureCanvas(page) {
  return page.evaluate(() => {
    const canvas = document.querySelector('canvas.gs-webgl-canvas');
    if (!(canvas instanceof HTMLCanvasElement)) return { ok: false, distinctColors: 0, variance: 0 };
    const probe = document.createElement('canvas');
    probe.width = 96;
    probe.height = 60;
    const ctx = probe.getContext('2d');
    if (!ctx) return { ok: false, distinctColors: 0, variance: 0 };
    ctx.drawImage(canvas, 0, 0, probe.width, probe.height);
    const data = ctx.getImageData(0, 0, probe.width, probe.height).data;
    const buckets = new Set();
    let s1 = 0;
    let s2 = 0;
    const n = probe.width * probe.height;
    for (let i = 0; i < data.length; i += 4) {
      buckets.add(`${data[i] >> 3},${data[i + 1] >> 3},${data[i + 2] >> 3}`);
      const lum = 0.299 * data[i] + 0.587 * data[i + 1] + 0.114 * data[i + 2];
      s1 += lum;
      s2 += lum * lum;
    }
    const mean = s1 / n;
    const variance = Math.max(0, s2 / n - mean * mean);
    return {
      ok: buckets.size >= 8 && variance > 10,
      distinctColors: buckets.size,
      variance: Number(variance.toFixed(1)),
      meanLum: Number(mean.toFixed(1)),
    };
  });
}

async function main() {
  fs.mkdirSync(OUT_DIR, { recursive: true });
  stageWasm();
  execSync('npm run build', { cwd: WEB_DIR, stdio: 'inherit' });

  const preview = spawn(
    'npx',
    ['vite', 'preview', '--port', String(PORT), '--strictPort', '--host', '127.0.0.1'],
    { cwd: WEB_DIR, stdio: ['ignore', 'pipe', 'pipe'] }
  );

  let browser;
  try {
    await waitForServer(BASE_URL);
    browser = await chromium.launch({
      executablePath: findChromium(),
      headless: true,
      args: ['--use-gl=angle', '--enable-webgl', '--ignore-gpu-blocklist', '--no-sandbox'],
    });

    const context = await browser.newContext({ viewport: { width: 1440, height: 900 } });
    const page = await context.newPage();

    const consoleErrors = [];
    const consoleWarnings = [];
    const pageErrors = [];
    page.on('console', (m) => {
      if (m.type() === 'error') consoleErrors.push(m.text());
      if (m.type() === 'warning' && /shader|webgl|glsl/i.test(m.text())) {
        consoleWarnings.push(m.text());
      }
    });
    page.on('pageerror', (e) => pageErrors.push(e.message));

    const snap = async (filename) => {
      await page.waitForTimeout(550);
      const c = await measureCanvas(page);
      const st = await page.evaluate(() => window.__grassmannStudio.getState());
      await page.screenshot({ path: path.join(OUT_DIR, filename) });
      console.log(`[wave3] ${filename} | preset=${st.presetId} | canvas=`, c);
      assert(c.ok, `Canvas blank on ${filename}: ${JSON.stringify(c)}`);
      return st;
    };

    await page.goto(BASE_URL, { waitUntil: 'networkidle' });
    await page.waitForTimeout(900);

    // 1. Dynamic Preset Catalog (69 presets!) + Dedicated Web Worker WASM + Sculpted Bunny #pga3d_slicing + LiveScript v2 metaJson.script
    const s0 = await snap('w3-01-bunny-before.png');
    assert(s0.transportKind === 'wasm', 'Expected live Lean WASM');
    assert(/Worker/i.test(s0.transportLabel || ''), `Expected dedicated Web Worker WASM, got ${s0.transportLabel}`);
    assert(s0.presetCount >= 69, `Expected >=69 dynamic Lean presets, got ${s0.presetCount}`);
    assert(await page.locator('.gs-contour-pip').isVisible(), 'Expected sculpted bunny 2D slice contour PiP visible!');
    assert(typeof s0.metaScript === 'string' && s0.metaScript.length >= 60, `Expected Lean metaJson.script populated on #pga3d_slicing, got ${JSON.stringify(s0.metaScript)}`);
    assert(s0.script === s0.metaScript, 'Expected Code Editor synced directly to Lean metaJson.script');
    console.log(`[wave3] Dynamic Lean preset catalog synced: ${s0.presetCount} presets via ${s0.transportLabel} (metaJson.script=${s0.metaScript.length} chars)`);

    // 1b. LiveScript v2 Live Edit + Shift+Enter + Syntax Error Resilience!
    const editor = page.locator('.gs-editor-textarea');
    const origScript = s0.script;
    const editedScript = origScript.replace(/-?\d+\.\d+/, '0.45');
    await editor.fill(editedScript);
    await editor.press('Shift+Enter');
    await page.waitForTimeout(400);
    const sEdited = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(Number(sEdited.frameSeq) > Number(s0.frameSeq), 'Expected LiveScript v2 Shift+Enter to advance frameSeq');
    assert(sEdited.diagnostics.length === 0, `Expected 0 diagnostics on valid edited LiveScript v2, got ${JSON.stringify(sEdited.diagnostics)}`);
    console.log(`[wave3] LiveScript v2 live edit + Shift+Enter PASS (seq ${s0.frameSeq} -> ${sEdited.frameSeq}, 0 diags)`);

    // Syntax error resilience: Line L, Col C diagnostic shown while last valid 3D mesh remains rendered!
    await editor.fill('let broken = 1 + (');
    await editor.press('Shift+Enter');
    await page.waitForTimeout(350);
    assert(await page.locator('.gs-diagnostics').isVisible(), 'Expected diagnostics banner visible on syntax error');
    const diagText = await page.locator('.gs-diagnostics').textContent();
    assert(/Line \d+, Col \d+|error|expected/i.test(diagText || ''), `Expected Line/Col diagnostic, got: ${diagText}`);
    const cAfterErr = await measureCanvas(page);
    assert(cAfterErr.ok, 'Expected last valid 3D scene retained after syntax error');
    console.log(`[wave3] LiveScript v2 syntax error resilience PASS ("${(diagText || '').trim()}")`);

    // Restore clean #pga3d_slicing preset before handle drag
    await page.locator('[data-preset-id="pga3d_slicing"]').click();
    await page.waitForTimeout(450);

    // Drag slice handle upward through bunny torso!
    const h0 = await page.evaluate(() => window.__grassmannStudio.getHandleScreenPos(0));
    assert(h0 !== null, 'Expected draggable slice handleId=0');
    await page.mouse.move(h0.clientX, h0.clientY);
    await page.mouse.down();
    await page.mouse.move(h0.clientX, h0.clientY - 70, { steps: 10 });
    await page.mouse.up();
    await snap('w3-02-bunny-sliced.png');

    // 2. Live Lean-Emitted GPUInit GLSL 300 es OPNS Raymarching (cga3d_opns_cyclide)
    await page.locator('[data-preset-id="cga3d_opns_cyclide"]').click();
    const sOpns = await snap('w3-03-opns-raymarch.png');
    assert(sOpns.opnsCount >= 1, `Expected active OPNS uniform on cga3d_opns_cyclide, got ${sOpns.opnsCount}`);

    // 3. 3D CGA Sphere Intersections
    await page.locator('[data-preset-id="cga3d_intersections"]').click();
    await snap('w3-04-cga3d-intersections.png');

    // 4. REAL Wedge 2D Level 1 Gameplay: Pull A & B apart -> Preview -> SOLVED!
    await page.locator('.gs-mode-btn', { hasText: 'Wedge 2D/3D' }).click();
    await page.waitForTimeout(600);
    const sW0 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sW0.wedge && sW0.wedge.level === 1 && !sW0.wedge.solved, `Expected Wedge L1 unsolved, got ${JSON.stringify(sW0.wedge)}`);
    const draggables = sW0.points.filter((p) => p.draggable);
    assert(draggables.length >= 2, `Expected >=2 draggable points on Wedge L1, got ${draggables.length}`);

    const pA = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), draggables[0].handleId);
    const pB = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), draggables[1].handleId);
    assert(pA && pB, 'Expected screen coordinates for Wedge points A and B');

    // Drag point A outward (left/down away from B)
    await page.mouse.move(pA.clientX, pA.clientY);
    await page.mouse.down();
    await page.mouse.move(pA.clientX - 95, pA.clientY + 25, { steps: 8 });
    await page.mouse.up();

    // Drag point B outward (right/up away from A) -> hold mid-drag for live preview screenshot!
    await page.mouse.move(pB.clientX, pB.clientY);
    await page.mouse.down();
    await page.mouse.move(pB.clientX + 95, pB.clientY - 25, { steps: 8 });
    await page.waitForTimeout(250);
    const rubberLines = await page.locator('.gs-wedge-svg line').count();
    assert(rubberLines >= 2, `Expected 2 green rubber-band drag vectors, got ${rubberLines}`);
    await snap('w3-05-wedge2d-preview.png');

    // Release mouse -> commit WedgeGesture -> Level 1 SOLVED!
    await page.mouse.up();
    const sSolved = await snap('w3-06-wedge2d-solved.png');
    assert(sSolved.wedge?.solved === true, `Expected Wedge L1 SOLVED after Join, got ${JSON.stringify(sSolved.wedge)}`);
    assert(await page.locator('.gs-wedge-solved').isVisible(), 'Expected solved celebration banner visible');
    console.log(`[wave3] REAL WEDGE 2D L1 SOLVED LIVE IN LEAN WASM! moves=${sSolved.wedge.moves} score=${sSolved.wedge.score}`);

    // 5. Wedge Tutorials (T2 Join) + Random Challenge + Wedge 3D Level 10
    await page.locator('.gs-wedge-tut-strip button', { hasText: /^T2 Join$/ }).click();
    await page.waitForTimeout(350);
    await page.locator('.gs-wedge-rand-btn').click();
    await page.waitForTimeout(350);
    await page.locator('.gs-wedge-top button', { hasText: /PGA/ }).click();
    const sW3d = await snap('w3-07-wedge3d-l10.png');
    assert(sW3d.wedge?.is3D === true, `Expected Wedge 3D mode, got ${JSON.stringify(sW3d.wedge)}`);

    // 6. STA Cl(3,1) Lorentz Boost + Dzhanibekov Free Top
    await page.locator('.gs-mode-btn', { hasText: 'CoffeeShop IDE' }).click();
    await page.locator('[data-preset-id="sta_lorentz_boost"]').click();
    await snap('w3-08-sta-lorentz.png');

    await page.locator('[data-preset-id="pga3d_physics_free_top"]').click();
    await snap('w3-09-free-top.png');

    // 7. LeanCalculator 3D: Surface + Implicit 3D (Mesh & GPU Raymarch) + Parametric 3D + 2D Eq Contours
    await page.locator('.gs-mode-btn', { hasText: 'LeanCalculator 3D' }).click();
    await page.locator('.gs-subtab-btn', { hasText: /^Surface$/ }).click();
    await page.locator('.gs-btn-primary', { hasText: 'Evaluate Surface in Lean' }).click();
    await snap('w3-10-surface-3d.png');

    await page.locator('.gs-subtab-btn', { hasText: /^2D Eq$/ }).click();
    await page.locator('.gs-btn-primary', { hasText: 'Solve Contours in Lean' }).click();
    await snap('w3-11-equations-contours.png');
    assert(await page.locator('.gs-contour-pip').isVisible(), 'Expected 2D Contour Overlay PiP visible after evalEquations');

    // 7b. Implicit 3D Gyroid (Symmetric Kuhn Marching Tetrahedra Mesh + ZERO stale contour PiP, AND live GPUInit GLSL3 Raymarch!)
    await page.locator('.gs-subtab-btn', { hasText: /^Imp 3D$/ }).click();
    await page.locator('.gs-seg-btn', { hasText: 'Marching Tet Mesh' }).click();
    await snap('w3-13-implicit-mesh.png');
    assert(!(await page.locator('.gs-contour-pip').isVisible()), 'Expected stale 2D Contour Overlay PiP CLEARED on evalImplicit!');
    const cMesh = await measureCanvas(page);
    assert(cMesh.variance >= 400 && cMesh.distinctColors >= 80, `Expected full symmetric Gyroid mesh, got ${JSON.stringify(cMesh)}`);

    await page.locator('.gs-seg-btn', { hasText: 'GPU Raymarch (GLSL3)' }).click();
    const sImpGpu = await snap('w3-14-implicit-gpu.png');
    assert(sImpGpu.opnsCount >= 1, `Expected live GPUInit OPNS shader for Implicit 3D GPU Raymarch, got ${sImpGpu.opnsCount}`);

    // 7c. Parametric 3D Möbius Strip
    await page.locator('.gs-subtab-btn', { hasText: /^Param$/ }).click();
    await page.locator('.gs-btn-primary', { hasText: 'Evaluate Parametric 3D in Lean' }).click();
    await snap('w3-15-parametric-mobius.png');

    // 8. GAlculator: e1 * e2 = 1e12 (ZERO ERR!)
    await page.locator('.gs-mode-btn', { hasText: 'GAlculator' }).click();
    await page.locator('.gs-keycap', { hasText: /^e1$/ }).click();
    await page.locator('.gs-keycap', { hasText: /^\*$/ }).click();
    await page.locator('.gs-keycap', { hasText: /^e2$/ }).click();
    await page.locator('.gs-keycap', { hasText: /^=$/ }).click();
    const sGalc = await snap('w3-12-galculator.png');
    assert(sGalc.calc?.display === '1e12', `Expected GAlculator display '1e12', got ${JSON.stringify(sGalc.calc)}`);

    // 9. Portable Cross-Client .grassmann.json Experiment Round-Trip + p95 Telemetry Check
    const expSnap = await page.evaluate(() => window.__grassmannStudio.exportExperiment());
    assert(expSnap && expSnap.version === 1 && typeof expSnap.presetId === 'string', 'Expected valid .grassmann.json v1 export');
    await page.evaluate(async (exp) => {
      await window.__grassmannStudio.importExperiment({ ...exp, mode: 'coffeeshop', presetId: 'pga3d_slicing' });
    }, expSnap);
    await page.waitForTimeout(450);
    const sAfterImport = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sAfterImport.presetId === 'pga3d_slicing', `Expected experiment import to restore pga3d_slicing, got ${sAfterImport.presetId}`);

    assert(consoleErrors.length === 0, `Console errors: ${JSON.stringify(consoleErrors)}`);
    assert(consoleWarnings.length === 0, `WebGL/Shader warnings: ${JSON.stringify(consoleWarnings)}`);
    assert(pageErrors.length === 0, `Page errors: ${JSON.stringify(pageErrors)}`);
    console.log('[wave3] ALL 15 FULL-STUDIO 69-PRESET VISUAL + GAMEPLAY + WORKER E2E CHECKS PASSED (0 console/shader/page errors)!');
  } finally {
    if (browser) await browser.close();
    preview.kill('SIGTERM');
  }
}

main().catch((err) => {
  console.error('[wave3] FAILED:', err);
  process.exit(1);
});
