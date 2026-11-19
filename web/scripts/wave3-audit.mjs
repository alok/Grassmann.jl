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

function ensureStagedWasm() {
  const manifestPath = path.join(PUBLIC_WASM_DIR, 'wasm-manifest.json');
  if (!fs.existsSync(manifestPath)) {
    execSync('node scripts/stage-wasm.mjs', { cwd: WEB_DIR, stdio: 'inherit' });
  }
  const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
  const wasmPath = path.join(PUBLIC_WASM_DIR, manifest.wasmFile);
  const mjsPath = path.join(PUBLIC_WASM_DIR, manifest.loaderFile);
  if (!fs.existsSync(wasmPath) || !fs.existsSync(mjsPath)) {
    throw new Error(`Missing fingerprinted WASM files referenced by ${manifestPath}`);
  }
  return manifest;
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
  const stagedManifest = ensureStagedWasm();
  console.log(`[wave3] Using staged fingerprinted WASM hash=${stagedManifest.hash} (presets=${stagedManifest.presetCount ?? 'dynamic'})`);
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

    // 1. Dynamic Preset Catalog (77 presets!) + Lean Tour Catalog (6 stops) + Dedicated Web Worker WASM + Sculpted Bunny #pga3d_slicing + LiveScript v2 metaJson.script
    const s0 = await snap('w3-01-bunny-before.png');
    assert(s0.transportKind === 'wasm', 'Expected live Lean WASM');
    assert(/Worker/i.test(s0.transportLabel || ''), `Expected dedicated Web Worker WASM, got ${s0.transportLabel}`);
    assert(s0.presetCount >= 77, `Expected >=77 dynamic Lean presets, got ${s0.presetCount}`);
    assert(s0.leanTourCount === 6 && s0.tourCount === 6, `Expected 6 Lean Guided Tour stops, got lean=${s0.leanTourCount} ui=${s0.tourCount}`);
    assert(s0.handlesCount >= 2, `Expected >=2 draggable slice handles (Center + Tilt Normal) on #pga3d_slicing, got ${s0.handlesCount}`);
    assert(typeof s0.formula === 'string' && s0.formula.length > 0, `Expected Lean metaJson.formula on #pga3d_slicing, got ${JSON.stringify(s0.formula)}`);
    assert(typeof s0.summary === 'string' && s0.summary.length > 0, `Expected Lean metaJson.summary on #pga3d_slicing, got ${JSON.stringify(s0.summary)}`);
    assert(await page.locator('.gs-contour-pip').isVisible(), 'Expected sculpted bunny 2D slice contour PiP visible!');
    assert(typeof s0.metaScript === 'string' && s0.metaScript.length >= 60, `Expected Lean metaJson.script populated on #pga3d_slicing, got ${JSON.stringify(s0.metaScript)}`);
    assert(s0.script === s0.metaScript, 'Expected Code Editor synced directly to Lean metaJson.script');
    console.log(`[wave3] Dynamic Lean catalog synced: ${s0.presetCount} presets + ${s0.leanTourCount} tour stops via ${s0.transportLabel} (handles=${s0.handlesCount})`);

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

    // Drag slice handle 0 (Center) upward through bunny torso!
    const h0 = await page.evaluate(() => window.__grassmannStudio.getHandleScreenPos(0));
    assert(h0 !== null, 'Expected draggable slice handleId=0');
    await page.mouse.move(h0.clientX, h0.clientY);
    await page.mouse.down();
    await page.mouse.move(h0.clientX, h0.clientY - 70, { steps: 10 });
    await page.mouse.up();
    const sSliced = await snap('w3-02-bunny-sliced.png');

    // Wave 7A: Drag slice handle 1 (Amber Tilt Normal) obliquely to tilt cutting plane in 3D & update 2D Contour PiP!
    const h1 = await page.evaluate(() => window.__grassmannStudio.getHandleScreenPos(1));
    assert(h1 !== null, 'Expected draggable Tilt Normal handleId=1 on #pga3d_slicing');
    await page.mouse.move(h1.clientX, h1.clientY);
    await page.mouse.down();
    await page.mouse.move(h1.clientX + 95, h1.clientY + 45, { steps: 12 });
    await page.mouse.up();
    const sTilted = await snap('w7-01-bunny-tilted.png');
    assert(Number(sTilted.frameSeq) > Number(sSliced.frameSeq), 'Expected DragHandle 1 (Tilt Normal) to advance frameSeq');
    assert(await page.locator('.gs-contour-pip').isVisible(), 'Expected 2D Contour PiP visible after oblique plane tilt');
    console.log(`[wave3] Wave 7A Dual-Handle Tilted 3D Bunny PASS (seq ${sSliced.frameSeq} -> ${sTilted.frameSeq})`);

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

    // 7b. Implicit 3D Gyroid (Symmetric Kuhn Marching Tetrahedra Mesh + ZERO stale contour PiP, bytecode <10ms WASM Worker, AND live GPUInit GLSL3 Raymarch!)
    await page.locator('.gs-subtab-btn', { hasText: /^Imp 3D$/ }).click();
    await page.locator('.gs-seg-btn', { hasText: 'Marching Tet Mesh' }).click();
    await snap('w3-13-implicit-mesh.png');
    assert(!(await page.locator('.gs-contour-pip').isVisible()), 'Expected stale 2D Contour Overlay PiP CLEARED on evalImplicit!');
    const cMesh = await measureCanvas(page);
    assert(cMesh.variance >= 400 && cMesh.distinctColors >= 80, `Expected full symmetric Gyroid mesh, got ${JSON.stringify(cMesh)}`);

    const gyroidBench = await page.evaluate(() =>
      window.__grassmannStudio.benchmarkJson(
        {
          op: 'evalImplicit',
          expr: 'sin(x*2.2)*cos(y*2.2) + sin(y*2.2)*cos(z*2.2) + sin(z*2.2)*cos(x*2.2)',
          bounds: [-2.4, 2.4, -2.4, 2.4, -2.4, 2.4],
          gridN: 16,
          gpuRaymarch: false,
        },
        6
      )
    );
    console.log(`[wave3] Bytecode Gyroid 16^3 WASM Worker benchmark:`, gyroidBench);
    assert(gyroidBench.warmAvgMs < 10.0, `Expected warm bytecode Gyroid 16^3 < 10ms in WASM Worker, got ${JSON.stringify(gyroidBench)}`);

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
      await window.__grassmannStudio.importExperiment({
        ...exp,
        mode: 'coffeeshop',
        sceneKind: 'preset',
        presetId: 'pga3d_slicing',
      });
    }, expSnap);
    await page.waitForTimeout(450);
    const sAfterImport = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sAfterImport.presetId === 'pga3d_slicing', `Expected experiment import to restore pga3d_slicing, got ${sAfterImport.presetId}`);

    // 10. Wave 4B + Wave 5B UX Craft: 74-Preset Gallery Modal + ALL 5 Showstopper Presets + @param Sliders + LiveScript slider(...) + Zen Mode
    assert(await page.locator('.gs-formula-card').isVisible(), 'Expected KaTeX Formula Card visible on #pga3d_slicing');
    assert((await page.locator('.gs-formula-card .katex').count()) >= 1, 'Expected rendered KaTeX math in Formula Card');
    assert(await page.locator('.gs-timeline-bar').isVisible(), 'Expected Simulation Timeline Bar visible');

    // Open Visual Preset Gallery Modal (G) -> assert 77 dynamic Lean cards!
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.waitForTimeout(250);
    assert(await page.locator('.gs-gallery-modal').isVisible(), 'Expected Visual Preset Gallery Modal visible');
    const galleryCards = await page.locator('.gs-gallery-card').count();
    assert(galleryCards >= 77, `Expected >=77 visual preset gallery cards, got ${galleryCards}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'w4-01-gallery-modal.png') });
    console.log(`[wave3] Visual Preset Gallery Modal PASS (${galleryCards} cards)`);

    // Helper to scrub a floating @param range slider cleanly
    const scrubParamSlider = async (paramName, value) => {
      const slider = page.locator(`.gs-param-slider[data-param-name="${paramName}"]`);
      await slider.waitFor({ state: 'visible', timeout: 3000 });
      await slider.evaluate((el, val) => {
        el.value = String(val);
        el.dispatchEvent(new Event('input', { bubbles: true }));
      }, value);
      await page.waitForTimeout(350);
    };

    // 10a. Showstopper 1: pga3d_bouncing_cube -> verify gravity/restitution/spin @param sliders + KaTeX + live drag!
    await page.locator('[data-gallery-preset-id="pga3d_bouncing_cube"]').click();
    const sBounce0 = await snap('w5-01-bouncing-cube.png');
    assert(sBounce0.params.length >= 2, `Expected >=2 @param sliders on pga3d_bouncing_cube, got ${JSON.stringify(sBounce0.params)}`);
    assert(await page.locator('.gs-param-panel').isVisible(), 'Expected floating @param panel visible on pga3d_bouncing_cube');
    assert(typeof sBounce0.formula === 'string' && sBounce0.formula.length > 0, 'Expected Lean formula on pga3d_bouncing_cube');
    const firstBounceParam = sBounce0.params[0].name;
    const targetBounceVal = Math.min(sBounce0.params[0].max, sBounce0.params[0].min + (sBounce0.params[0].max - sBounce0.params[0].min) * 0.8);
    await scrubParamSlider(firstBounceParam, targetBounceVal);
    const sBounce1 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(Number(sBounce1.frameSeq) > Number(sBounce0.frameSeq), 'Expected setParam slider drag to advance frameSeq on pga3d_bouncing_cube');
    const updatedBounceParam = sBounce1.params.find((p) => p.name === firstBounceParam);
    assert(updatedBounceParam && Math.abs(updatedBounceParam.value - targetBounceVal) < 0.25, `Expected ${firstBounceParam} updated near ${targetBounceVal}, got ${JSON.stringify(updatedBounceParam)}`);
    console.log(`[wave3] Showcase 1 pga3d_bouncing_cube PASS | params=[${sBounce0.params.map((p) => p.name).join(', ')}]`);

    // 10b. Showstopper 2: pga3d_double_pendulum -> chaotic 3D trails + sliders + zero duplicate "Bob 2" label!
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="pga3d_double_pendulum"]').click();
    const sPend = await snap('w5-02-double-pendulum.png');
    assert(sPend.params.length >= 1, `Expected @param sliders on pga3d_double_pendulum, got ${JSON.stringify(sPend.params)}`);
    const bob2Labels = await page.locator('.gs-scene-label', { hasText: /^Bob 2$/ }).count();
    assert(bob2Labels === 1, `Expected exactly 1 deduplicated 'Bob 2' label, got ${bob2Labels}`);
    console.log(`[wave3] Showcase 2 pga3d_double_pendulum PASS | params=[${sPend.params.map((p) => p.name).join(', ')}]`);

    // 10c. Showstopper 3: sta_terrell_penrose -> relativistic Cl(3,1) cube vs dashed ghost + scrub beta -> 0.85!
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="sta_terrell_penrose"]').click();
    const sTP0 = await snap('w5-03a-terrell-penrose-default.png');
    assert(sTP0.params.some((p) => p.name === 'beta'), `Expected 'beta' @param on sta_terrell_penrose, got ${JSON.stringify(sTP0.params)}`);
    await scrubParamSlider('beta', 0.85);
    const sTP1 = await snap('w5-03b-terrell-penrose-beta85.png');
    const betaAfter = sTP1.params.find((p) => p.name === 'beta');
    assert(betaAfter && Math.abs(betaAfter.value - 0.85) < 0.03, `Expected beta=0.85 after scrub, got ${JSON.stringify(betaAfter)}`);
    console.log(`[wave3] Showcase 3 sta_terrell_penrose PASS | beta=${betaAfter.value}`);

    // 10d. Showstopper 4: sta_maxwell_streamlines -> velocity-colored 0x0D flow ribbons + 6 Faraday bivector disks!
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="sta_maxwell_streamlines"]').click();
    const sMax = await snap('w5-04-maxwell-streamlines.png');
    assert(sMax.flowCount > 0, `Expected 0x0D FLOW_PARTICLES on sta_maxwell_streamlines, got ${sMax.flowCount}`);
    assert(sMax.bivectorCount >= 6, `Expected >=6 Faraday bivector disks on sta_maxwell_streamlines, got ${sMax.bivectorCount}`);
    console.log(`[wave3] Showcase 4 sta_maxwell_streamlines PASS | flow=${sMax.flowCount} bivectors=${sMax.bivectorCount}`);

    // 10e. Showstopper 5: pga3d_hopf_streamlines -> Hopf fibration + PGA3 screw-motor flow ribbons!
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="pga3d_hopf_streamlines"]').click();
    const sHopf = await snap('w5-05-hopf-streamlines.png');
    assert(sHopf.flowCount > 0 || sHopf.curveCount > 0, `Expected Hopf flow ribbons/curves, got flow=${sHopf.flowCount} curves=${sHopf.curveCount}`);
    console.log(`[wave3] Showcase 5 pga3d_hopf_streamlines PASS | flow=${sHopf.flowCount} curves=${sHopf.curveCount}`);

    // 10f. LiveScript v2 slider("amp", 0.5, 0.1, 2.0) live execution + dynamic slider render + scrub!
    const liveSliderScript = [
      '@basis PGA3',
      'let amp = slider("amp", 0.5, 0.1, 2.0, 0.05, "Wave Amplitude")',
      'let A = point(-amp, 0.2, 0)',
      'let B = point(amp, 0.8, 0.3)',
      'let L = A & B',
      'let span = seg(A, B)',
    ].join('\n');
    await page.locator('.gs-editor-textarea').fill(liveSliderScript);
    await page.locator('.gs-editor-textarea').press('Shift+Enter');
    await page.waitForTimeout(450);
    const sLS0 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sLS0.diagnostics.length === 0, `LiveScript slider(...) had diagnostics: ${JSON.stringify(sLS0.diagnostics)}`);
    assert(sLS0.params.some((p) => p.name === 'amp'), `Expected dynamic 'amp' @param from LiveScript slider(...), got ${JSON.stringify(sLS0.params)}`);
    const ptBefore = sLS0.points[0]?.pos?.[0] ?? 0;
    await scrubParamSlider('amp', 1.65);
    const sLS1 = await snap('w5-06-livescript-slider.png');
    const ampAfter = sLS1.params.find((p) => p.name === 'amp');
    assert(ampAfter && Math.abs(ampAfter.value - 1.65) < 0.05, `Expected LiveScript amp=1.65 after scrub, got ${JSON.stringify(ampAfter)}`);
    const ptAfter = sLS1.points[0]?.pos?.[0] ?? 0;
    assert(Math.abs(ptAfter - ptBefore) > 0.5, `Expected LiveScript slider scrub to move 3D point A (before=${ptBefore}, after=${ptAfter})`);
    console.log(`[wave3] LiveScript v2 slider("amp") live execution + scrub PASS | amp=${ampAfter.value} A.x: ${ptBefore.toFixed(2)} -> ${ptAfter.toFixed(2)}`);

    // Enter Fullscreen Zen Mode (F) on sta_maxwell_streamlines -> verify unobstructed full-bleed viewport + Exit Zen pill!
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="sta_maxwell_streamlines"]').click();
    await page.waitForTimeout(450);
    await page.locator('.gs-vp-btn', { hasText: /Zen/ }).click();
    await page.waitForTimeout(350);
    assert(await page.locator('.gs-exit-zen-pill').isVisible(), 'Expected Exit Zen pill visible');
    const zenBox = await page.locator('canvas.gs-webgl-canvas').boundingBox();
    assert(zenBox && zenBox.width >= 1400 && zenBox.height >= 860, `Expected full-bleed Zen canvas >=1400x860, got ${JSON.stringify(zenBox)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'w4-02-zen-mode.png') });
    await page.locator('.gs-exit-zen-pill').click();
    await page.waitForTimeout(250);
    console.log(`[wave3] Fullscreen Zen Mode PASS (${Math.round(zenBox.width)}x${Math.round(zenBox.height)})`);

    // 11. Wave 7A Grand Finale Live Showcases & Functional Checks!
    // 11a. Barth Sextic (implicit_barth_sextic)
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="implicit_barth_sextic"]').click();
    const sBarth = await snap('w7-02-barth-sextic.png');
    assert(sBarth.opnsCount >= 1 || sBarth.meshCount >= 1, `Expected GPU OPNS or mesh on implicit_barth_sextic, got opns=${sBarth.opnsCount} mesh=${sBarth.meshCount}`);
    assert(sBarth.params.length >= 2, `Expected >=2 @param sliders (phi, iso) on implicit_barth_sextic, got ${JSON.stringify(sBarth.params)}`);
    console.log(`[wave3] Wave 7A Barth Sextic PASS | opns=${sBarth.opnsCount} params=[${sBarth.params.map((p) => p.name).join(', ')}]`);

    // 11b. CGA3 Dupin Cyclide GPU Raymarch (cga3d_dupin_cyclide_raymarch)
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="cga3d_dupin_cyclide_raymarch"]').click();
    const sCyclide = await snap('w7-03-dupin-cyclide-raymarch.png');
    assert(sCyclide.opnsCount >= 1, `Expected GPU OPNS shader on cga3d_dupin_cyclide_raymarch, got opns=${sCyclide.opnsCount}`);
    assert(sCyclide.params.length >= 2, `Expected >=2 @param sliders on cga3d_dupin_cyclide_raymarch, got ${JSON.stringify(sCyclide.params)}`);
    console.log(`[wave3] Wave 7A Dupin Cyclide Raymarch PASS | opns=${sCyclide.opnsCount} params=[${sCyclide.params.map((p) => p.name).join(', ')}]`);

    // 11c. Involute 3D Meshing Gears (pga3d_gears_kinematics)
    await page.locator('.gs-vp-btn', { hasText: /Gallery/ }).click();
    await page.locator('[data-gallery-preset-id="pga3d_gears_kinematics"]').click();
    const sGears = await snap('w7-04-gears-kinematics.png');
    assert(sGears.meshCount >= 1, `Expected 3D gear meshes on pga3d_gears_kinematics, got mesh=${sGears.meshCount}`);
    assert(sGears.params.length >= 1, `Expected @param sliders on pga3d_gears_kinematics, got ${JSON.stringify(sGears.params)}`);
    console.log(`[wave3] Wave 7A Involute 3D Gears PASS | meshes=${sGears.meshCount} params=[${sGears.params.map((p) => p.name).join(', ')}]`);

    // 11d. Live Lean resetTime === 0.0 exact (NOT 0.001!)
    await page.evaluate(() => window.__grassmannStudio.dispatchJson({ op: 'seekTime', t: 2.5 }));
    await page.waitForTimeout(250);
    const sSeek = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(Math.abs(sSeek.simTime - 2.5) < 0.05, `Expected seekTime(2.5) -> simTime~2.5, got ${sSeek.simTime}`);
    await page.locator('.gs-tl-reset').click();
    await page.waitForTimeout(250);
    const sReset = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sReset.simTime === 0, `Expected resetTime -> exact simTime===0.0 (not 0.001!), got ${sReset.simTime}`);
    console.log(`[wave3] Wave 7A Live resetTime PASS | seek=${sSeek.simTime.toFixed(2)} -> reset=${sReset.simTime}`);

    // 11e. Live Lean Guided Tour (T) via grassmann_studio_tour_catalog + loadTourStop
    await page.locator('.gs-vp-btn', { hasText: /Tour/ }).click();
    await page.waitForTimeout(350);
    assert(await page.locator('.gs-tour-card').isVisible(), 'Expected Guided Tour card visible');
    const sTour0 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sTour0.recentEvents.includes('json:loadTourStop'), `Expected json:loadTourStop dispatched, got ${JSON.stringify(sTour0.recentEvents)}`);
    await page.locator('.gs-tour-next').click();
    await page.waitForTimeout(350);
    const sTour1 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sTour1.tourStop === 1 && sTour1.presetId === 'pga3d_slicing', `Expected Tour stop 1 -> pga3d_slicing, got stop=${sTour1.tourStop} preset=${sTour1.presetId}`);
    await page.locator('.gs-tour-close').click();
    await page.waitForTimeout(200);
    console.log(`[wave3] Wave 7A Live Lean Tour PASS | 6 stops | loadTourStop verified`);

    // 11f. Dots P0 #5 Live GPU bound=4 sphere (x*x+y*y+z*z-9 visible outside old r=2.2 clip!)
    await page.evaluate(() =>
      window.__grassmannStudio.dispatchJson({
        op: 'evalImplicit',
        expr: 'x*x+y*y+z*z-9',
        gpuRaymarch: true,
        bound: 4,
        bounds: [-4, 4, -4, 4, -4, 4],
        gridN: 16,
        forceFullSnapshot: true,
      })
    );
    const sBound4 = await snap('w7-06-gpu-bound4-sphere.png');
    assert(sBound4.opnsCount >= 1, `Expected GPU OPNS raymarch for bound=4 sphere, got opns=${sBound4.opnsCount}`);
    const cBound4 = await measureCanvas(page);
    assert(cBound4.variance >= 120 && cBound4.distinctColors >= 25, `Expected visible radius-3 sphere at bound=4, got ${JSON.stringify(cBound4)}`);
    console.log(`[wave3] Wave 7A GPU bound=4 Sphere PASS | canvas=`, cBound4);

    // 11g. Wedge L17 (3D Euler Axis Grand Finale) + Dots P0 #4 Lossless 64-bit seedStr "9007199254740993" round-trip!
    await page.locator('.gs-mode-btn', { hasText: 'Wedge 2D/3D' }).click();
    await page.waitForTimeout(450);
    await page.locator('.gs-wedge-select').selectOption('17');
    const sL17 = await snap('w7-05-wedge-l17.png');
    assert(sL17.wedge && sL17.wedge.level === 17 && sL17.wedge.totalLevels >= 17 && sL17.wedge.is3D === true, `Expected Wedge L17 3D, got ${JSON.stringify(sL17.wedge)}`);
    console.log(`[wave3] Wave 7A Wedge L17 Grand Finale PASS | ${sL17.wedge.title} (${sL17.wedge.level}/${sL17.wedge.totalLevels})`);

    await page.evaluate(() =>
      window.__grassmannStudio.dispatchJson({
        op: 'wedgeRandom',
        dim: 3,
        difficulty: 2,
        seed: 0,
        seedStr: '9007199254740993',
        forceFullSnapshot: true,
      })
    );
    await page.waitForTimeout(350);
    const sSeed0 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sSeed0.wedge?.isRandom === true && sSeed0.wedge?.seedStr === '9007199254740993', `Expected Lean metaJson.wedge.seedStr === '9007199254740993', got ${JSON.stringify(sSeed0.wedge)}`);
    const expSeed = await page.evaluate(() => window.__grassmannStudio.exportExperiment());
    assert(expSeed.sceneKind === 'wedgeRandom' && expSeed.wedgeSeed === '9007199254740993', `Expected exported wedgeSeed === '9007199254740993', got ${JSON.stringify(expSeed)}`);
    await page.evaluate(() => window.__grassmannStudio.dispatchJson({ op: 'loadPreset', id: 'pga3d_slicing', forceFullSnapshot: true }));
    await page.waitForTimeout(250);
    await page.evaluate((exp) => window.__grassmannStudio.importExperiment(exp), expSeed);
    await page.waitForTimeout(400);
    const sSeed1 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sSeed1.wedge?.isRandom === true && sSeed1.wedge?.seedStr === '9007199254740993', `Expected restored wedge seedStr === '9007199254740993', got ${JSON.stringify(sSeed1.wedge)}`);
    console.log(`[wave3] Wave 7A Lossless 64-bit seedStr Round-Trip PASS | seedStr=${sSeed1.wedge.seedStr}`);

    // 12. Wave 8B/8C Dots Round-3 Fixpoint Verification Suite (36/36 full suite!)
    const runWave8 = process.env.WAVE8_FIXPOINT !== '0' && !process.argv.includes('--no-wave8');
    if (runWave8) {
      await page.locator('.gs-mode-btn', { hasText: 'CoffeeShop IDE' }).click();
      await page.waitForTimeout(250);

      // 12a. Signed/odd integer power in GPU raymarch: x^5 + 1 = 0 (x = -1 MUST be visible!)
      await page.evaluate(() =>
        window.__grassmannStudio.dispatchJson({
          op: 'evalImplicit',
          expr: 'x^5 + 1',
          gpuRaymarch: true,
          bound: 2,
          gridN: 16,
          forceFullSnapshot: true,
        })
      );
      const sOdd = await snap('w8-01-signed-odd-power.png');
      assert(sOdd.opnsCount >= 1, `Expected GPU OPNS shader for x^5+1, got ${sOdd.opnsCount}`);
      const cOdd = await measureCanvas(page);
      assert(cOdd.variance >= 100 && cOdd.distinctColors >= 20, `Expected visible x^5+1 plane at x=-1, got ${JSON.stringify(cOdd)}`);
      console.log(`[wave3] Wave 8 Signed Odd Power (x^5+1) PASS | canvas=`, cOdd);

      // 12b. Exact AABB [-bound, bound]^3 clipping: x - 1.5 @ bound=1 MUST clip empty, x - 15 @ bound=20 MUST render visibly!
      await page.evaluate(() =>
        window.__grassmannStudio.dispatchJson({
          op: 'evalImplicit',
          expr: 'x - 1.5',
          gpuRaymarch: true,
          bound: 1,
          gridN: 16,
          forceFullSnapshot: true,
        })
      );
      await page.waitForTimeout(550);
      await page.screenshot({ path: path.join(OUT_DIR, 'w8-02a-bound1-clipped.png') });
      const cClip1 = await measureCanvas(page);
      assert(cClip1.variance < 120, `Expected x-1.5 @ bound=1 clipped outside [-1,1]^3 AABB (empty), got ${JSON.stringify(cClip1)}`);

      await page.evaluate(() =>
        window.__grassmannStudio.dispatchJson({
          op: 'evalImplicit',
          expr: 'x - 15',
          gpuRaymarch: true,
          bound: 20,
          gridN: 16,
          forceFullSnapshot: true,
        })
      );
      const sBound20 = await snap('w8-02b-bound20-plane.png');
      assert(sBound20.opnsCount >= 1, `Expected GPU OPNS shader for x-15 @ bound=20, got ${sBound20.opnsCount}`);
      const cBound20 = await measureCanvas(page);
      assert(cBound20.variance >= 120 && cBound20.distinctColors >= 20, `Expected visible x-15 plane at bound=20, got ${JSON.stringify(cBound20)}`);
      console.log(`[wave3] Wave 8 AABB Clipping (bound=1 empty var=${cClip1.variance}, bound=20 visible var=${cBound20.variance}) PASS`);

      // 12c. Deterministic RK4 seekTime(2.5) replay on pga3d_bouncing_cube (visibly moves pose away from t=0!)
      await page.evaluate(() =>
        window.__grassmannStudio.dispatchJson({ op: 'loadPreset', id: 'pga3d_bouncing_cube', forceFullSnapshot: true })
      );
      await page.waitForTimeout(450);
      const sCube0 = await page.evaluate(() => window.__grassmannStudio.getState());
      const mat0 = sCube0.meshRefMatrices?.[0]?.mat4 ?? [];
      assert(mat0.length === 16, `Expected bouncing cube meshRef matrix at t=0, got ${mat0.length}`);
      await page.evaluate(() => window.__grassmannStudio.dispatchJson({ op: 'seekTime', t: 2.5, forceFullSnapshot: true }));
      const sCube25 = await snap('w8-03-bouncing-cube-seek25.png');
      assert(Math.abs(sCube25.simTime - 2.5) < 0.05, `Expected simTime=2.5 after seekTime, got ${sCube25.simTime}`);
      const mat25 = sCube25.meshRefMatrices?.[0]?.mat4 ?? [];
      const maxMatDelta = mat0.reduce((mx, v, i) => Math.max(mx, Math.abs(v - (mat25[i] ?? v))), 0);
      assert(maxMatDelta > 0.05, `Expected seekTime(2.5) to replay RK4 and move bouncing cube (maxMatDelta=${maxMatDelta})`);
      console.log(`[wave3] Wave 8 Deterministic RK4 seekTime(2.5) PASS | maxMatDelta=${maxMatDelta.toFixed(3)}`);

      // 12d. Non-overlapping meshing 3D involute gears (pga3d_gears_kinematics)
      await page.evaluate(() =>
        window.__grassmannStudio.dispatchJson({ op: 'loadPreset', id: 'pga3d_gears_kinematics', forceFullSnapshot: true })
      );
      const sGears8 = await snap('w8-04-gears-meshing.png');
      assert(sGears8.meshCount >= 3, `Expected 3 meshing 3D involute gears, got ${sGears8.meshCount}`);
      console.log(`[wave3] Wave 8 Involute Meshing Gears Visual Snapshot PASS | meshes=${sGears8.meshCount}`);
    }

    assert(consoleErrors.length === 0, `Console errors: ${JSON.stringify(consoleErrors)}`);
    assert(consoleWarnings.length === 0, `WebGL/Shader warnings: ${JSON.stringify(consoleWarnings)}`);
    assert(pageErrors.length === 0, `Page errors: ${JSON.stringify(pageErrors)}`);
    console.log(
      runWave8
        ? '[wave3] ALL 36 FULL-STUDIO 77-PRESET + WAVE 8 FIXPOINT R3 E2E CHECKS PASSED (0 console/shader/page errors)!'
        : '[wave3] ALL 32 FULL-STUDIO 77-PRESET + WAVE 7A SHOWCASE + TOUR + L17 + DOTS FIXES E2E CHECKS PASSED (0 console/shader/page errors)!'
    );
  } finally {
    if (browser) await browser.close();
    preview.kill('SIGTERM');
  }
}

main().catch((err) => {
  console.error('[wave3] FAILED:', err);
  process.exit(1);
});
