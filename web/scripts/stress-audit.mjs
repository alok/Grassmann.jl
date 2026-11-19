#!/usr/bin/env node
/**
 * Wave 6D Sustained 300-Frame Stress, Real RAF Paint Latency (p50/p95/p99),
 * WebGL/Heap Leak Audit, Dots Round 2 Regression Verification, Guided Tour,
 * Studio Floor Contact Shadow, & Multi-Level Interactive Wedge 2D + 3D Playthrough!
 */

import { spawn, execSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { chromium } from 'playwright-core';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WEB_DIR = path.resolve(__dirname, '..');
const OUT_DIR = path.join(WEB_DIR, 'artifacts', 'stress-audit');
const PUBLIC_WASM_DIR = path.join(WEB_DIR, 'public', 'wasm');
const PORT = 4189;
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

function assert(cond, msg) {
  if (!cond) throw new Error(`ASSERTION FAILED: ${msg}`);
}

function percentile(sorted, p) {
  if (sorted.length === 0) return 0;
  const idx = Math.min(sorted.length - 1, Math.floor((sorted.length - 1) * p));
  return Number(sorted[idx].toFixed(2));
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

async function verifyStandaloneFingerprintedLoader(manifest) {
  // Dots P0 #6: Direct ES import of fingerprinted loader WITHOUT locateFile must succeed with zero ENOENT!
  const loaderPath = path.join(PUBLIC_WASM_DIR, manifest.loaderFile);
  const modNs = await import(pathToFileURL(loaderPath).href);
  assert(typeof modNs.default === 'function', `Expected default Emscripten factory in ${manifest.loaderFile}`);
  const instance = await modNs.default();
  assert(instance._grassmann_initialize() === 0, 'grassmann_initialize failed');
  const session = instance._grassmann_studio_create();
  assert(session !== 0 && session !== 0n, 'grassmann_studio_create returned 0');
  instance._grassmann_studio_destroy(session);
  console.log(`[stress] 0. Dots P0 #6 Standalone fingerprinted loader smoke PASS (${manifest.loaderFile} -> ${manifest.wasmFile}, zero locateFile)`);
}

async function main() {
  fs.mkdirSync(OUT_DIR, { recursive: true });
  const manifestPath = path.join(PUBLIC_WASM_DIR, 'wasm-manifest.json');
  assert(fs.existsSync(manifestPath), `Missing ${manifestPath}`);
  const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));

  await verifyStandaloneFingerprintedLoader(manifest);
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
      args: [
        '--use-gl=angle',
        '--enable-webgl',
        '--ignore-gpu-blocklist',
        '--no-sandbox',
        '--enable-precise-memory-info',
      ],
    });

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

    const waitNextPaint = async () => {
      await page.evaluate(
        () => new Promise((r) => requestAnimationFrame(() => requestAnimationFrame(r)))
      );
    };

    const getHeapMb = async () =>
      page.evaluate(() => {
        const mem = performance.memory;
        return mem ? Number((mem.usedJSHeapSize / (1024 * 1024)).toFixed(2)) : null;
      });

    await page.goto(BASE_URL, { waitUntil: 'networkidle' });
    await page.waitForTimeout(900);

    const sInit = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sInit.transportKind === 'wasm' && sInit.presetCount >= 74, `Expected 74-preset WASM, got ${JSON.stringify(sInit)}`);

    // =========================================================================
    // 1. SUSTAINED 300-FRAME STRESS + REAL RAF p50/p95/p99 + WEBGL/HEAP LEAK AUDIT
    // =========================================================================
    await page.evaluate(() => window.__grassmannStudio.resetLatencySamples());
    const memStart = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());
    const heapStartMb = await getHeapMb();

    // 1a. 100 continuous 3D handle drags on #pga3d_slicing
    const h0 = await page.evaluate(() => window.__grassmannStudio.getHandleScreenPos(0));
    assert(h0 !== null, 'Expected handleId=0 on #pga3d_slicing');
    await page.mouse.move(h0.clientX, h0.clientY);
    await page.mouse.down();
    for (let i = 0; i < 100; i++) {
      const dy = Math.sin((i / 100) * Math.PI * 2) * 58;
      await page.mouse.move(h0.clientX, h0.clientY + dy);
      await waitNextPaint();
    }
    await page.mouse.up();
    const afterDrags = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());

    // 1b. 100 continuous @param scrubs on sta_terrell_penrose (beta 0.10..0.90)
    await page.evaluate(() =>
      window.__grassmannStudio.dispatchJson({ op: 'loadPreset', id: 'sta_terrell_penrose', forceFullSnapshot: true })
    );
    await page.waitForTimeout(350);
    const betaSlider = page.locator('.gs-param-slider[data-param-name="beta"]');
    await betaSlider.waitFor({ state: 'visible', timeout: 3000 });
    for (let i = 0; i < 100; i++) {
      const val = (0.1 + 0.8 * (0.5 + 0.5 * Math.sin((i / 100) * Math.PI * 2))).toFixed(3);
      await betaSlider.evaluate((el, v) => {
        el.value = v;
        el.dispatchEvent(new Event('input', { bubbles: true }));
      }, val);
      await waitNextPaint();
    }
    const afterParams = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());

    // 1c. 20 rapid preset switches across Bunny, Gyroid, Terrell-Penrose, Maxwell streamlines, OPNS cyclide, Bouncing Cube, Double Pendulum, Wedge!
    const switchCycle = [
      { op: 'loadPreset', id: 'pga3d_slicing', forceFullSnapshot: true },
      { op: 'evalImplicit', expr: 'sin(x*2.2)*cos(y*2.2)+sin(y*2.2)*cos(z*2.2)+sin(z*2.2)*cos(x*2.2)', gpuRaymarch: false, bound: 2.4, bounds: [-2.4, 2.4, -2.4, 2.4, -2.4, 2.4], gridN: 16 },
      { op: 'loadPreset', id: 'sta_terrell_penrose', forceFullSnapshot: true },
      { op: 'loadPreset', id: 'sta_maxwell_streamlines', forceFullSnapshot: true },
      { op: 'loadPreset', id: 'cga3d_opns_cyclide', forceFullSnapshot: true },
      { op: 'loadPreset', id: 'pga3d_bouncing_cube', forceFullSnapshot: true },
      { op: 'loadPreset', id: 'pga3d_double_pendulum', forceFullSnapshot: true },
      { op: 'loadPreset', id: 'game_wedge', forceFullSnapshot: true },
    ];
    let afterCycle1Info = null;
    for (let i = 0; i < 20; i++) {
      const ev = switchCycle[i % switchCycle.length];
      await page.evaluate((e) => window.__grassmannStudio.dispatchJson(e), ev);
      await waitNextPaint();
      if (i === switchCycle.length - 1) {
        afterCycle1Info = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());
      }
    }
    // Capture steady-state interactive RAF latency across 100 drags + 100 @param scrubs + 20 preset switches
    // (before intentional 40-shader cold ANGLE/Metal GLSL compile churn in 1d)
    const steadyInfo = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());
    const sortedLat = [...steadyInfo.samples].sort((a, b) => a - b);
    const p50 = percentile(sortedLat, 0.5);
    const p95 = percentile(sortedLat, 0.95);
    const p99 = percentile(sortedLat, 0.99);

    // 1d. Dots P1 #9 Live WebGL 40-Shader Bounded LRU Stress (40 distinct varying GPU implicit expressions!)
    for (let i = 0; i < 40; i++) {
      const k = (1.6 + i * 0.03).toFixed(3);
      await page.evaluate(
        (expr) =>
          window.__grassmannStudio.dispatchJson({
            op: 'evalImplicit',
            expr,
            gpuRaymarch: true,
            bound: 2.2,
            bounds: [-2.2, 2.2, -2.2, 2.2, -2.2, 2.2],
            gridN: 16,
          }),
        `sin(x*${k})*cos(y*${k}) + sin(y*${k})*cos(z*${k}) + sin(z*${k})*cos(x*${k})`
      );
      if (i % 4 === 0) await waitNextPaint();
    }
    await waitNextPaint();
    const after40Shaders = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());
    assert(
      after40Shaders.cachedOpnsShaders <= 24,
      `Expected bounded LRU OpnsShaderCache <= 24 after 40 distinct implicit shaders, got ${after40Shaders.cachedOpnsShaders}`
    );
    console.log(
      `[stress] 1d. Dots P1 #9 40-Shader Bounded LRU PASS | cachedOpnsShaders=${after40Shaders.cachedOpnsShaders} (<=24) | geometries=${after40Shaders.geometries} textures=${after40Shaders.textures}`
    );

    // Settle back on #pga3d_slicing for apples-to-apples WebGL memory comparison AFTER all 300+ frames & 40-shader churn
    await page.evaluate(() =>
      window.__grassmannStudio.dispatchJson({ op: 'loadPreset', id: 'pga3d_slicing', forceFullSnapshot: true })
    );
    await waitNextPaint();
    await page.waitForTimeout(250);

    const memEnd = await page.evaluate(() => window.__grassmannStudio.getRenderInfo());
    const heapEndMb = await getHeapMb();

    console.log(
      `[stress] 1. 300-Frame Stress Summary | samples=${sortedLat.length} | RAF i2p p50=${p50}ms p95=${p95}ms p99=${p99}ms`
    );
    console.log(
      `[stress]    WebGL Memory: start(geo=${memStart.geometries}, tex=${memStart.textures}) -> drags(geo=${afterDrags.geometries}) -> params(geo=${afterParams.geometries}) -> cycle1(geo=${afterCycle1Info.geometries}) -> end(geo=${memEnd.geometries}, tex=${memEnd.textures}, cachedMeshes=${memEnd.cachedMeshes}, labels=${memEnd.labelDomNodes})`
    );
    console.log(`[stress]    JS Heap: start=${heapStartMb} MB -> end=${heapEndMb} MB`);

    assert(sortedLat.length >= 180, `Expected >=180 RAF input-to-present samples across stress run, got ${sortedLat.length}`);
    assert(p50 < 25, `Expected p50 input-to-present < 25ms, got ${p50}ms`);
    assert(p95 < 55, `Expected p95 input-to-present < 55ms, got ${p95}ms`);
    assert(memEnd.cachedMeshes <= 24, `Expected LRU mesh cache <= 24, got ${memEnd.cachedMeshes}`);
    // Bounded WebGL geometry & texture delta (only bounded LRU cache growth, ZERO leak across cycles!)
    assert(
      memEnd.geometries - memStart.geometries <= 36,
      `WebGL geometry leak detected: ${memStart.geometries} -> ${memEnd.geometries}`
    );
    assert(
      memEnd.textures - memStart.textures <= 4,
      `WebGL texture leak detected: ${memStart.textures} -> ${memEnd.textures}`
    );
    assert(memEnd.labelDomNodes <= 12, `CSS2D label DOM leak detected: ${memEnd.labelDomNodes}`);
    if (heapStartMb !== null && heapEndMb !== null) {
      assert(heapEndMb - heapStartMb < 90, `JS heap grew excessively: ${heapStartMb} -> ${heapEndMb} MB`);
    }

    // =========================================================================
    // 2. DOTS P0 #4 LIVE EXPERIMENT RESTORE + P1 #10 TIMELINE OPS + P2 #11 SPACE GUARD
    // =========================================================================
    await page.locator('.gs-mode-btn', { hasText: 'CoffeeShop IDE' }).click();
    const customCode = '@basis PGA3\nlet amp = slider("amp", 1.35, 0.2, 2.0)\nlet A = point(-amp, 0.3, 0)\nlet B = point(amp, 0.3, 0)\nlet L = A & B';
    await page.locator('.gs-editor-textarea').fill(customCode);
    await page.locator('.gs-editor-textarea').press('Shift+Enter');
    await page.waitForTimeout(350);

    const exportedScript = await page.evaluate(() => window.__grassmannStudio.exportExperiment());
    assert(exportedScript.sceneKind === 'script', `Expected sceneKind='script', got ${exportedScript.sceneKind}`);
    assert(exportedScript.presetId !== 'custom_script', `presetId must NEVER be 'custom_script', got ${exportedScript.presetId}`);

    // Switch away to Bunny, then re-import custom script -> MUST restore custom script (NOT Bunny!)
    await page.locator('[data-preset-id="pga3d_slicing"]').click();
    await page.waitForTimeout(350);
    await page.evaluate((exp) => window.__grassmannStudio.importExperiment(exp), exportedScript);
    await page.waitForTimeout(450);
    const sRestored = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sRestored.sceneKind === 'script', `Expected restored sceneKind='script', got ${sRestored.sceneKind}`);
    assert(sRestored.params.some((p) => p.name === 'amp'), `Expected custom script 'amp' slider restored (not Bunny!), got ${JSON.stringify(sRestored.params)}`);
    console.log('[stress] 2a. Dots P0 #4 Live custom script .grassmann.json export/import restore PASS');

    // Dots P1 #10: Timeline Reset & Scrub dispatch explicit json:resetTime and json:seekTime
    await page.locator('.gs-tl-slider').evaluate((el) => {
      el.value = '3.50';
      el.dispatchEvent(new Event('input', { bubbles: true }));
    });
    await page.waitForTimeout(180);
    await page.locator('.gs-tl-reset').click();
    await page.waitForTimeout(180);
    const sTl = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sTl.recentEvents.includes('json:seekTime'), `Expected json:seekTime dispatched, got ${JSON.stringify(sTl.recentEvents)}`);
    assert(sTl.recentEvents.includes('json:resetTime'), `Expected json:resetTime dispatched, got ${JSON.stringify(sTl.recentEvents)}`);
    console.log('[stress] 2b. Dots P1 #10 Timeline seekTime + resetTime dispatch PASS');

    // =========================================================================
    // 3. INTERACTIVE 6-STOP GUIDED GA TOUR (T) & STUDIO FLOOR CONTACT SHADOW
    // =========================================================================
    await page.locator('[data-preset-id="pga3d_slicing"]').click();
    await page.waitForTimeout(400);
    const floorBefore = await page.evaluate(() => window.__grassmannStudio.getRenderInfo().floorShadowVisible);
    assert(floorBefore === true, 'Expected Studio Floor contact shadow visible in 3D mode');
    await page.locator('.gs-vp-btn', { hasText: /^Floor$/ }).click();
    const floorOff = await page.evaluate(() => window.__grassmannStudio.getRenderInfo().floorShadowVisible);
    assert(floorOff === false, 'Expected Floor button to toggle studio floor shadow off');
    await page.locator('.gs-vp-btn', { hasText: /^Floor$/ }).click();

    // Gallery Daylight screenshot with subtle architectural plinth contact shadow!
    await page.locator('.gs-theme-btn').click();
    await page.waitForTimeout(450);
    await page.screenshot({ path: path.join(OUT_DIR, 'w6-02-floor-daylight.png') });
    // Back to Obsidian Dark
    await page.locator('.gs-theme-btn').click();
    await page.waitForTimeout(350);

    // Open Guided Tour via keyboard shortcut 'T', step through stops 0 -> 1 (Bunny) -> 4 (Terrell-Penrose)!
    await page.locator('canvas.gs-webgl-canvas').click({ position: { x: 20, y: 20 } });
    await page.keyboard.press('t');
    await page.waitForTimeout(400);
    assert(await page.locator('.gs-tour-card').isVisible(), 'Expected Guided Tour card visible after pressing T');
    assert((await page.locator('.gs-tour-formula .katex').count()) >= 1, 'Expected KaTeX formula in Guided Tour');
    await page.locator('.gs-tour-next').click(); // Stop 2: 3D Bunny Plane Slicing
    await page.waitForTimeout(500);
    await page.screenshot({ path: path.join(OUT_DIR, 'w6-01-tour-bunny.png') });
    await page.keyboard.press('Escape');
    await page.waitForTimeout(200);
    assert(!(await page.locator('.gs-tour-card').isVisible()), 'Expected Esc to close Guided Tour card');
    console.log('[stress] 3. Guided 6-Stop GA Tour (T/Next/Esc) + Studio Floor Contact Shadow PASS');

    // =========================================================================
    // 4. MULTI-LEVEL INTERACTIVE WEDGE 2D & 3D PLAYTHROUGH (5 LEVELS!) + DOTS P2 #11 SPACE CHECK
    // =========================================================================
    await page.locator('.gs-mode-btn', { hasText: 'Wedge 2D/3D' }).click();
    await page.waitForTimeout(550);

    // Verify floor contact shadow auto-disables in 2D ortho Wedge mode!
    const floorIn2D = await page.evaluate(() => window.__grassmannStudio.getRenderInfo().floorShadowVisible);
    assert(floorIn2D === false, 'Expected Studio Floor shadow auto-disabled in 2D ortho Wedge mode');

    // Dots P2 #11: Focus Wedge Hint button and press Space -> activates button (shows hint) WITHOUT toggling Play/Pause!
    const hintBtn = page.locator('.gs-wedge-dock button', { hasText: /Hint/ });
    await hintBtn.focus();
    await page.keyboard.press('Space');
    await page.waitForTimeout(250);
    const sAfterSpaceOnBtn = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sAfterSpaceOnBtn.animRunning === false, 'Dots P2 #11: Pressing Space on focused Wedge Hint button must NOT toggle Play/Pause!');
    assert(await page.locator('.gs-wedge-hint').isVisible(), 'Dots P2 #11: Pressing Space on focused Wedge Hint button should activate Hint!');
    console.log('[stress] 4a. Dots P2 #11 Focused Button Space Accessibility PASS (Hint activated, animRunning=false)');

    const clickPairAndOp = async (idA, idB, op) => {
      const hA = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), idA);
      const hB = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), idB);
      assert(hA && hB, `Missing screen coords for handles ${idA} & ${idB}`);
      await page.mouse.click(hA.clientX, hA.clientY);
      await page.waitForTimeout(140);
      await page.mouse.click(hB.clientX, hB.clientY);
      await page.waitForTimeout(180);
      assert(await page.locator('.gs-wedge-armed').isVisible(), `Expected Armed bar visible after clicking ${idA} & ${idB}`);
      await page.locator(`.gs-wedge-op-btn[data-wedge-op="${op}"]`).click();
      await page.waitForTimeout(420);
    };

    // Level 1 (Index 0): L1 · Join (A & B) — real mouse drag pull-apart!
    const hL1 = await page.evaluate(() => window.__grassmannStudio.getAllInteractiveHandles());
    assert(hL1.length >= 2, `Expected >=2 handles on L1, got ${hL1.length}`);
    await page.mouse.move(hL1[0].clientX, hL1[0].clientY);
    await page.mouse.down();
    await page.mouse.move(hL1[0].clientX - 95, hL1[0].clientY + 25, { steps: 8 });
    await page.mouse.up();
    await page.mouse.move(hL1[1].clientX, hL1[1].clientY);
    await page.mouse.down();
    await page.mouse.move(hL1[1].clientX + 95, hL1[1].clientY - 25, { steps: 8 });
    await page.mouse.up();
    await page.waitForTimeout(400);
    const sL1 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sL1.wedge?.level === 1 && sL1.wedge?.solved === true, `L1 Join not solved: ${JSON.stringify(sL1.wedge)}`);
    console.log(`[stress] 4b. Wedge L1 Join SOLVED (moves=${sL1.wedge.moves}, score=${sL1.wedge.score})`);

    // Level 2: L2 · Meet (a ^ b) — click line a + click line b -> Meet!
    await page.locator('.gs-wedge-select').selectOption('2');
    await page.waitForTimeout(450);
    const hL2 = await page.evaluate(() => window.__grassmannStudio.getAllInteractiveHandles());
    assert(hL2.length >= 2, `Expected >=2 interactive lines on L2, got ${JSON.stringify(hL2)}`);
    await clickPairAndOp(hL2[0].handleId, hL2[1].handleId, 'meet');
    const sL2 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sL2.wedge?.level === 2 && sL2.wedge?.solved === true, `L2 Meet not solved: ${JSON.stringify(sL2.wedge)}`);
    console.log(`[stress] 4c. Wedge L2 Meet SOLVED (moves=${sL2.wedge.moves}, score=${sL2.wedge.score})`);

    // Level 3: L3 · Add Points (Midpoint A + B) — click A + click B -> Add +!
    await page.locator('.gs-wedge-select').selectOption('3');
    await page.waitForTimeout(450);
    const hL3 = await page.evaluate(() => window.__grassmannStudio.getAllInteractiveHandles());
    assert(hL3.length >= 2, `Expected >=2 interactive points on L3, got ${JSON.stringify(hL3)}`);
    await clickPairAndOp(hL3[0].handleId, hL3[1].handleId, 'add');
    const sL3 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sL3.wedge?.level === 3 && sL3.wedge?.solved === true, `L3 Add Midpoint not solved: ${JSON.stringify(sL3.wedge)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'w6-03-wedge-l3-midpoint.png') });
    console.log(`[stress] 4d. Wedge L3 Add Midpoint SOLVED (moves=${sL3.wedge.moves}, score=${sL3.wedge.score})`);

    // Level 5: L5 · Dot / Orthogonal Projection (a << B) — click line a + click point B -> Dot!
    await page.locator('.gs-wedge-select').selectOption('5');
    await page.waitForTimeout(450);
    const hL5 = await page.evaluate(() => window.__grassmannStudio.getAllInteractiveHandles());
    assert(hL5.length >= 2, `Expected >=2 interactive elements on L5, got ${JSON.stringify(hL5)}`);
    await clickPairAndOp(hL5[0].handleId, hL5[1].handleId, 'dot');
    const sL5 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sL5.wedge?.level === 5 && sL5.wedge?.solved === true, `L5 Dot Projection not solved: ${JSON.stringify(sL5.wedge)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'w6-04-wedge-l5-dot.png') });
    console.log(`[stress] 4e. Wedge L5 Dot Projection SOLVED (moves=${sL5.wedge.moves}, score=${sL5.wedge.score})`);

    // Level 10: Wedge 3D L10 · 3D Join (A & B -> Line, Line & C -> Red Plane)!
    await page.locator('.gs-wedge-select').selectOption('10');
    await page.waitForTimeout(550);
    const hL10a = await page.evaluate(() => window.__grassmannStudio.getAllInteractiveHandles());
    assert(hL10a.length >= 3, `Expected 3 draggable points A,B,C on Wedge 3D L10, got ${JSON.stringify(hL10a)}`);
    // Step 1: Join A & B -> 3D line
    await clickPairAndOp(hL10a[0].handleId, hL10a[1].handleId, 'join');
    // Step 2: Find the newly constructed 3D line + remaining point C -> Join -> Plane SOLVED!
    const hL10b = await page.evaluate(() => window.__grassmannStudio.getAllInteractiveHandles());
    const lineHandle = hL10b.find((h) => h.kind === 'line');
    assert(lineHandle, `Expected constructed 3D line handle on Wedge 3D L10, got ${JSON.stringify(hL10b)}`);
    await clickPairAndOp(lineHandle.handleId, hL10a[2].handleId, 'join');
    const sL10 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(sL10.wedge?.level === 10 && sL10.wedge?.is3D === true && sL10.wedge?.solved === true, `Wedge 3D L10 not solved: ${JSON.stringify(sL10.wedge)}`);
    await page.screenshot({ path: path.join(OUT_DIR, 'w6-05-wedge3d-l10-solved.png') });
    console.log(`[stress] 4f. Wedge 3D L10 (2-step Line + Plane) SOLVED (moves=${sL10.wedge.moves}, score=${sL10.wedge.score})`);

    assert(consoleErrors.length === 0, `Console errors: ${JSON.stringify(consoleErrors)}`);
    assert(consoleWarnings.length === 0, `WebGL/Shader warnings: ${JSON.stringify(consoleWarnings)}`);
    assert(pageErrors.length === 0, `Page errors: ${JSON.stringify(pageErrors)}`);
    console.log('[stress] ALL WAVE 6D 300-FRAME STRESS + LEAK + 40-SHADER LRU + DOTS P0/P1/P2 + TOUR + 5-LEVEL WEDGE 2D/3D CHECKS PASSED (0 errors)!');
  } finally {
    if (browser) await browser.close();
    preview.kill('SIGTERM');
  }
}

main().catch((err) => {
  console.error('[stress] FAILED:', err);
  process.exit(1);
});
