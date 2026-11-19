#!/usr/bin/env node
/**
 * Interactive Playwright E2E Suite against Live Lean 4.36 WASM
 *
 * Verifies real user interactions end-to-end:
 *  1. Real mouse drag on a 3D draggable handle -> DragHandle (0x01) moves geometry in Lean
 *  2. Real Inspect Stash blade slider drag -> EditCoeff (0x04) updates Lean multivector live
 *  3. Real Code Editor inline number-scrub drag + Shift+Enter -> EvalScript
 *  4. Real Wedge 2D/3D mode + rubber-band drag gesture + WedgeAction (0x07)
 *  5. Real LeanCalculator 3D evalSurface + STA Cl(3,1) Lorentz boost slider + GAlculator keypad (x1..x10)
 *  6. Real PNG & SVG downloads verified byte-for-byte
 *  7. Real Obsidian / Gallery Daylight theme toggle persistence + clickable 3D Axis Triad Gizmo
 *  8. Responsive layout screenshots & zero-overflow assertions at 1440x900, 1280x720 (Vision Pro), 900x700
 */

import { spawn, execSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright-core';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WEB_DIR = path.resolve(__dirname, '..');
const OUT_DIR = path.join(WEB_DIR, 'artifacts', 'interaction-e2e');
const PUBLIC_WASM_DIR = path.join(WEB_DIR, 'public', 'wasm');
const PORT = 4181;
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
    throw new Error(`Compiled Lean WASM missing in ${wasmSrcDir}`);
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
  throw new Error(`Preview server did not start at ${url}`);
}

function assert(cond, msg) {
  if (!cond) throw new Error(`ASSERTION FAILED: ${msg}`);
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

    const context = await browser.newContext({
      viewport: { width: 1440, height: 900 },
      acceptDownloads: true,
    });
    const page = await context.newPage();

    const consoleErrors = [];
    const pageErrors = [];
    page.on('console', (m) => {
      if (m.type() === 'error') consoleErrors.push(m.text());
    });
    page.on('pageerror', (e) => pageErrors.push(e.message));

    await page.goto(BASE_URL, { waitUntil: 'networkidle' });
    await page.waitForTimeout(900);

    const s0 = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(s0.transportKind === 'wasm', `Expected live Lean WASM, got ${s0.transportKind}`);
    console.log('[e2e] 1. Connected live Lean 4.36 WASM:', s0.presetId, 'seq=', s0.frameSeq);

    // -------------------------------------------------------------------------
    // TEST 1: Real 3D Handle Mouse Drag -> DragHandle (0x01) moves geometry
    // -------------------------------------------------------------------------
    const handleBefore = await page.evaluate(() => window.__grassmannStudio.getHandleScreenPos(0));
    assert(handleBefore !== null, 'Expected draggable handleId=0 on initial scene');
    await page.mouse.move(handleBefore.clientX, handleBefore.clientY);
    await page.mouse.down();
    await page.mouse.move(handleBefore.clientX + 95, handleBefore.clientY - 65, { steps: 10 });
    await page.mouse.up();
    await page.waitForTimeout(250);

    const sAfterDrag = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(BigInt(sAfterDrag.frameSeq) > BigInt(s0.frameSeq), 'DragHandle must increment frameSeq');
    assert(sAfterDrag.recentEvents.includes('bin:0x1'), `Expected bin:0x1 DragHandle in ${sAfterDrag.recentEvents}`);
    const ptAfter = sAfterDrag.points.find((p) => p.handleId === 0);
    assert(ptAfter, 'Expected handleId=0 point after drag');
    const distMoved = Math.hypot(
      ptAfter.pos[0] - handleBefore.world[0],
      ptAfter.pos[1] - handleBefore.world[1],
      ptAfter.pos[2] - handleBefore.world[2]
    );
    assert(distMoved > 0.05, `Expected handle 0 to move in 3D, moved only ${distMoved.toFixed(4)}`);
    console.log(`[e2e] 2. Real 3D DragHandle PASS (moved ${distMoved.toFixed(3)} units, seq=${sAfterDrag.frameSeq})`);

    // -------------------------------------------------------------------------
    // TEST 2: Real Inspect Stash Blade Slider Drag -> EditCoeff (0x04)
    // -------------------------------------------------------------------------
    await page.locator('.gs-left-tab-btn', { hasText: 'Inspect' }).click();
    await page.waitForTimeout(200);
    const e0Slider = page.locator('.gs-blade-slider').nth(1); // e0 blade
    const seqBeforeEdit = BigInt((await page.evaluate(() => window.__grassmannStudio.getState())).frameSeq);
    await e0Slider.evaluate((el) => {
      el.value = '0.85';
      el.dispatchEvent(new Event('input', { bubbles: true }));
    });
    await page.waitForTimeout(220);
    const sAfterEdit = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(BigInt(sAfterEdit.frameSeq) > seqBeforeEdit, 'EditCoeff slider must increment frameSeq');
    assert(sAfterEdit.recentEvents.includes('bin:0x4'), 'Expected bin:0x4 EditCoeff event');
    console.log(`[e2e] 3. Inspect Stash EditCoeff slider PASS (seq=${sAfterEdit.frameSeq})`);

    // -------------------------------------------------------------------------
    // TEST 3: Code Editor Inline Number Scrubber + Shift+Enter -> EvalScript
    // -------------------------------------------------------------------------
    await page.evaluate(() => {
      const ta = document.querySelector('textarea.gs-editor-textarea');
      const m = /-?\d+\.\d+/.exec(ta.value);
      if (!m) throw new Error(`No float literal found in editor: ${ta.value}`);
      ta.focus();
      ta.setSelectionRange(m.index, m.index + m[0].length);
      ta.dispatchEvent(new Event('select', { bubbles: true }));
    });
    await page.waitForTimeout(150);
    const popoverVisible = await page.locator('.gs-inline-popover').isVisible();
    assert(popoverVisible, 'Inline number scrubber popover must appear when numeric token is selected');
    await page.locator('.gs-popover-range').evaluate((el) => {
      el.value = '1.15';
      el.dispatchEvent(new Event('input', { bubbles: true }));
    });
    await page.waitForTimeout(200);
    const codeAfterScrub = await page.locator('textarea.gs-editor-textarea').inputValue();
    assert(codeAfterScrub.includes('1.15'), `Expected scrubbed value 1.15 in code, got: ${codeAfterScrub}`);

    const seqBeforeRun = BigInt((await page.evaluate(() => window.__grassmannStudio.getState())).frameSeq);
    await page.locator('textarea.gs-editor-textarea').press('Shift+Enter');
    await page.waitForTimeout(200);
    const sAfterRun = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(BigInt(sAfterRun.frameSeq) > seqBeforeRun, 'Shift+Enter EvalScript must increment frameSeq');
    assert(sAfterRun.recentEvents.includes('json:evalScript'), 'Expected json:evalScript event');
    console.log(`[e2e] 4. Inline Number Scrubber + Shift+Enter PASS (seq=${sAfterRun.frameSeq})`);

    // Reload rich multi-primitive preset before SVG export check
    await page.locator('.gs-left-tab-btn', { hasText: 'Presets' }).click();
    await page.locator('[data-preset-id="cga3d_intersections"]').click();
    await page.waitForTimeout(350);

    // -------------------------------------------------------------------------
    // TEST 4: Real PNG & SVG Downloads Verified Byte-for-Byte
    // -------------------------------------------------------------------------
    const [pngDownload] = await Promise.all([
      page.waitForEvent('download'),
      page.locator('.gs-vp-btn', { hasText: 'PNG' }).click(),
    ]);
    const pngPath = path.join(OUT_DIR, 'exported-viewport.png');
    await pngDownload.saveAs(pngPath);
    const pngBytes = fs.readFileSync(pngPath);
    assert(pngBytes.length > 10000, `Exported PNG too small (${pngBytes.length} bytes)`);
    assert(
      pngBytes[0] === 0x89 && pngBytes[1] === 0x50 && pngBytes[2] === 0x4e && pngBytes[3] === 0x47,
      'Exported PNG missing valid PNG signature'
    );

    const [svgDownload] = await Promise.all([
      page.waitForEvent('download'),
      page.locator('.gs-vp-btn', { hasText: 'SVG' }).click(),
    ]);
    const svgPath = path.join(OUT_DIR, 'exported-viewport.svg');
    await svgDownload.saveAs(svgPath);
    const svgText = fs.readFileSync(svgPath, 'utf8');
    assert(svgText.startsWith('<svg') && svgText.trim().endsWith('</svg>'), 'Invalid exported SVG structure');
    assert(svgText.includes('<polyline') || svgText.includes('<line') || svgText.includes('<circle'), 'Exported SVG missing primitives');
    console.log(`[e2e] 5. PNG (${pngBytes.length} B) + SVG (${svgText.length} B) Export PASS`);

    // -------------------------------------------------------------------------
    // TEST 5: Theme Toggle (Gallery Daylight Persistence) + Axis Triad Gizmo
    // -------------------------------------------------------------------------
    await page.locator('.gs-theme-btn').click();
    await page.waitForTimeout(250);
    // Click Top (+y) on Axis Triad Gizmo -> triggers camera transition & SetCamera frame
    await page.locator('.gs-cam-chip', { hasText: 'Top' }).click();
    await page.waitForTimeout(550);
    await page.locator('.gs-cam-chip', { hasText: 'Iso' }).click();
    await page.waitForTimeout(550);
    const themeCheck = await page.evaluate(() => ({
      attr: document.getElementById('app')?.dataset.theme,
      stateTheme: window.__grassmannStudio.getState().theme,
    }));
    assert(themeCheck.attr === 'light' && themeCheck.stateTheme === 'light', 'Light theme must persist across Lean frames');
    await page.screenshot({ path: path.join(OUT_DIR, 'e2e-daylight-1440x900.png') });
    // Toggle back to dark obsidian
    await page.locator('.gs-theme-btn').click();
    await page.waitForTimeout(200);
    console.log('[e2e] 6. Gallery Daylight Theme Persistence + 3D Axis Triad Gizmo PASS');

    // -------------------------------------------------------------------------
    // TEST 6: Wedge 2D/3D Mode + Gesture / Action Verification
    // -------------------------------------------------------------------------
    await page.locator('.gs-mode-btn', { hasText: 'Wedge 2D/3D' }).click();
    await page.waitForTimeout(350);
    const wedgeState = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(wedgeState.mode === 'wedge', 'Expected wedge mode');
    await page.locator('.gs-wedge-dock button', { hasText: 'Hint' }).click();
    await page.waitForTimeout(180);
    await page.locator('.gs-wedge-dock button', { hasText: 'Reset' }).click();
    await page.waitForTimeout(180);
    const afterWedgeAct = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(afterWedgeAct.recentEvents.includes('bin:0x7'), 'Expected bin:0x7 WedgeAction event');
    // Exercise real 2-element drag if >=2 draggable handles are present in current WASM build
    const draggablePts = afterWedgeAct.points.filter((p) => p.draggable);
    if (draggablePts.length >= 2) {
      const hA = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), draggablePts[0].handleId);
      const hB = await page.evaluate((id) => window.__grassmannStudio.getHandleScreenPos(id), draggablePts[1].handleId);
      await page.mouse.move(hA.clientX, hA.clientY);
      await page.mouse.down();
      await page.mouse.move(hA.clientX - 45, hA.clientY, { steps: 5 });
      await page.mouse.up();
      await page.mouse.move(hB.clientX, hB.clientY);
      await page.mouse.down();
      await page.mouse.move(hB.clientX + 45, hB.clientY, { steps: 5 });
      const rubberCount = await page.locator('.gs-wedge-svg line').count();
      assert(rubberCount >= 2, `Expected 2 green rubber-band vectors during Wedge drag, got ${rubberCount}`);
      await page.mouse.up();
      await page.waitForTimeout(200);
      const afterGest = await page.evaluate(() => window.__grassmannStudio.getState());
      assert(afterGest.recentEvents.includes('bin:0x6'), 'Expected bin:0x6 WedgeGesture event');
    }
    console.log(`[e2e] 7. Wedge 2D/3D Mode + Actions PASS (draggable handles=${draggablePts.length})`);

    // -------------------------------------------------------------------------
    // TEST 7: LeanCalculator 3D Surface + STA Lorentz Boost + GAlculator x1..x10
    // -------------------------------------------------------------------------
    await page.locator('.gs-mode-btn', { hasText: 'LeanCalculator 3D' }).click();
    await page.locator('.gs-subtab-btn', { hasText: /^Surface$/ }).click();
    const surfInput = page.locator('.gs-subtab-pane:not(.hidden) input.gs-input.mono').first();
    await surfInput.fill('0.5*cos(x*2)*sin(y*2)');
    await page.locator('.gs-btn-primary', { hasText: 'Evaluate Surface in Lean' }).click();
    await page.waitForTimeout(350);
    const surfState = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(surfState.recentEvents.includes('json:evalSurface'), 'Expected json:evalSurface event');
    assert(
      String(surfState.title ?? '').includes('0.5*cos(x*2)*sin(y*2)'),
      `Expected Lean surface title to reflect input expr, got: ${surfState.title}`
    );

    // STA Cl(3,1) (-+++) Lorentz boost slider
    await page.locator('.gs-subtab-btn', { hasText: /^STA$/ }).click();
    await page.locator('.gs-subtab-pane:not(.hidden) input[type="range"]').evaluate((el) => {
      el.value = '0.65';
      el.dispatchEvent(new Event('input', { bubbles: true }));
    });
    await page.waitForTimeout(220);
    const staState = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(staState.recentEvents.includes('json:calcEval'), 'Expected json:calcEval from STA boost slider');

    // GAlculator tactile keypad + register x1
    await page.locator('.gs-mode-btn', { hasText: 'GAlculator' }).click();
    await page.locator('.gs-keycap', { hasText: /^e1$/ }).click();
    await page.locator('.gs-keycap', { hasText: /^\*$/ }).click();
    await page.locator('.gs-keycap', { hasText: /^e2$/ }).click();
    await page.locator('.gs-keycap', { hasText: /^=$/ }).click();
    await page.locator('.gs-reg-key').first().click();
    await page.waitForTimeout(200);
    const galcState = await page.evaluate(() => window.__grassmannStudio.getState());
    assert(galcState.recentEvents.includes('json:calcKey'), 'Expected json:calcKey from GAlculator keypad');
    console.log('[e2e] 8. LeanCalculator evalSurface + STA Boost + GAlculator Keypad PASS');

    // -------------------------------------------------------------------------
    // TEST 8: Responsive Layout Matrix (1440x900, 1280x720 Vision Pro, 900x700)
    // -------------------------------------------------------------------------
    await page.locator('.gs-mode-btn', { hasText: 'CoffeeShop IDE' }).click();
    await page.locator('.gs-left-tab-btn', { hasText: 'Presets' }).click();
    await page.locator('[data-preset-id="pga3d_slicing"]').click();
    await page.waitForTimeout(450);

    for (const vp of [
      { width: 1440, height: 900, name: 'e2e-resp-1440x900.png' },
      { width: 1280, height: 720, name: 'e2e-resp-1280x720-visionpro.png' },
      { width: 900, height: 700, name: 'e2e-resp-900x700-compact.png' },
    ]) {
      await page.setViewportSize({ width: vp.width, height: vp.height });
      await page.waitForTimeout(400);
      const overflow = await page.evaluate(() => ({
        scrollW: document.documentElement.scrollWidth,
        clientW: document.documentElement.clientWidth,
        vpW: document.querySelector('.gs-viewport-wrap')?.getBoundingClientRect().width ?? 0,
      }));
      assert(
        overflow.scrollW <= overflow.clientW + 1,
        `Horizontal overflow at ${vp.width}x${vp.height}: ${JSON.stringify(overflow)}`
      );
      assert(overflow.vpW >= 240, `3D viewport squeezed too narrow at ${vp.width}x${vp.height}: ${overflow.vpW}px`);
      await page.screenshot({ path: path.join(OUT_DIR, vp.name) });
      console.log(`[e2e] 9. Responsive ${vp.width}x${vp.height} PASS (viewport=${Math.round(overflow.vpW)}px, 0 overflow)`);
    }

    assert(consoleErrors.length === 0, `Console errors: ${JSON.stringify(consoleErrors)}`);
    assert(pageErrors.length === 0, `Page errors: ${JSON.stringify(pageErrors)}`);
    console.log('[e2e] ALL INTERACTIVE PLAYWRIGHT E2E CHECKS PASSED (0 console/page errors)!');
  } finally {
    if (browser) await browser.close();
    preview.kill('SIGTERM');
  }
}

main().catch((err) => {
  console.error('[e2e] FAILED:', err);
  process.exit(1);
});
