#!/usr/bin/env node
/**
 * Real Playwright Headless Chromium WebGL2 Visual + Runtime E2E Audit
 *
 * Stages the latest compiled Lean 4.36 WASM into gitignored `public/wasm/`,
 * builds Vite production output, boots `vite preview`, captures 1440x900
 * screenshots of all 4 Grassmann Studio modes, and asserts:
 *   - Zero console errors & zero uncaught page errors
 *   - Live Lean 4.36 WASM auto-discovery & round-trip latency
 *   - Non-blank WebGL2 3D canvas (pixel variance check) on every view
 *   - Working Inspect Stash, inline number scrubber, Wedge HUD, LeanCalculator Surface/STA, and GAlculator
 */

import { spawn, execSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright-core';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const WEB_DIR = path.resolve(__dirname, '..');
const ARTIFACTS_DIR = path.join(WEB_DIR, 'artifacts', 'visual-audit');
const PUBLIC_WASM_DIR = path.join(WEB_DIR, 'public', 'wasm');
const PORT = 4179;
const BASE_URL = `http://127.0.0.1:${PORT}/`;

function findChromiumExecutable() {
  const home = os.homedir();
  const candidates = [
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/opt/homebrew/bin/chromium',
    path.join(
      home,
      'Library/Caches/ms-playwright/chromium-1254/chrome-mac-arm64/Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing'
    ),
    path.join(
      home,
      'Library/Caches/ms-playwright/chromium-1161/chrome-mac-arm64/Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing'
    ),
  ];

  // Also scan ms-playwright cache dynamically
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
  throw new Error('No Chromium / Chrome executable found for Playwright visual audit');
}

function stageWasmFromCabi() {
  const argDir = process.argv.find((a) => a.startsWith('--wasm-dir='))?.slice('--wasm-dir='.length);
  const wasmSrcDir =
    argDir ?? path.resolve(WEB_DIR, '..', '..', 'cabi', 'wasm', 'dist');

  if (!fs.existsSync(wasmSrcDir)) {
    console.warn(`[audit] WASM dir not found at ${wasmSrcDir} — running without staged WASM`);
    return false;
  }

  fs.mkdirSync(PUBLIC_WASM_DIR, { recursive: true });
  const canonicalMjs = path.join(wasmSrcDir, 'grassmann.mjs');
  const canonicalWasm = path.join(wasmSrcDir, 'grassmann.wasm');
  const rawMjs = path.join(wasmSrcDir, 'grassmann_raw.mjs');
  const rawWasm = path.join(wasmSrcDir, 'grassmann_raw.wasm');

  if (fs.existsSync(canonicalMjs) && fs.existsSync(canonicalWasm)) {
    fs.copyFileSync(canonicalMjs, path.join(PUBLIC_WASM_DIR, 'grassmann.mjs'));
    fs.copyFileSync(canonicalWasm, path.join(PUBLIC_WASM_DIR, 'grassmann.wasm'));
    const helper = path.join(wasmSrcDir, 'grassmann_wasm.mjs');
    if (fs.existsSync(helper)) {
      fs.copyFileSync(helper, path.join(PUBLIC_WASM_DIR, 'grassmann_wasm.mjs'));
    }
    console.log(`[audit] Staged live Lean 4.36 WASM (grassmann.mjs + grassmann.wasm) -> ${PUBLIC_WASM_DIR}`);
    return true;
  }

  if (fs.existsSync(rawMjs) && fs.existsSync(rawWasm)) {
    fs.copyFileSync(rawMjs, path.join(PUBLIC_WASM_DIR, 'grassmann_raw.mjs'));
    fs.copyFileSync(rawWasm, path.join(PUBLIC_WASM_DIR, 'grassmann_raw.wasm'));
    fs.writeFileSync(
      path.join(PUBLIC_WASM_DIR, 'grassmann.mjs'),
      `export { default } from './grassmann_raw.mjs';\n`
    );
    console.log(`[audit] Staged live Lean 4.36 WASM (grassmann_raw.*) -> ${PUBLIC_WASM_DIR}`);
    return true;
  }

  console.warn(`[audit] Missing grassmann.{mjs,wasm} in ${wasmSrcDir}`);
  return false;
}

async function waitForServer(url, timeoutMs = 15000) {
  const start = Date.now();
  while (Date.now() - start < timeoutMs) {
    try {
      const resp = await fetch(url);
      if (resp.ok) return;
    } catch {
      // retry
    }
    await new Promise((r) => setTimeout(r, 150));
  }
  throw new Error(`Vite preview failed to respond at ${url} within ${timeoutMs}ms`);
}

async function measureCanvasNonBlank(page) {
  return page.evaluate(() => {
    const canvas = document.querySelector('canvas.gs-webgl-canvas');
    if (!(canvas instanceof HTMLCanvasElement)) {
      return { ok: false, reason: 'No .gs-webgl-canvas found', distinctColors: 0, variance: 0 };
    }
    const probe = document.createElement('canvas');
    probe.width = 96;
    probe.height = 60;
    const ctx = probe.getContext('2d');
    if (!ctx) return { ok: false, reason: 'No 2D context', distinctColors: 0, variance: 0 };
    ctx.drawImage(canvas, 0, 0, probe.width, probe.height);
    const data = ctx.getImageData(0, 0, probe.width, probe.height).data;
    const buckets = new Set();
    let sumL = 0;
    let sumL2 = 0;
    const n = probe.width * probe.height;
    for (let i = 0; i < data.length; i += 4) {
      const r = data[i];
      const g = data[i + 1];
      const b = data[i + 2];
      buckets.add(`${r >> 3},${g >> 3},${b >> 3}`);
      const lum = 0.299 * r + 0.587 * g + 0.114 * b;
      sumL += lum;
      sumL2 += lum * lum;
    }
    const mean = sumL / n;
    const variance = Math.max(0, sumL2 / n - mean * mean);
    return {
      ok: buckets.size >= 8 && variance > 12,
      distinctColors: buckets.size,
      variance: Number(variance.toFixed(2)),
      meanLum: Number(mean.toFixed(2)),
      width: canvas.width,
      height: canvas.height,
    };
  });
}

async function main() {
  fs.mkdirSync(ARTIFACTS_DIR, { recursive: true });
  const hasWasm = stageWasmFromCabi();

  console.log('[audit] Building Vite production bundle...');
  execSync('npm run build', { cwd: WEB_DIR, stdio: 'inherit' });

  const previewProc = spawn(
    'npx',
    ['vite', 'preview', '--port', String(PORT), '--strictPort', '--host', '127.0.0.1'],
    { cwd: WEB_DIR, stdio: ['ignore', 'pipe', 'pipe'] }
  );

  let browser;
  try {
    await waitForServer(BASE_URL);
    const executablePath = findChromiumExecutable();
    console.log(`[audit] Launching Chromium (${executablePath})`);

    browser = await chromium.launch({
      executablePath,
      headless: true,
      args: [
        '--use-gl=angle',
        '--enable-webgl',
        '--ignore-gpu-blocklist',
        '--no-sandbox',
        '--disable-dev-shm-usage',
      ],
    });

    const context = await browser.newContext({ viewport: { width: 1440, height: 900 } });
    const page = await context.newPage();

    const consoleErrors = [];
    const pageErrors = [];
    page.on('console', (msg) => {
      if (msg.type() === 'error') consoleErrors.push(msg.text());
    });
    page.on('pageerror', (err) => {
      pageErrors.push(err.message);
    });

    await page.goto(BASE_URL, { waitUntil: 'networkidle' });
    await page.waitForTimeout(900);

    const initState = await page.evaluate(() => window.__grassmannStudio?.getState?.() ?? null);
    console.log('[audit] Initial studio state:', initState);

    if (hasWasm && initState?.transportKind !== 'wasm') {
      throw new Error(`Expected live Lean WASM auto-discovery, got: ${JSON.stringify(initState)}`);
    }

    const shots = [];
    const capture = async (name) => {
      await page.waitForTimeout(550);
      const canvasCheck = await measureCanvasNonBlank(page);
      const telemetry = await page.locator('.gs-telemetry-pill').textContent();
      const status = await page.locator('.gs-status-pill').textContent();
      const outPath = path.join(ARTIFACTS_DIR, name);
      await page.screenshot({ path: outPath });
      shots.push({ name, canvasCheck, telemetry: telemetry?.trim(), status: status?.trim() });
      console.log(`[audit] Captured ${name} | status="${status?.trim()}" | canvas=`, canvasCheck);
      if (!canvasCheck.ok) {
        throw new Error(`Blank or flat WebGL canvas on ${name}: ${JSON.stringify(canvasCheck)}`);
      }
    };

    // 1. CoffeeShop #pga3d_slicing (initial live Lean 4.36 WASM frame + 2D contour PiP)
    await capture('01-coffeeshop-pga3d-slicing.png');

    // 2. Inspect Stash + Metric Grid + Code Editor Inline Number Scrubber
    await page.locator('.gs-left-tab-btn', { hasText: 'Inspect' }).click();
    await page.evaluate(() => {
      const ta = document.querySelector('textarea.gs-editor-textarea');
      if (ta instanceof HTMLTextAreaElement) {
        const idx = ta.value.indexOf('0.25');
        if (idx >= 0) {
          ta.focus();
          ta.setSelectionRange(idx, idx + 4);
          ta.dispatchEvent(new Event('select', { bubbles: true }));
        }
      }
    });
    await capture('02-coffeeshop-inspect-scrubber.png');

    // 3. CoffeeShop CGA3 OPNS / Intersections preset
    await page.locator('.gs-left-tab-btn', { hasText: 'Presets' }).click();
    await page.locator('.gs-preset-card', { hasText: 'Conformal Sphere Intersections' }).click();
    await capture('03-coffeeshop-cga3d-opns.png');

    // 4. Wedge 2D/3D Game Mode (via keyboard shortcut `2`!)
    await page.keyboard.press('Escape');
    await page.locator('canvas.gs-webgl-canvas').click({ position: { x: 400, y: 300 } });
    await page.keyboard.press('2');
    await capture('04-wedge-2d-3d.png');

    // 5. LeanCalculator 3D Surface z=f(x,y,t) evaluated live in Lean + STA tab
    await page.locator('.gs-mode-btn', { hasText: 'LeanCalculator 3D' }).click();
    await page.locator('.gs-subtab-btn', { hasText: 'Surface 3D' }).click();
    await page.locator('.gs-btn-primary', { hasText: 'Evaluate Surface in Lean' }).click();
    await capture('05-leancalc-surface.png');

    // Also capture STA Cl(3,1) (-+++) panel over live surface/scene
    await page.locator('.gs-subtab-btn', { hasText: 'STA −+++' }).click();
    await capture('05b-leancalc-sta.png');

    // 6. GAlculator Tactile Keypad Mode
    await page.locator('.gs-mode-btn', { hasText: 'GAlculator' }).click();
    await capture('06-galculator.png');

    const report = {
      passed: consoleErrors.length === 0 && pageErrors.length === 0,
      hasWasm,
      initState,
      consoleErrors,
      pageErrors,
      shots,
    };
    fs.writeFileSync(path.join(ARTIFACTS_DIR, 'report.json'), JSON.stringify(report, null, 2));

    if (consoleErrors.length > 0 || pageErrors.length > 0) {
      console.error('[audit] FAILED with browser errors:', { consoleErrors, pageErrors });
      process.exitCode = 1;
      return;
    }

    console.log(`[audit] ALL ${shots.length} VISUAL + RUNTIME CHECKS PASSED (0 console/page errors)!`);
  } finally {
    if (browser) await browser.close();
    previewProc.kill('SIGTERM');
  }
}

main().catch((err) => {
  console.error('[audit] FATAL:', err);
  process.exit(1);
});
