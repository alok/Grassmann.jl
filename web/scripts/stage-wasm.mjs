#!/usr/bin/env node
// Stages compiled Lean 4.36 WASM artifacts into public/wasm/ with content-fingerprinted
// filenames and a cache-busted wasm-manifest.json so Vercel immutable caching never serves stale WASM.

import { createHash } from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const webDir = path.resolve(__dirname, '..');
const outDir = path.join(webDir, 'public', 'wasm');

const argIdx = process.argv.indexOf('--src');
const srcDir =
  (argIdx >= 0 && process.argv[argIdx + 1]) ||
  process.env.GRASSMANN_WASM_DIR ||
  path.resolve(webDir, '..', 'wasm', 'dist');

const srcMjs = path.join(srcDir, 'grassmann.mjs');
const srcWasm = path.join(srcDir, 'grassmann.wasm');
const srcManifest = path.join(srcDir, 'wasm-manifest.json');

if (!fs.existsSync(srcMjs) || !fs.existsSync(srcWasm)) {
  console.error(`[stage-wasm] Missing compiled Lean WASM in ${srcDir} (expected grassmann.mjs & grassmann.wasm)`);
  process.exit(1);
}

fs.mkdirSync(outDir, { recursive: true });

// Remove stale fingerprinted or un-fingerprinted artifacts before writing fresh ones
for (const entry of fs.readdirSync(outDir)) {
  if (/^grassmann(\.[a-f0-9]{8,})?\.(wasm|mjs)$/.test(entry)) {
    fs.unlinkSync(path.join(outDir, entry));
  }
}

const wasmBytes = fs.readFileSync(srcWasm);
const mjsBytes = fs.readFileSync(srcMjs);

let hash;
let hashedWasmName;
let hashedMjsName;
let manifest;

if (fs.existsSync(srcManifest)) {
  const upstream = JSON.parse(fs.readFileSync(srcManifest, 'utf8'));
  hash = String(upstream.hash || '').trim();
  hashedWasmName = upstream.wasmFile || `grassmann.${hash}.wasm`;
  hashedMjsName = upstream.loaderFile || `grassmann.${hash}.mjs`;
  manifest = {
    ...upstream,
    loaderFile: hashedMjsName,
    wasmFile: hashedWasmName,
    mjs: `./${hashedMjsName}`,
    wasm: `./${hashedWasmName}`,
  };
} else {
  hash = createHash('sha256').update(wasmBytes).update(mjsBytes).digest('hex').slice(0, 10);
  hashedWasmName = `grassmann.${hash}.wasm`;
  hashedMjsName = `grassmann.${hash}.mjs`;
  manifest = {
    version: 1,
    hash,
    loaderFile: hashedMjsName,
    wasmFile: hashedWasmName,
    mjs: `./${hashedMjsName}`,
    wasm: `./${hashedWasmName}`,
    bytes: wasmBytes.byteLength,
  };
}

// Rewrite internal default "grassmann.wasm" references inside the fingerprinted ES loader
// so standalone imports without custom `locateFile` resolve the exact fingerprinted binary (Dots P0 #6).
const mjsText = mjsBytes.toString('utf8');
const patchedMjsText = mjsText.replaceAll('"grassmann.wasm"', `"${hashedWasmName}"`);

fs.writeFileSync(path.join(outDir, hashedWasmName), wasmBytes);
fs.writeFileSync(path.join(outDir, hashedMjsName), patchedMjsText, 'utf8');
fs.writeFileSync(path.join(outDir, 'wasm-manifest.json'), JSON.stringify(manifest, null, 2) + '\n');

console.log(
  `[stage-wasm] Staged Lean WASM hash=${hash} (${(wasmBytes.byteLength / 1024).toFixed(1)} KB wasm, ` +
    `${(mjsBytes.byteLength / 1024).toFixed(1)} KB mjs, presets=${manifest.presetCount ?? 'dynamic'}) -> ${outDir}`
);
