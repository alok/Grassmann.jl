import { readFileSync } from 'node:fs';
import vm from 'node:vm';

const rendererUrl = new URL('../GrassmannViz/multivectorField.js', import.meta.url);
let source = readFileSync(rendererUrl, 'utf8');
source = source
  .replace("import * as React from 'react';", '')
  .replace('export default function MultivectorField', 'function MultivectorField');
source += `
globalThis.__multivectorRendererTestApi = {
  fitPlanarLattice,
  frameScales,
  gridElements,
  project,
  sampleGlyph,
  vectorMetrics,
};`;

const context = vm.createContext({
  React: {
    createElement: (type, props, ...children) => ({ type, props: props ?? {}, children }),
  },
  clearInterval,
  console,
  setInterval,
});
new vm.Script(source, { filename: rendererUrl.pathname }).runInContext(context);

const {
  fitPlanarLattice,
  frameScales,
  gridElements,
  project,
  sampleGlyph,
  vectorMetrics,
} = context.__multivectorRendererTestApi;

function assertFiniteTree(node) {
  if (node == null || typeof node === 'boolean') return;
  if (Array.isArray(node)) {
    node.forEach(assertFiniteTree);
    return;
  }
  if (typeof node !== 'object') return;
  for (const value of Object.values(node.props ?? {})) {
    if (typeof value === 'number' && !Number.isFinite(value)) {
      throw new Error(`renderer emitted non-finite numeric SVG data: ${value}`);
    }
    if (typeof value === 'string' && /NaN|Infinity/.test(value)) {
      throw new Error(`renderer emitted non-finite SVG text: ${value}`);
    }
  }
  assertFiniteTree(node.children);
}

const extremeValue = {
  scalar: 1e308,
  vector: { x: 1e308, y: -1e308, z: 1e308 },
  bivectorNormal: { x: -1e308, y: 1e308, z: 1e308 },
  pseudoscalar: -1e308,
};
const extremeFrame = {
  parameter: 0,
  samples: [
    { position: { x: -1e308, y: 1e307, z: 0 }, value: extremeValue },
    { position: { x: 1e308, y: 1e307, z: 0 }, value: extremeValue },
    { position: { x: -1e308, y: 1e308, z: 0 }, value: extremeValue },
    { position: { x: 1e308, y: 1e308, z: 0 }, value: extremeValue },
  ],
};
const camera = { yaw: -0.72, pitch: 0.72, zoom: 1 };
const toDisplay = fitPlanarLattice(extremeFrame);
const displayPosition = toDisplay(extremeFrame.samples[0].position);
const projected = project(displayPosition, camera);
const info = vectorMetrics(extremeValue.vector);
for (const value of [
  displayPosition.x,
  displayPosition.y,
  projected.x,
  projected.y,
  projected.depth,
  info.magnitude,
  info.direction.x,
  info.direction.y,
  info.direction.z,
]) {
  if (!Number.isFinite(value)) throw new Error(`renderer math produced ${value}`);
}

const scales = frameScales(extremeFrame);
const glyph = sampleGlyph({
  sample: extremeFrame.samples[0],
  index: 0,
  displayPosition,
  projected,
}, camera, scales, { 0: true, 1: true, 2: true, 3: true }, 0, () => {});
assertFiniteTree(glyph);
assertFiniteTree(gridElements(extremeFrame, camera, toDisplay));

const zeroFit = fitPlanarLattice({
  parameter: 0,
  samples: [{ position: { x: 0, y: 0, z: 0 }, value: extremeValue }],
});
const zeroDisplay = zeroFit({ x: 0, y: 0, z: 0 });
if (zeroDisplay.x !== 0 || zeroDisplay.y !== 0 || zeroDisplay.z !== 0) {
  throw new Error('degenerate display fitting did not use its finite zero fallback');
}

console.log('multivector renderer runtime math passed');
