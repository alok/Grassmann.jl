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

function treeHasGrade(node, grade) {
  if (node == null || typeof node === 'boolean') return false;
  if (Array.isArray(node)) return node.some(child => treeHasGrade(child, grade));
  if (typeof node !== 'object') return false;
  return node.props?.['data-grade'] === grade || treeHasGrade(node.children, grade);
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

const nearEpsilon = vectorMetrics({ x: 9e-9, y: 9e-9, z: 9e-9 });
if (!(nearEpsilon.magnitude > 1e-8) ||
    ![nearEpsilon.direction.x, nearEpsilon.direction.y, nearEpsilon.direction.z]
      .every(Number.isFinite)) {
  throw new Error('Euclidean vector epsilon diverged from the Lean fallback renderer');
}
const belowEpsilon = vectorMetrics({ x: 5e-9, y: 0, z: 0 });
if (belowEpsilon.magnitude !== 0) {
  throw new Error('sub-epsilon vector was not omitted');
}

const thresholdValue = {
  scalar: 1e-8,
  vector: { x: 1e-8, y: 0, z: 0 },
  bivectorNormal: { x: 0, y: 1e-8, z: 0 },
  pseudoscalar: 1e-8,
};
const thresholdFrame = {
  parameter: 0,
  samples: [{ position: { x: 0, y: 0, z: 0 }, value: thresholdValue }],
};
const thresholdGlyph = sampleGlyph({
  sample: thresholdFrame.samples[0],
  index: 0,
  displayPosition: { x: 0, y: 0, z: 0 },
  projected: project({ x: 0, y: 0, z: 0 }, camera),
}, camera, frameScales(thresholdFrame),
{ 0: true, 1: true, 2: true, 3: true }, 0, () => {});
for (const grade of [0, 1, 2, 3]) {
  if (!treeHasGrade(thresholdGlyph, grade)) {
    throw new Error(`grade ${grade} at the documented epsilon was omitted`);
  }
}

const zeroFit = fitPlanarLattice({
  parameter: 0,
  samples: [{ position: { x: 0, y: 0, z: 0 }, value: extremeValue }],
});
const zeroDisplay = zeroFit({ x: 0, y: 0, z: 0 });
if (zeroDisplay.x !== 0 || zeroDisplay.y !== 0 || zeroDisplay.z !== 0) {
  throw new Error('degenerate display fitting did not use its finite zero fallback');
}

console.log('multivector renderer runtime math passed');
