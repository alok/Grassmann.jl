import * as React from 'react';

const h = React.createElement;
const WIDTH = 900;
const HEIGHT = 520;
const EPSILON = 1e-8;
const DEFAULT_CAMERA = { yaw: -0.72, pitch: 0.72, zoom: 1.0 };

function clamp(value, low, high) {
  return Math.max(low, Math.min(high, value));
}

function vectorMetrics(vector) {
  const maximum = Math.max(Math.abs(vector.x), Math.abs(vector.y), Math.abs(vector.z));
  if (maximum < EPSILON) {
    return { magnitude: 0, direction: { x: 0, y: 0, z: 0 } };
  }
  const scaled = {
    x: vector.x / maximum,
    y: vector.y / maximum,
    z: vector.z / maximum,
  };
  const scaledLength = Math.sqrt(
    scaled.x * scaled.x + scaled.y * scaled.y + scaled.z * scaled.z,
  );
  const rawMagnitude = maximum * scaledLength;
  return {
    magnitude: Number.isFinite(rawMagnitude) ? rawMagnitude : Number.MAX_VALUE,
    direction: {
      x: scaled.x / scaledLength,
      y: scaled.y / scaledLength,
      z: scaled.z / scaledLength,
    },
  };
}

function magnitude(vector) {
  return vectorMetrics(vector).magnitude;
}

function normalize(vector) {
  return vectorMetrics(vector).direction;
}

function add(a, b) {
  return { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z };
}

function scale(value, vector) {
  return { x: value * vector.x, y: value * vector.y, z: value * vector.z };
}

function cross(a, b) {
  return {
    x: a.y * b.z - a.z * b.y,
    y: a.z * b.x - a.x * b.z,
    z: a.x * b.y - a.y * b.x,
  };
}

function signColor(value) {
  return value < 0 ? '#38bdf8' : '#f59e0b';
}

function fitPlanarLattice(frame) {
  const xs = frame.samples.map(sample => sample.position.x);
  const ys = frame.samples.map(sample => sample.position.y);
  const xMinimum = Math.min(...xs);
  const xMaximum = Math.max(...xs);
  const yMinimum = Math.min(...ys);
  const yMaximum = Math.max(...ys);
  const rawScale = Math.max(
    Math.abs(xMinimum), Math.abs(xMaximum), Math.abs(yMinimum), Math.abs(yMaximum),
  );
  if (rawScale === 0 || !Number.isFinite(rawScale)) {
    return () => ({ x: 0, y: 0, z: 0 });
  }
  const scaledXMinimum = xMinimum / rawScale;
  const scaledXMaximum = xMaximum / rawScale;
  const scaledYMinimum = yMinimum / rawScale;
  const scaledYMaximum = yMaximum / rawScale;
  const centerX = scaledXMinimum + (scaledXMaximum - scaledXMinimum) * 0.5;
  const centerY = scaledYMinimum + (scaledYMaximum - scaledYMinimum) * 0.5;
  const halfSpan = Math.max(
    (scaledXMaximum - scaledXMinimum) * 0.5,
    (scaledYMaximum - scaledYMinimum) * 0.5,
  );
  const divisor = halfSpan > 0 && Number.isFinite(halfSpan) ? halfSpan : 1;
  return position => ({
    x: (position.x / rawScale - centerX) / divisor,
    y: (position.y / rawScale - centerY) / divisor,
    z: 0,
  });
}

function project(point, camera) {
  const cosineYaw = Math.cos(camera.yaw);
  const sineYaw = Math.sin(camera.yaw);
  const cosinePitch = Math.cos(camera.pitch);
  const sinePitch = Math.sin(camera.pitch);
  const rotatedX = cosineYaw * point.x - sineYaw * point.y;
  const rotatedY = sineYaw * point.x + cosineYaw * point.y;
  const depth = cosinePitch * rotatedY + sinePitch * point.z;
  const vertical = sinePitch * rotatedY - cosinePitch * point.z;
  const perspective = 1 / clamp(1 + 0.12 * depth, 0.72, 1.32);
  const pixels = 154 * camera.zoom * perspective;
  return {
    x: WIDTH * 0.5 + rotatedX * pixels,
    y: HEIGHT * 0.54 + vertical * pixels,
    depth,
    perspective,
  };
}

function arrowParts(key, start, end, color, width, data = {}) {
  const dx = end.x - start.x;
  const dy = end.y - start.y;
  const length = Math.sqrt(dx * dx + dy * dy);
  if (length < 0.5) return [];
  const ux = dx / length;
  const uy = dy / length;
  const px = -uy;
  const py = ux;
  const headLength = clamp(length * 0.28, 7, 13);
  const headWidth = headLength * 0.48;
  const leftX = end.x - ux * headLength + px * headWidth;
  const leftY = end.y - uy * headLength + py * headWidth;
  const rightX = end.x - ux * headLength - px * headWidth;
  const rightY = end.y - uy * headLength - py * headWidth;
  return [
    h('line', {
      key: key + '-shaft',
      ...data,
      'data-glyph-part': 'shaft',
      x1: start.x,
      y1: start.y,
      x2: end.x - ux * (headLength * 0.55),
      y2: end.y - uy * (headLength * 0.55),
      stroke: color,
      strokeWidth: width,
      strokeLinecap: 'round',
    }),
    h('polygon', {
      key: key + '-head',
      ...data,
      'data-glyph-part': 'head',
      points: `${end.x},${end.y} ${leftX},${leftY} ${rightX},${rightY}`,
      fill: color,
    }),
  ];
}

function coefficientText(sample, index) {
  const position = sample.position;
  const value = sample.value;
  const show = number => String(number);
  return [
    `sample ${index} at (${show(position.x)}, ${show(position.y)}, ${show(position.z)})`,
    `grade 0: ${show(value.scalar)}`,
    `grade 1: (${show(value.vector.x)}, ${show(value.vector.y)}, ${show(value.vector.z)})`,
    `grade 2 normal (e23,e31,e12): (${show(value.bivectorNormal.x)}, ${show(value.bivectorNormal.y)}, ${show(value.bivectorNormal.z)})`,
    `grade 3: ${show(value.pseudoscalar)}`,
  ].join('\n');
}

function frameScales(frame) {
  const maxima = frame.samples.reduce((result, sample) => ({
    scalar: Math.max(result.scalar, Math.abs(sample.value.scalar)),
    vector: Math.max(result.vector, magnitude(sample.value.vector)),
    bivector: Math.max(result.bivector, magnitude(sample.value.bivectorNormal)),
    pseudoscalar: Math.max(result.pseudoscalar, Math.abs(sample.value.pseudoscalar)),
  }), { scalar: EPSILON, vector: EPSILON, bivector: EPSILON, pseudoscalar: EPSILON });
  return maxima;
}

function gridElements(frame, camera, toDisplay) {
  const xs = [...new Set(frame.samples.map(sample => sample.position.x))].sort((a, b) => a - b);
  const ys = [...new Set(frame.samples.map(sample => sample.position.y))].sort((a, b) => a - b);
  const z = frame.samples[0].position.z;
  const xMin = xs[0];
  const xMax = xs[xs.length - 1];
  const yMin = ys[0];
  const yMax = ys[ys.length - 1];
  const elements = [];
  xs.forEach((x, index) => {
    const start = project(toDisplay({ x, y: yMin, z }), camera);
    const end = project(toDisplay({ x, y: yMax, z }), camera);
    elements.push(h('line', {
      key: `grid-x-${index}`,
      x1: start.x,
      y1: start.y,
      x2: end.x,
      y2: end.y,
      stroke: Math.abs(x) < EPSILON ? '#64748b' : '#334155',
      strokeWidth: Math.abs(x) < EPSILON ? 1.5 : 1,
    }));
  });
  ys.forEach((y, index) => {
    const start = project(toDisplay({ x: xMin, y, z }), camera);
    const end = project(toDisplay({ x: xMax, y, z }), camera);
    elements.push(h('line', {
      key: `grid-y-${index}`,
      x1: start.x,
      y1: start.y,
      x2: end.x,
      y2: end.y,
      stroke: Math.abs(y) < EPSILON ? '#64748b' : '#334155',
      strokeWidth: Math.abs(y) < EPSILON ? 1.5 : 1,
    }));
  });
  return elements;
}

function sampleGlyph(entry, camera, scales, visible, selectedIndex, selectSample) {
  const sample = entry.sample;
  const value = sample.value;
  const center = entry.projected;
  const children = [];

  if (visible[3] && Math.abs(value.pseudoscalar) > EPSILON) {
    const ratio = clamp(Math.abs(value.pseudoscalar) / scales.pseudoscalar, 0, 1);
    children.push(h('circle', {
      key: 'pseudoscalar',
      'data-grade': 3,
      'data-glyph': 'pseudoscalar-halo',
      'data-sample-index': entry.index,
      cx: center.x,
      cy: center.y,
      r: (10 + 17 * ratio) * camera.zoom * center.perspective,
      fill: 'none',
      stroke: signColor(value.pseudoscalar),
      strokeWidth: 2 + 2.4 * ratio,
      strokeOpacity: 0.62,
      strokeDasharray: '5 4',
    }));
  }

  const bivectorMetrics = vectorMetrics(value.bivectorNormal);
  const bivectorMagnitude = bivectorMetrics.magnitude;
  if (visible[2] && bivectorMagnitude > EPSILON) {
    const ratio = clamp(bivectorMagnitude / scales.bivector, 0, 1);
    const normal = bivectorMetrics.direction;
    const reference = Math.abs(normal.z) < 0.82
      ? { x: 0, y: 0, z: 1 }
      : { x: 1, y: 0, z: 0 };
    const tangentU = normalize(cross(normal, reference));
    const tangentV = normalize(cross(normal, tangentU));
    const radius = 0.095 + 0.19 * ratio;
    const diskPoints = [];
    for (let step = 0; step < 20; step += 1) {
      const angle = 2 * Math.PI * step / 20;
      const offset = add(
        scale(radius * Math.cos(angle), tangentU),
        scale(radius * Math.sin(angle), tangentV),
      );
      const diskPoint = project(add(entry.displayPosition, offset), camera);
      diskPoints.push(`${diskPoint.x},${diskPoint.y}`);
    }
    const color = '#f59e0b';
    children.push(h('polygon', {
      key: 'bivector-disk',
      'data-grade': 2,
      'data-glyph': 'bivector-disk',
      'data-sample-index': entry.index,
      points: diskPoints.join(' '),
      fill: color,
      fillOpacity: 0.20,
      stroke: color,
      strokeOpacity: 0.82,
      strokeWidth: 1.7,
    }));
    const normalTip = project(
      add(entry.displayPosition, scale(0.16 + 0.12 * ratio, normal)),
      camera,
    );
    children.push(...arrowParts('bivector-normal', center, normalTip, color, 1.6, {
      'data-grade': 2,
      'data-glyph': 'bivector-normal',
      'data-sample-index': entry.index,
    }));
  }

  const vectorMetrics = vectorMetrics(value.vector);
  const vectorMagnitude = vectorMetrics.magnitude;
  if (visible[1] && vectorMagnitude > EPSILON) {
    const ratio = clamp(vectorMagnitude / scales.vector, 0, 1);
    const direction = vectorMetrics.direction;
    const tip = project(
      add(entry.displayPosition, scale(0.15 + 0.32 * ratio, direction)),
      camera,
    );
    children.push(...arrowParts('vector', center, tip, '#a78bfa', 2.6, {
      'data-grade': 1,
      'data-glyph': 'vector-arrow',
      'data-sample-index': entry.index,
    }));
  }

  if (visible[0] && Math.abs(value.scalar) > EPSILON) {
    const ratio = clamp(Math.abs(value.scalar) / scales.scalar, 0, 1);
    children.push(h('circle', {
      key: 'scalar',
      'data-grade': 0,
      'data-glyph': 'scalar-dot',
      'data-sample-index': entry.index,
      cx: center.x,
      cy: center.y,
      r: (3.5 + 7.5 * ratio) * Math.sqrt(center.perspective),
      fill: signColor(value.scalar),
      stroke: '#f8fafc',
      strokeWidth: 1.1,
      fillOpacity: 0.92,
    }));
  }

  if (entry.index === selectedIndex) {
    children.push(h('circle', {
      key: 'selected',
      'data-glyph': 'selection',
      'data-sample-index': entry.index,
      cx: center.x,
      cy: center.y,
      r: 15,
      fill: 'none',
      stroke: '#f8fafc',
      strokeWidth: 2,
      strokeOpacity: 0.88,
    }));
  }

  children.push(h('title', { key: 'title' }, coefficientText(sample, entry.index)));
  return h('g', {
    key: `sample-${entry.index}`,
    'data-region': 'sample',
    'data-sample-index': entry.index,
    onPointerDown: event => event.stopPropagation(),
    onClick: event => {
      event.stopPropagation();
      selectSample(entry.index);
    },
    style: { cursor: 'pointer' },
  }, children);
}

function gradeButton(grade, label, color, visible, setVisible) {
  const active = visible[grade];
  return h('button', {
    key: grade,
    type: 'button',
    'data-region': 'grade-toggle',
    'data-grade': grade,
    onClick: () => setVisible(current => ({ ...current, [grade]: !current[grade] })),
    'aria-pressed': active,
    style: {
      border: `1px solid ${active ? color : '#475569'}`,
      borderRadius: 7,
      background: active ? `${color}24` : '#172033',
      color: active ? '#f8fafc' : '#94a3b8',
      padding: '6px 10px',
      fontSize: 14,
      cursor: 'pointer',
    },
  }, label);
}

function inspector(sample, index) {
  if (!sample) return null;
  const value = sample.value;
  const row = (label, text, color) => h('div', {
    key: label,
    style: { display: 'flex', gap: 8, marginTop: 5, alignItems: 'baseline' },
  }, [
    h('span', { key: 'label', style: { width: 74, color, fontWeight: 650 } }, label),
    h('code', { key: 'value', style: { color: '#e2e8f0', fontSize: 13 } }, text),
  ]);
  const show = number => String(number);
  return h('div', {
    'data-region': 'inspector-card',
    style: {
      minWidth: 276,
      border: '1px solid #334155',
      borderRadius: 10,
      background: '#111827',
      padding: '11px 13px',
      fontSize: 13,
    },
  }, [
    h('div', { key: 'heading', style: { fontSize: 14, color: '#f8fafc', fontWeight: 700 } },
      `Lean sample ${index}`),
    h('div', { key: 'position', style: { color: '#94a3b8', marginTop: 4 } },
      `p = (${show(sample.position.x)}, ${show(sample.position.y)}, ${show(sample.position.z)})`),
    row('grade 0', show(value.scalar), signColor(value.scalar)),
    row('grade 1', `(${show(value.vector.x)}, ${show(value.vector.y)}, ${show(value.vector.z)})`, '#a78bfa'),
    row('grade 2', `(${show(value.bivectorNormal.x)}, ${show(value.bivectorNormal.y)}, ${show(value.bivectorNormal.z)})`, '#f59e0b'),
    row('grade 3', show(value.pseudoscalar), signColor(value.pseudoscalar)),
    h('div', { key: 'basis', style: { color: '#64748b', marginTop: 7 } },
      'grade 2 tuple = (e23, e31, e12)'),
  ]);
}

export default function MultivectorField(props) {
  const frameCount = props.frames.length;
  const [frameIndex, setFrameIndex] = React.useState(props.initialFrame);
  const [playing, setPlaying] = React.useState(false);
  const [visible, setVisible] = React.useState({ 0: true, 1: true, 2: true, 3: true });
  const [camera, setCamera] = React.useState(DEFAULT_CAMERA);
  const [dragging, setDragging] = React.useState(false);
  const [selectedIndex, setSelectedIndex] = React.useState(props.initialSample);
  const drag = React.useRef(null);

  // Validated props always contain frames and samples. Clamp synchronously so
  // an InfoView hot update cannot index old UI state before effects run.
  const safeFrameIndex = clamp(frameIndex, 0, frameCount - 1);
  const frame = props.frames[safeFrameIndex];
  const safeSelectedIndex = clamp(selectedIndex, 0, frame.samples.length - 1);

  React.useEffect(() => {
    setPlaying(false);
    setFrameIndex(props.initialFrame);
    setSelectedIndex(props.initialSample);
  }, [props.frames, props.initialFrame, props.initialSample]);

  React.useEffect(() => {
    if (!playing || frameCount < 2) return undefined;
    const timer = setInterval(() => {
      setFrameIndex(index => (index + 1) % frameCount);
    }, 520);
    return () => clearInterval(timer);
  }, [playing, frameCount]);

  const scales = frameScales(frame);
  const toDisplay = fitPlanarLattice(frame);
  const entries = frame.samples.map((sample, index) => {
    const displayPosition = toDisplay(sample.position);
    return {
      sample,
      index,
      displayPosition,
      projected: project(displayPosition, camera),
    };
  }).sort((a, b) => b.projected.depth - a.projected.depth);

  const pointerDown = event => {
    event.preventDefault();
    event.currentTarget.setPointerCapture(event.pointerId);
    drag.current = { x: event.clientX, y: event.clientY, camera };
    setDragging(true);
  };
  const pointerMove = event => {
    if (!drag.current) return;
    const dx = event.clientX - drag.current.x;
    const dy = event.clientY - drag.current.y;
    setCamera({
      ...drag.current.camera,
      yaw: drag.current.camera.yaw + dx * 0.008,
      pitch: clamp(drag.current.camera.pitch + dy * 0.006, 0.16, 1.38),
    });
  };
  const pointerUp = event => {
    if (event.currentTarget.hasPointerCapture(event.pointerId)) {
      event.currentTarget.releasePointerCapture(event.pointerId);
    }
    drag.current = null;
    setDragging(false);
  };
  const lostPointerCapture = () => {
    drag.current = null;
    setDragging(false);
  };
  const wheel = event => {
    event.preventDefault();
    setCamera(current => ({
      ...current,
      zoom: clamp(current.zoom * Math.exp(-event.deltaY * 0.0012), 0.55, 2.25),
    }));
  };

  const buttonStyle = {
    border: '1px solid #475569',
    borderRadius: 7,
    background: '#172033',
    color: '#e2e8f0',
    padding: '6px 11px',
    fontSize: 14,
    cursor: 'pointer',
  };
  const badgeStyle = {
    border: '1px solid #334155',
    borderRadius: 999,
    padding: '4px 9px',
    color: '#cbd5e1',
    background: '#111827',
    fontSize: 14,
  };

  return h('div', {
    'data-region': 'multivector-field',
    style: {
      boxSizing: 'border-box',
      width: '100%',
      maxWidth: 1120,
      margin: '0 auto',
      padding: 16,
      border: '1px solid #334155',
      borderRadius: 14,
      background: 'linear-gradient(155deg, #0f172a 0%, #111827 58%, #101827 100%)',
      color: '#f8fafc',
      fontFamily: 'var(--vscode-font-family, system-ui, sans-serif)',
    },
  }, [
    h('div', {
      key: 'header',
      'data-region': 'header',
      style: { display: 'flex', justifyContent: 'space-between', gap: 18, flexWrap: 'wrap' },
    }, [
      h('div', { key: 'titles', style: { minWidth: 320, flex: '1 1 520px' } }, [
        h('div', { key: 'title', style: { fontSize: 22, lineHeight: 1.25, fontWeight: 760 } }, props.title),
        h('div', { key: 'subtitle', style: { color: '#94a3b8', fontSize: 15, marginTop: 5 } }, props.subtitle),
        h('code', {
          key: 'formula',
          style: { display: 'block', color: '#c4b5fd', fontSize: 14, marginTop: 8, whiteSpace: 'normal' },
        }, props.formula),
      ]),
      h('div', { key: 'badges', style: { display: 'flex', alignItems: 'flex-start', gap: 7, flexWrap: 'wrap' } }, [
        h('span', { key: 'lean', style: badgeStyle }, 'Lean Float runtime'),
        h('span', { key: 'frames', style: badgeStyle },
          `${frameCount} Lean frame${frameCount === 1 ? '' : 's'}`),
        h('span', { key: 'samples', style: badgeStyle }, `${frame.samples.length} samples`),
        h('span', { key: 'parameter', style: badgeStyle },
          `${props.parameterLabel} = ${frame.parameter.toFixed(3)}`),
      ]),
    ]),
    h('div', {
      key: 'controls',
      'data-region': 'grade-controls',
      style: { display: 'flex', gap: 7, alignItems: 'center', flexWrap: 'wrap', margin: '13px 0 9px' },
    }, [
      gradeButton(0, 'grade 0 · scalar', '#f59e0b', visible, setVisible),
      gradeButton(1, 'grade 1 · vector', '#a78bfa', visible, setVisible),
      gradeButton(2, 'grade 2 · plane', '#f59e0b', visible, setVisible),
      gradeButton(3, 'grade 3 · volume', '#38bdf8', visible, setVisible),
      h('button', {
        key: 'reset',
        type: 'button',
        onClick: () => setCamera(DEFAULT_CAMERA),
        style: buttonStyle,
      }, 'Reset view'),
    ]),
    h('div', {
      key: 'content',
      'data-region': 'field-and-inspector',
      style: { display: 'flex', gap: 13, alignItems: 'stretch', flexWrap: 'wrap' },
    }, [
      h('svg', {
        key: 'svg',
        'data-region': 'field-svg',
        viewBox: `0 0 ${WIDTH} ${HEIGHT}`,
        role: 'img',
        'aria-label': 'Interactive three-dimensional multivector field',
        onPointerDown: pointerDown,
        onPointerMove: pointerMove,
        onPointerUp: pointerUp,
        onPointerCancel: pointerUp,
        onLostPointerCapture: lostPointerCapture,
        onWheel: wheel,
        style: {
          flex: '1 1 650px',
          minWidth: 0,
          minHeight: 430,
          border: '1px solid #334155',
          borderRadius: 11,
          background: '#0b1120',
          cursor: dragging ? 'grabbing' : 'grab',
          touchAction: 'none',
          userSelect: 'none',
        },
      }, [
        h('rect', { key: 'background', x: 0, y: 0, width: WIDTH, height: HEIGHT, fill: '#0b1120' }),
        h('g', { key: 'grid', 'data-region': 'guide-grid', pointerEvents: 'none' },
          gridElements(frame, camera, toDisplay)),
        h('g', { key: 'glyphs', 'data-region': 'glyphs' }, entries.map(entry =>
          sampleGlyph(entry, camera, scales, visible, safeSelectedIndex, setSelectedIndex))),
        h('text', {
          key: 'hint',
          x: 18,
          y: HEIGHT - 18,
          fill: '#64748b',
          fontSize: 14,
          pointerEvents: 'none',
        }, 'drag to orbit · wheel to zoom · click a sample to inspect'),
      ]),
      h('div', {
        key: 'inspector',
        'data-region': 'inspector',
        style: { flex: '0 1 300px', alignSelf: 'flex-start' },
      },
        inspector(frame.samples[safeSelectedIndex], safeSelectedIndex)),
    ]),
    frameCount > 1 ? h('div', {
      key: 'timeline',
      'data-region': 'timeline',
      style: { display: 'flex', gap: 10, alignItems: 'center', marginTop: 11 },
    }, [
      h('button', {
        key: 'play',
        type: 'button',
        onClick: () => setPlaying(value => !value),
        style: { ...buttonStyle, minWidth: 76 },
      }, playing ? 'Pause' : 'Play'),
      h('input', {
        key: 'slider',
        type: 'range',
        min: 0,
        max: frameCount - 1,
        step: 1,
        value: safeFrameIndex,
        onChange: event => {
          setPlaying(false);
          setFrameIndex(Number(event.target.value));
        },
        'aria-label': `Lean-computed ${props.parameterLabel} frame`,
        style: { flex: 1, minWidth: 180 },
      }),
      h('span', { key: 'frame', style: { color: '#cbd5e1', fontSize: 14, minWidth: 92, textAlign: 'right' } },
        `frame ${safeFrameIndex + 1} / ${frameCount}`),
    ]) : h('div', {
      key: 'timeline-static',
      'data-region': 'timeline-static',
      style: { color: '#94a3b8', fontSize: 14, marginTop: 11 },
    }, 'frame 1 / 1 · static scene'),
    h('div', {
      key: 'ownership',
      'data-region': 'ownership',
      style: { color: '#94a3b8', fontSize: 14, lineHeight: 1.45, marginTop: 10 },
    }, 'Lean computed and validated every position and grade coefficient. This local SVG view infers rectangular guides from the validated lattice, normalizes display scales, constructs glyph geometry, projects, depth-sorts, and paints those serialized values.'),
  ]);
}
