// Interactive 3D Axis Triad Orientation Gizmo (bottom-right viewport overlay)
// Pure camera orientation display + clickable view snapping (X / Y / Z / ISO).
// Zero GA math — projects standard Three.js camera basis vectors into a crisp 88×88 SVG widget.

import * as THREE from 'three';

export type AxisSnapPreset = '+x' | '-x' | '+y' | '-y' | '+z' | '-z' | 'iso';

interface AxisDef {
  id: AxisSnapPreset;
  label: string;
  vec: THREE.Vector3;
  color: string;
  positive: boolean;
}

const AXES: AxisDef[] = [
  { id: '+x', label: 'X', vec: new THREE.Vector3(1, 0, 0), color: '#f43f5e', positive: true },
  { id: '+y', label: 'Y', vec: new THREE.Vector3(0, 1, 0), color: '#34d399', positive: true },
  { id: '+z', label: 'Z', vec: new THREE.Vector3(0, 0, 1), color: '#38bdf8', positive: true },
  { id: '-x', label: '−X', vec: new THREE.Vector3(-1, 0, 0), color: '#f43f5e', positive: false },
  { id: '-y', label: '−Y', vec: new THREE.Vector3(0, -1, 0), color: '#34d399', positive: false },
  { id: '-z', label: '−Z', vec: new THREE.Vector3(0, 0, -1), color: '#38bdf8', positive: false },
];

export class AxisTriadGizmo {
  readonly element: HTMLDivElement;
  private readonly svg: SVGSVGElement;
  private readonly onSnap: (preset: AxisSnapPreset) => void;
  private readonly invQuat = new THREE.Quaternion();
  private readonly tmpVec = new THREE.Vector3();
  private lastQuatKey = '';

  constructor(onSnap: (preset: AxisSnapPreset) => void) {
    this.onSnap = onSnap;

    this.element = document.createElement('div');
    this.element.className = 'gs-axis-gizmo';

    this.svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    this.svg.setAttribute('viewBox', '0 0 92 92');
    this.svg.setAttribute('width', '88');
    this.svg.setAttribute('height', '88');
    this.svg.setAttribute('class', 'gs-axis-svg');

    // Quick preset pill strip under gizmo
    const strip = document.createElement('div');
    strip.className = 'gs-cam-presets';
    const presets: Array<{ id: AxisSnapPreset; label: string }> = [
      { id: 'iso', label: 'Iso' },
      { id: '+y', label: 'Top' },
      { id: '+z', label: 'Front' },
      { id: '+x', label: 'Side' },
    ];
    for (const p of presets) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-cam-chip';
      btn.textContent = p.label;
      btn.title = `Snap camera to ${p.label} view`;
      btn.addEventListener('click', () => this.onSnap(p.id));
      strip.appendChild(btn);
    }

    this.element.append(this.svg, strip);
  }

  update(camera: THREE.Camera, isOrtho: boolean): void {
    const q = camera.quaternion;
    const key = `${isOrtho ? 1 : 0}:${q.x.toFixed(3)},${q.y.toFixed(3)},${q.z.toFixed(3)},${q.w.toFixed(3)}`;
    if (key === this.lastQuatKey) return;
    this.lastQuatKey = key;

    this.invQuat.copy(q).invert();

    const cx = 46;
    const cy = 46;
    const armLen = 30;

    const projected = AXES.map((a) => {
      this.tmpVec.copy(a.vec).applyQuaternion(this.invQuat);
      return {
        axis: a,
        sx: cx + this.tmpVec.x * armLen,
        sy: cy - this.tmpVec.y * armLen,
        depth: this.tmpVec.z,
      };
    });

    // Painter's algorithm: back-to-front by view-space depth
    projected.sort((a, b) => a.depth - b.depth);

    this.svg.innerHTML = '';

    // Subtle circular ring backdrop (clicking center snaps to Iso)
    const bg = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
    bg.setAttribute('cx', String(cx));
    bg.setAttribute('cy', String(cy));
    bg.setAttribute('r', '42');
    bg.setAttribute('class', 'gs-axis-ring');
    bg.addEventListener('click', () => this.onSnap('iso'));
    this.svg.appendChild(bg);

    for (const item of projected) {
      const g = document.createElementNS('http://www.w3.org/2000/svg', 'g');
      g.setAttribute('class', 'gs-axis-arm');
      g.style.cursor = 'pointer';
      g.addEventListener('click', (ev) => {
        ev.stopPropagation();
        this.onSnap(item.axis.id);
      });

      const opacity = item.depth < -0.15 ? 0.45 : 0.96;

      if (item.axis.positive) {
        const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
        line.setAttribute('x1', String(cx));
        line.setAttribute('y1', String(cy));
        line.setAttribute('x2', item.sx.toFixed(1));
        line.setAttribute('y2', item.sy.toFixed(1));
        line.setAttribute('stroke', item.axis.color);
        line.setAttribute('stroke-width', '2.2');
        line.setAttribute('stroke-linecap', 'round');
        line.setAttribute('stroke-opacity', String(opacity));
        g.appendChild(line);
      }

      const cap = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
      cap.setAttribute('cx', item.sx.toFixed(1));
      cap.setAttribute('cy', item.sy.toFixed(1));
      cap.setAttribute('r', item.axis.positive ? '8.5' : '4.5');
      cap.setAttribute('fill', item.axis.positive ? item.axis.color : 'rgba(148,163,184,0.22)');
      cap.setAttribute('stroke', item.axis.color);
      cap.setAttribute('stroke-width', item.axis.positive ? '0' : '1.4');
      cap.setAttribute('fill-opacity', String(opacity));
      g.appendChild(cap);

      if (item.axis.positive) {
        const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        txt.setAttribute('x', item.sx.toFixed(1));
        txt.setAttribute('y', (item.sy + 3.4).toFixed(1));
        txt.setAttribute('text-anchor', 'middle');
        txt.setAttribute('font-size', '9.5');
        txt.setAttribute('font-weight', '700');
        txt.setAttribute('font-family', 'ui-monospace, SFMono-Regular, Menlo, monospace');
        txt.setAttribute('fill', '#070a13');
        txt.textContent = item.axis.label;
        g.appendChild(txt);
      }

      this.svg.appendChild(g);
    }
  }

  dispose(): void {
    this.element.remove();
  }
}
