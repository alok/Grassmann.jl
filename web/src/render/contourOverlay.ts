// Crisp Floating 2D Picture-in-Picture Renderer for GSIR 0x0F CONTOUR_OVERLAY
// Renders #pga3d_slicing live projected contour AND multi-equation implicit contours + common intersections.
// Pure 2D painter: ZERO contour marching or intersection solving in JS!

import { GSIR_NO_LABEL, type GsirContourOverlay } from '../gsir/types';

function rgbaCss(rgba: readonly [number, number, number, number], alphaScale = 1): string {
  const r = Math.round(Math.max(0, Math.min(1, rgba[0])) * 255);
  const g = Math.round(Math.max(0, Math.min(1, rgba[1])) * 255);
  const b = Math.round(Math.max(0, Math.min(1, rgba[2])) * 255);
  const a = Math.max(0, Math.min(1, rgba[3] * alphaScale));
  return `rgba(${r}, ${g}, ${b}, ${a.toFixed(3)})`;
}

export class ContourOverlayRenderer {
  readonly element: HTMLDivElement;
  private readonly canvas: HTMLCanvasElement;
  private readonly ctx: CanvasRenderingContext2D;
  private readonly subtitleEl: HTMLSpanElement;
  private collapsed = false;
  private lastOverlay: GsirContourOverlay | null = null;
  private lastLabels: string[] = [];
  private darkTheme = true;

  constructor() {
    this.element = document.createElement('div');
    this.element.className = 'gs-contour-pip hidden';

    const header = document.createElement('div');
    header.className = 'gs-contour-header';

    const titleWrap = document.createElement('div');
    titleWrap.className = 'gs-contour-title-wrap';
    const title = document.createElement('span');
    title.className = 'gs-contour-title';
    title.textContent = '2D Contour Slice';
    this.subtitleEl = document.createElement('span');
    this.subtitleEl.className = 'gs-contour-sub';
    titleWrap.append(title, this.subtitleEl);

    const toggleBtn = document.createElement('button');
    toggleBtn.type = 'button';
    toggleBtn.className = 'gs-icon-btn gs-contour-toggle';
    toggleBtn.title = 'Collapse / Expand 2D Contour Inset';
    toggleBtn.textContent = '−';
    toggleBtn.addEventListener('click', () => {
      this.collapsed = !this.collapsed;
      this.canvas.style.display = this.collapsed ? 'none' : 'block';
      toggleBtn.textContent = this.collapsed ? '+' : '−';
    });

    header.append(titleWrap, toggleBtn);

    this.canvas = document.createElement('canvas');
    this.canvas.className = 'gs-contour-canvas';
    this.canvas.width = 480;
    this.canvas.height = 400;

    const ctx = this.canvas.getContext('2d');
    if (!ctx) {
      throw new Error('Failed to acquire 2D canvas context for contour overlay');
    }
    this.ctx = ctx;

    this.element.append(header, this.canvas);
  }

  update(overlay: GsirContourOverlay | null, labels: string[] = [], darkTheme = true): void {
    this.lastOverlay = overlay;
    this.lastLabels = labels;
    this.darkTheme = darkTheme;

    if (!overlay || (overlay.curves.length === 0 && overlay.intersections.length === 0)) {
      this.element.classList.add('hidden');
      return;
    }

    this.element.classList.remove('hidden');
    this.subtitleEl.textContent = `${overlay.curves.length} curve${overlay.curves.length === 1 ? '' : 's'}${
      overlay.intersections.length > 0 ? ` · ${overlay.intersections.length} pts` : ''
    }`;

    if (!this.collapsed) {
      this.draw();
    }
  }

  private draw(): void {
    const overlay = this.lastOverlay;
    if (!overlay) return;

    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const cssW = 240;
    const cssH = 200;
    const w = Math.round(cssW * dpr);
    const h = Math.round(cssH * dpr);
    if (this.canvas.width !== w || this.canvas.height !== h) {
      this.canvas.width = w;
      this.canvas.height = h;
    }

    const ctx = this.ctx;
    ctx.save();
    ctx.scale(dpr, dpr);

    // Backdrop
    ctx.fillStyle = this.darkTheme ? '#090e1a' : '#f8fafc';
    ctx.fillRect(0, 0, cssW, cssH);

    const pad = 22;
    const plotW = cssW - pad * 2;
    const plotH = cssH - pad * 2;
    const spanX = Math.max(1e-5, overlay.maxX - overlay.minX);
    const spanY = Math.max(1e-5, overlay.maxY - overlay.minY);

    const mapX = (x: number) => pad + ((x - overlay.minX) / spanX) * plotW;
    const mapY = (y: number) => pad + (1 - (y - overlay.minY) / spanY) * plotH;

    // Subtle grid
    ctx.strokeStyle = this.darkTheme ? 'rgba(94, 122, 178, 0.18)' : 'rgba(100, 116, 139, 0.2)';
    ctx.lineWidth = 1;
    for (let i = 0; i <= 4; i++) {
      const gx = pad + (plotW * i) / 4;
      const gy = pad + (plotH * i) / 4;
      ctx.beginPath();
      ctx.moveTo(gx, pad);
      ctx.lineTo(gx, pad + plotH);
      ctx.stroke();

      ctx.beginPath();
      ctx.moveTo(pad, gy);
      ctx.lineTo(pad + plotW, gy);
      ctx.stroke();
    }

    // Zero axes if inside domain
    ctx.strokeStyle = this.darkTheme ? 'rgba(148, 175, 224, 0.36)' : 'rgba(71, 85, 105, 0.35)';
    ctx.lineWidth = 1.1;
    if (overlay.minX <= 0 && overlay.maxX >= 0) {
      const zx = mapX(0);
      ctx.beginPath();
      ctx.moveTo(zx, pad);
      ctx.lineTo(zx, pad + plotH);
      ctx.stroke();
    }
    if (overlay.minY <= 0 && overlay.maxY >= 0) {
      const zy = mapY(0);
      ctx.beginPath();
      ctx.moveTo(pad, zy);
      ctx.lineTo(pad + plotW, zy);
      ctx.stroke();
    }

    // Plot area clip
    ctx.save();
    ctx.beginPath();
    ctx.rect(pad, pad, plotW, plotH);
    ctx.clip();

    // Draw contour polylines with soft glow
    ctx.lineJoin = 'round';
    ctx.lineCap = 'round';
    for (const curve of overlay.curves) {
      if (curve.ptCount < 2) continue;

      // Soft bloom pass
      ctx.strokeStyle = rgbaCss(curve.rgba, 0.28);
      ctx.lineWidth = Math.max(3.5, curve.width * 2.4);
      ctx.beginPath();
      ctx.moveTo(mapX(curve.xy[0]!), mapY(curve.xy[1]!));
      for (let i = 1; i < curve.ptCount; i++) {
        ctx.lineTo(mapX(curve.xy[i * 2]!), mapY(curve.xy[i * 2 + 1]!));
      }
      ctx.stroke();

      // Crisp core pass
      ctx.strokeStyle = rgbaCss(curve.rgba, 1.0);
      ctx.lineWidth = Math.max(1.25, curve.width);
      ctx.stroke();
    }

    // Draw common intersection markers
    for (const pt of overlay.intersections) {
      const px = mapX(pt.x);
      const py = mapY(pt.y);

      ctx.beginPath();
      ctx.arc(px, py, 5.5, 0, Math.PI * 2);
      ctx.fillStyle = rgbaCss(pt.rgba, 0.28);
      ctx.fill();

      ctx.beginPath();
      ctx.arc(px, py, 3.0, 0, Math.PI * 2);
      ctx.fillStyle = rgbaCss(pt.rgba, 1.0);
      ctx.fill();
      ctx.strokeStyle = this.darkTheme ? '#090e1a' : '#ffffff';
      ctx.lineWidth = 1.2;
      ctx.stroke();

      if (pt.labelIdx !== GSIR_NO_LABEL && this.lastLabels[pt.labelIdx]) {
        ctx.font = '600 10px ui-monospace, SFMono-Regular, Menlo, monospace';
        ctx.fillStyle = this.darkTheme ? '#e2e8f0' : '#0f172a';
        ctx.fillText(this.lastLabels[pt.labelIdx]!, px + 6, py - 5);
      }
    }
    ctx.restore();

    // Bounds labels
    ctx.font = '500 9px ui-monospace, SFMono-Regular, Menlo, monospace';
    ctx.fillStyle = this.darkTheme ? 'rgba(186, 204, 236, 0.65)' : 'rgba(51, 65, 85, 0.72)';
    ctx.fillText(overlay.minX.toFixed(1), pad, cssH - 6);
    ctx.fillText(overlay.maxX.toFixed(1), cssW - pad - 18, cssH - 6);
    ctx.fillText(overlay.maxY.toFixed(1), 3, pad + 7);
    ctx.fillText(overlay.minY.toFixed(1), 3, pad + plotH);

    ctx.restore();
  }

  dispose(): void {
    this.element.remove();
  }
}
