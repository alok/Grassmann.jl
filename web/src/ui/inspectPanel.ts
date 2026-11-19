// CoffeeShop "Inspect Stash" Panel:
// - Live multivector blade table populated from metaJson.inspect + binary 0x11 INSPECT_COEFFS
// - Clickable color-coded metric matrix (-1 crimson, 0 emerald, +1 sapphire)
// - Live coefficient editor sending binary EditCoeff(entryIdx, bladeIdx, val) to Lean at 60fps
// - One-click Copy JSON

import type { GsirFrame } from '../gsir/types';

// Pure static display-label dictionary used ONLY when a compact GSIR frame omits
// meta.algebra.basisNames / basisMetric (zero GA arithmetic!).
const DISPLAY_BASIS_PRESETS: Record<string, { names: string[]; metric: number[] }> = {
  PGA3: {
    names: ['1', 'e0', 'e1', 'e2', 'e3', 'e01', 'e02', 'e03', 'e12', 'e13', 'e23', 'e012', 'e013', 'e023', 'e123', 'e0123'],
    metric: [1, 0, 1, 1, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0],
  },
  PGA2: {
    names: ['1', 'e0', 'e1', 'e2', 'e01', 'e02', 'e12', 'e012'],
    metric: [1, 0, 1, 1, 0, 0, -1, 0],
  },
  STA: {
    names: ['1', 'et', 'ex', 'ey', 'ez', 'etx', 'ety', 'etz', 'exy', 'exz', 'eyz', 'etxy', 'etxz', 'etyz', 'exyz', 'I'],
    metric: [1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1],
  },
  R3: {
    names: ['1', 'e1', 'e2', 'e3', 'e12', 'e13', 'e23', 'e123'],
    metric: [1, 1, 1, 1, -1, -1, -1, -1],
  },
};

export interface InspectPanelCallbacks {
  onEditCoeff: (entryIdx: number, bladeIdx: number, value: number) => void;
}

export class InspectStashPanel {
  readonly element: HTMLDivElement;
  private readonly callbacks: InspectPanelCallbacks;
  private readonly headerMetaEl: HTMLDivElement;
  private readonly tableContainer: HTMLDivElement;
  private readonly detailContainer: HTMLDivElement;
  private readonly copyStatusEl: HTMLSpanElement;

  private selectedEntryIdx: number | null = null;
  private lastFrame: GsirFrame | null = null;

  constructor(callbacks: InspectPanelCallbacks) {
    this.callbacks = callbacks;

    this.element = document.createElement('div');
    this.element.className = 'gs-inspect-panel';

    const topBar = document.createElement('div');
    topBar.className = 'gs-inspect-topbar';

    this.headerMetaEl = document.createElement('div');
    this.headerMetaEl.className = 'gs-inspect-algebra-badge';
    this.headerMetaEl.textContent = 'No algebra loaded';

    const copyBtn = document.createElement('button');
    copyBtn.type = 'button';
    copyBtn.className = 'gs-btn gs-btn-ghost';
    copyBtn.textContent = 'Copy JSON';
    copyBtn.addEventListener('click', () => this.copyInspectJson());

    this.copyStatusEl = document.createElement('span');
    this.copyStatusEl.className = 'gs-copy-toast';

    topBar.append(this.headerMetaEl, this.copyStatusEl, copyBtn);

    // Metric legend
    const legend = document.createElement('div');
    legend.className = 'gs-metric-legend';
    legend.innerHTML =
      '<span class="gs-metric-pill metric-neg">−1</span>' +
      '<span class="gs-metric-pill metric-zero">0</span>' +
      '<span class="gs-metric-pill metric-pos">+1</span>' +
      '<span class="gs-metric-caption">Click any row to edit blades live in Lean</span>';

    this.tableContainer = document.createElement('div');
    this.tableContainer.className = 'gs-inspect-table-wrap';

    this.detailContainer = document.createElement('div');
    this.detailContainer.className = 'gs-inspect-detail';

    this.element.append(topBar, legend, this.tableContainer, this.detailContainer);
  }

  /**
   * Highlights the Inspect entry matching a clicked 3D viewport object (by label or handleId).
   * Returns true if a matching entry was found and focused.
   */
  selectByHandleOrLabel(handleId: number, label?: string): boolean {
    const inspect = this.lastFrame?.meta?.inspect ?? [];
    if (inspect.length === 0) return false;
    const cleanLabel = (label ?? '').replace(/^Drag\s+/i, '').trim().toLowerCase();
    let match =
      (cleanLabel
        ? inspect.find(
            (e) =>
              e.name.toLowerCase() === cleanLabel ||
              e.name.toLowerCase().includes(cleanLabel) ||
              cleanLabel.includes(e.name.toLowerCase())
          )
        : undefined) ??
      inspect.find((e) => e.idx === handleId) ??
      inspect[0];

    if (!match) return false;
    this.selectedEntryIdx = match.idx;
    if (this.lastFrame) {
      this.update(this.lastFrame);
      const selectedRow = this.tableContainer.querySelector('tr.selected');
      selectedRow?.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    }
    return true;
  }

  update(frame: GsirFrame): void {
    this.lastFrame = frame;
    const algebra = frame.meta?.algebra;
    const inspect = frame.meta?.inspect ?? [];

    if (algebra) {
      this.headerMetaEl.textContent = `${algebra.name} · Cl(${algebra.p},${algebra.q},${algebra.r})${
        algebra.conformalWitt ? ' Witt' : ''
      }`;
    } else {
      this.headerMetaEl.textContent = `Cl(${frame.header.p},${frame.header.q},${frame.header.r})`;
    }

    // Build coeff map from 0x11 INSPECT_COEFFS
    const coeffMap = new Map<number, Float32Array>();
    for (const ic of frame.inspectCoeffs) {
      coeffMap.set(ic.entryIdx, ic.coeffs);
    }

    if (inspect.length === 0) {
      this.tableContainer.innerHTML =
        '<div class="gs-empty-state">No multivectors exposed in current frame.<br/>Load a preset or run a script in Lean.</div>';
      this.detailContainer.innerHTML = '';
      return;
    }

    if (this.selectedEntryIdx === null || !inspect.some((e) => e.idx === this.selectedEntryIdx)) {
      this.selectedEntryIdx = inspect[0]!.idx;
    }

    const table = document.createElement('table');
    table.className = 'gs-inspect-table';
    table.innerHTML =
      '<thead><tr><th>#</th><th>Gr</th><th>Name</th><th>Value</th></tr></thead><tbody></tbody>';
    const tbody = table.querySelector('tbody')!;

    for (const entry of inspect) {
      const tr = document.createElement('tr');
      if (entry.idx === this.selectedEntryIdx) tr.classList.add('selected');
      tr.innerHTML =
        `<td class="mono dim">${entry.idx}</td>` +
        `<td class="mono"><span class="gs-grade-pill">g${entry.grade}</span></td>` +
        `<td class="mono strong">${this.escapeHtml(entry.name)}</td>` +
        `<td class="mono val">${this.escapeHtml(entry.formatted)}</td>`;
      tr.addEventListener('click', () => {
        this.selectedEntryIdx = entry.idx;
        if (this.lastFrame) this.update(this.lastFrame);
      });
      tbody.appendChild(tr);
    }

    this.tableContainer.innerHTML = '';
    this.tableContainer.appendChild(table);

    // Render expanded clickable color-coded metric matrix for selected entry
    const selected = inspect.find((e) => e.idx === this.selectedEntryIdx);
    this.renderBladeMatrix(selected?.idx ?? 0, selected?.name ?? '', selected?.editable ?? true, coeffMap);
  }

  private renderBladeMatrix(
    entryIdx: number,
    name: string,
    editable: boolean,
    coeffMap: Map<number, Float32Array>
  ): void {
    const algebra = this.lastFrame?.meta?.algebra;
    const fallback = algebra ? DISPLAY_BASIS_PRESETS[algebra.name] : undefined;
    const basisNames =
      algebra?.basisNames && algebra.basisNames.length > 0 ? algebra.basisNames : (fallback?.names ?? []);
    const basisMetric =
      algebra?.basisMetric && algebra.basisMetric.length > 0 ? algebra.basisMetric : (fallback?.metric ?? []);
    const coeffs = coeffMap.get(entryIdx);
    const count = Math.max(basisNames.length, coeffs?.length ?? 0);

    this.detailContainer.innerHTML = '';
    if (count === 0) return;

    const heading = document.createElement('div');
    heading.className = 'gs-detail-heading';
    heading.textContent = `Blades & Metric · ${name || `#${entryIdx}`}`;
    this.detailContainer.appendChild(heading);

    const grid = document.createElement('div');
    grid.className = 'gs-blade-grid';

    for (let b = 0; b < count; b++) {
      const bName = basisNames[b] ?? `b${b}`;
      const metric = basisMetric[b] ?? 1;
      const val = coeffs?.[b] ?? 0;

      const cell = document.createElement('div');
      const metricCls = metric < 0 ? 'metric-neg' : metric === 0 ? 'metric-zero' : 'metric-pos';
      cell.className = `gs-blade-cell ${metricCls}${Math.abs(val) > 1e-4 ? ' nonzero' : ''}`;
      cell.title = `${bName}² = ${metric > 0 ? '+1' : metric}`;

      const top = document.createElement('div');
      top.className = 'gs-blade-head';
      top.innerHTML = `<span class="mono">${this.escapeHtml(bName)}</span><span class="gs-blade-sig">${
        metric > 0 ? '+1' : metric
      }</span>`;

      const input = document.createElement('input');
      input.type = 'number';
      input.step = '0.05';
      input.className = 'gs-blade-input';
      input.value = Math.abs(val) < 1e-5 ? '0' : Number(val.toFixed(4)).toString();
      input.disabled = !editable;
      input.addEventListener('change', () => {
        const parsed = Number.parseFloat(input.value);
        if (Number.isFinite(parsed)) {
          this.callbacks.onEditCoeff(entryIdx, b, parsed);
        }
      });

      const slider = document.createElement('input');
      slider.type = 'range';
      slider.className = 'gs-blade-slider';
      slider.min = '-2';
      slider.max = '2';
      slider.step = '0.02';
      slider.value = String(Math.max(-2, Math.min(2, val)));
      slider.disabled = !editable;
      slider.addEventListener('input', () => {
        const nextVal = Number.parseFloat(slider.value);
        input.value = nextVal.toFixed(2);
        this.callbacks.onEditCoeff(entryIdx, b, nextVal);
      });

      cell.append(top, input, slider);
      grid.appendChild(cell);
    }

    this.detailContainer.appendChild(grid);
  }

  private async copyInspectJson(): Promise<void> {
    if (!this.lastFrame) return;
    const payload = {
      algebra: this.lastFrame.meta?.algebra ?? null,
      inspect: (this.lastFrame.meta?.inspect ?? []).map((entry) => {
        const coeffs = this.lastFrame!.inspectCoeffs.find((c) => c.entryIdx === entry.idx)?.coeffs;
        return {
          ...entry,
          coeffs: coeffs ? Array.from(coeffs) : [],
        };
      }),
    };
    try {
      await navigator.clipboard.writeText(JSON.stringify(payload, null, 2));
      this.copyStatusEl.textContent = 'Copied!';
      setTimeout(() => {
        this.copyStatusEl.textContent = '';
      }, 1400);
    } catch {
      this.copyStatusEl.textContent = 'Clipboard blocked';
    }
  }

  private escapeHtml(str: string): string {
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }
}
