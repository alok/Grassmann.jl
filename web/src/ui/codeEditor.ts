// CoffeeShop Interactive Code Editor
// Features:
// - Monospace line-numbered code editor with Shift+Enter Run & Tab indent
// - Signature CoffeeShop inline drag-to-scrub floating number slider on numeric selection
// - Signature CoffeeShop inline floating hex color picker on 0xRRGGBB / #RRGGBB selection
// - Live diagnostics list from Lean's metaJson.diagnostics

import type { DiagnosticItem } from '../gsir/types';

export interface CodeEditorCallbacks {
  onRun: (code: string) => void;
  onChange?: (code: string) => void;
}

interface ScrubberSelection {
  start: number;
  end: number;
  kind: 'number' | 'color';
  numValue?: number;
  decimals?: number;
  colorPrefix?: '0x' | '#';
  colorHex?: string;
}

const NUMBER_RE = /^-?\d+(?:\.\d+)?$/;
const HEX_COLOR_RE = /^(0x|#)([0-9a-fA-F]{6})$/;

export class CoffeeShopCodeEditor {
  readonly element: HTMLDivElement;
  private readonly textarea: HTMLTextAreaElement;
  private readonly gutter: HTMLDivElement;
  private readonly diagnosticsEl: HTMLDivElement;
  private readonly popover: HTMLDivElement;
  private readonly runBtn: HTMLButtonElement;
  private readonly callbacks: CodeEditorCallbacks;

  private activeSelection: ScrubberSelection | null = null;
  private lastScrubRunMs = 0;

  constructor(callbacks: CodeEditorCallbacks) {
    this.callbacks = callbacks;

    this.element = document.createElement('div');
    this.element.className = 'gs-editor-root';

    // Header toolbar
    const header = document.createElement('div');
    header.className = 'gs-panel-header';

    const title = document.createElement('div');
    title.className = 'gs-panel-title';
    title.innerHTML = '<span>Lean GA Script</span><span class="gs-kbd">⇧↵ Run</span>';

    const actions = document.createElement('div');
    actions.className = 'gs-panel-actions';

    const tip = document.createElement('span');
    tip.className = 'gs-hint-chip';
    tip.textContent = 'Select a number or 0xRRGGBB to scrub';

    this.runBtn = document.createElement('button');
    this.runBtn.type = 'button';
    this.runBtn.className = 'gs-btn gs-btn-primary';
    this.runBtn.textContent = '▸ Run';
    this.runBtn.addEventListener('click', () => this.callbacks.onRun(this.getCode()));

    actions.append(tip, this.runBtn);
    header.append(title, actions);

    // Editor body
    const body = document.createElement('div');
    body.className = 'gs-editor-body';

    this.gutter = document.createElement('div');
    this.gutter.className = 'gs-editor-gutter';
    this.gutter.setAttribute('aria-hidden', 'true');

    this.textarea = document.createElement('textarea');
    this.textarea.className = 'gs-editor-textarea';
    this.textarea.spellcheck = false;
    this.textarea.autocapitalize = 'off';
    this.textarea.autocomplete = 'off';
    this.textarea.placeholder = '// Write Grassmann.lean / CoffeeShop GA code...\n// Shift+Enter evaluates in Lean 4';

    this.popover = document.createElement('div');
    this.popover.className = 'gs-inline-popover hidden';

    body.append(this.gutter, this.textarea, this.popover);

    // Diagnostics bar
    this.diagnosticsEl = document.createElement('div');
    this.diagnosticsEl.className = 'gs-diagnostics hidden';

    this.element.append(header, body, this.diagnosticsEl);

    // Event bindings
    this.textarea.addEventListener('input', () => {
      this.syncLineNumbers();
      this.callbacks.onChange?.(this.textarea.value);
    });
    this.textarea.addEventListener('scroll', () => {
      this.gutter.scrollTop = this.textarea.scrollTop;
    });
    this.textarea.addEventListener('keydown', this.onKeyDown);
    this.textarea.addEventListener('select', this.inspectSelection);
    this.textarea.addEventListener('mouseup', this.inspectSelection);
    this.textarea.addEventListener('keyup', this.inspectSelection);
    document.addEventListener('pointerdown', this.onDocumentPointerDown);

    this.syncLineNumbers();
  }

  setCode(code: string): void {
    this.textarea.value = code;
    this.hidePopover();
    this.syncLineNumbers();
  }

  getCode(): string {
    return this.textarea.value;
  }

  setDiagnostics(items: Array<string | DiagnosticItem> | undefined): void {
    if (!items || items.length === 0) {
      this.diagnosticsEl.classList.add('hidden');
      this.diagnosticsEl.innerHTML = '';
      return;
    }
    this.diagnosticsEl.classList.remove('hidden');
    this.diagnosticsEl.innerHTML = '';
    for (const item of items) {
      const row = document.createElement('div');
      const sev = typeof item === 'string' ? 'error' : (item.severity ?? 'error');
      row.className = `gs-diag-row gs-diag-${sev}`;
      const loc =
        typeof item === 'object' && item.line !== undefined
          ? `L${item.line}${item.col !== undefined ? `:${item.col}` : ''} `
          : '';
      row.textContent = `${loc}${typeof item === 'string' ? item : item.message}`;
      this.diagnosticsEl.appendChild(row);
    }
  }

  private syncLineNumbers(): void {
    const count = Math.max(1, this.textarea.value.split('\n').length);
    const lines: string[] = [];
    for (let i = 1; i <= count; i++) lines.push(String(i));
    this.gutter.textContent = lines.join('\n');
  }

  private readonly onKeyDown = (ev: KeyboardEvent): void => {
    if (ev.key === 'Enter' && (ev.shiftKey || ev.metaKey || ev.ctrlKey)) {
      ev.preventDefault();
      this.callbacks.onRun(this.textarea.value);
      return;
    }
    if (ev.key === 'Tab') {
      ev.preventDefault();
      const s = this.textarea.selectionStart;
      const e = this.textarea.selectionEnd;
      const v = this.textarea.value;
      this.textarea.value = `${v.slice(0, s)}  ${v.slice(e)}`;
      this.textarea.selectionStart = this.textarea.selectionEnd = s + 2;
      this.syncLineNumbers();
      this.callbacks.onChange?.(this.textarea.value);
    }
    if (ev.key === 'Escape') {
      this.hidePopover();
    }
  };

  private readonly onDocumentPointerDown = (ev: PointerEvent): void => {
    const target = ev.target as Node | null;
    if (target && !this.popover.contains(target) && target !== this.textarea) {
      this.hidePopover();
    }
  };

  private readonly inspectSelection = (): void => {
    const start = this.textarea.selectionStart;
    const end = this.textarea.selectionEnd;
    if (start === end) {
      this.hidePopover();
      return;
    }
    const token = this.textarea.value.slice(start, end).trim();
    if (!token || token.includes('\n')) {
      this.hidePopover();
      return;
    }

    const colorMatch = HEX_COLOR_RE.exec(token);
    if (colorMatch) {
      const prefix = colorMatch[1] as '0x' | '#';
      const hex = colorMatch[2]!;
      this.activeSelection = { start, end, kind: 'color', colorPrefix: prefix, colorHex: hex };
      this.showColorPopover(prefix, hex);
      return;
    }

    if (NUMBER_RE.test(token)) {
      const numValue = Number.parseFloat(token);
      if (Number.isFinite(numValue)) {
        const dotIdx = token.indexOf('.');
        const decimals = dotIdx >= 0 ? Math.min(4, Math.max(2, token.length - dotIdx - 1)) : 2;
        this.activeSelection = { start, end, kind: 'number', numValue, decimals };
        this.showNumberPopover(numValue, decimals);
        return;
      }
    }

    this.hidePopover();
  };

  private showNumberPopover(initial: number, decimals: number): void {
    const span = Math.max(2, Math.ceil(Math.abs(initial) * 2.2));
    const min = -span;
    const max = span;
    const step = decimals >= 3 ? 0.005 : 0.01;

    this.popover.innerHTML = '';
    this.popover.classList.remove('hidden');

    const label = document.createElement('span');
    label.className = 'gs-popover-label';
    label.textContent = initial.toFixed(decimals);

    const range = document.createElement('input');
    range.type = 'range';
    range.className = 'gs-popover-range';
    range.min = String(min);
    range.max = String(max);
    range.step = String(step);
    range.value = String(initial);

    range.addEventListener('input', () => {
      if (!this.activeSelection || this.activeSelection.kind !== 'number') return;
      const val = Number.parseFloat(range.value);
      const formatted = val.toFixed(decimals);
      label.textContent = formatted;
      this.replaceSelectionText(formatted);
    });

    const rangeHint = document.createElement('span');
    rangeHint.className = 'gs-popover-bounds';
    rangeHint.textContent = `[${min}..${max}]`;

    this.popover.append(label, range, rangeHint);
  }

  private showColorPopover(prefix: '0x' | '#', hex: string): void {
    this.popover.innerHTML = '';
    this.popover.classList.remove('hidden');

    const swatch = document.createElement('input');
    swatch.type = 'color';
    swatch.className = 'gs-popover-color';
    swatch.value = `#${hex.toLowerCase()}`;

    const codeLabel = document.createElement('span');
    codeLabel.className = 'gs-popover-label';
    codeLabel.textContent = `${prefix}${hex.toLowerCase()}`;

    swatch.addEventListener('input', () => {
      if (!this.activeSelection || this.activeSelection.kind !== 'color') return;
      const nextHex = swatch.value.slice(1).toLowerCase();
      const literal = `${prefix}${nextHex}`;
      codeLabel.textContent = literal;
      this.replaceSelectionText(literal);
    });

    this.popover.append(swatch, codeLabel);
  }

  private replaceSelectionText(nextToken: string): void {
    if (!this.activeSelection) return;
    const { start, end } = this.activeSelection;
    const v = this.textarea.value;
    this.textarea.value = `${v.slice(0, start)}${nextToken}${v.slice(end)}`;
    this.activeSelection.end = start + nextToken.length;
    this.textarea.setSelectionRange(start, this.activeSelection.end);
    this.syncLineNumbers();
    this.callbacks.onChange?.(this.textarea.value);

    // Throttle live Lean execution to ~60fps
    const now = performance.now();
    if (now - this.lastScrubRunMs >= 16) {
      this.lastScrubRunMs = now;
      this.callbacks.onRun(this.textarea.value);
    }
  }

  private hidePopover(): void {
    this.activeSelection = null;
    this.popover.classList.add('hidden');
  }

  dispose(): void {
    document.removeEventListener('pointerdown', this.onDocumentPointerDown);
  }
}
