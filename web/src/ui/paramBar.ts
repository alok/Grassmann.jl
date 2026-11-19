// Floating @param Slider Overlay + Compact Simulation Timeline Bar
// STRICT PURITY: Zero math in JS — sliders dispatch `{op:"setParam", name, value}` straight to Lean,
// and timeline scrubs dispatch binary `Tick(0, t)` straight to Lean.

import type { ParamSpec } from '../gsir/types';

export interface ParamTimelineCallbacks {
  onSetParam: (name: string, value: number) => void;
  onTogglePlay: () => void;
  onScrubTime: (timeSec: number) => void;
  onSpeedChange: (speed: number) => void;
  onResetTime: () => void;
}

const SPEEDS = [0.25, 0.5, 1, 2] as const;

export class ParamTimelineOverlay {
  readonly paramPanel: HTMLDivElement;
  readonly timelineBar: HTMLDivElement;

  private readonly callbacks: ParamTimelineCallbacks;
  private readonly paramListEl: HTMLDivElement;
  private readonly playBtn: HTMLButtonElement;
  private readonly timeSlider: HTMLInputElement;
  private readonly timeLabel: HTMLSpanElement;
  private readonly speedButtons = new Map<number, HTMLButtonElement>();

  private lastParamSignature = '';
  private paramInputs = new Map<string, { range: HTMLInputElement; readout: HTMLSpanElement }>();
  private scrubbingTime = false;
  private activeSpeed = 1;

  constructor(callbacks: ParamTimelineCallbacks) {
    this.callbacks = callbacks;

    // 1. Dynamic Floating @param Sliders Card
    this.paramPanel = document.createElement('div');
    this.paramPanel.className = 'gs-param-panel hidden';

    const pHead = document.createElement('div');
    pHead.className = 'gs-param-header';
    pHead.innerHTML = '<span class="gs-param-title">Parameters</span><span class="gs-param-tag mono">@param</span>';

    this.paramListEl = document.createElement('div');
    this.paramListEl.className = 'gs-param-list';

    this.paramPanel.append(pHead, this.paramListEl);

    // 2. Compact Bottom-Center Simulation Timeline Bar
    this.timelineBar = document.createElement('div');
    this.timelineBar.className = 'gs-timeline-bar';

    this.playBtn = document.createElement('button');
    this.playBtn.type = 'button';
    this.playBtn.className = 'gs-tl-play';
    this.playBtn.title = 'Play / Pause Simulation (Space)';
    this.playBtn.textContent = '▶';
    this.playBtn.addEventListener('click', () => this.callbacks.onTogglePlay());

    this.timeLabel = document.createElement('span');
    this.timeLabel.className = 'gs-tl-time mono';
    this.timeLabel.textContent = 't=0.00s';

    this.timeSlider = document.createElement('input');
    this.timeSlider.type = 'range';
    this.timeSlider.className = 'gs-tl-slider';
    this.timeSlider.min = '0';
    this.timeSlider.max = '12';
    this.timeSlider.step = '0.02';
    this.timeSlider.value = '0';
    this.timeSlider.setAttribute('aria-label', 'Simulation time t');
    this.timeSlider.addEventListener('pointerdown', () => {
      this.scrubbingTime = true;
    });
    this.timeSlider.addEventListener('pointerup', () => {
      this.scrubbingTime = false;
    });
    this.timeSlider.addEventListener('input', () => {
      const nextT = Number.parseFloat(this.timeSlider.value);
      if (Number.isFinite(nextT)) {
        this.timeLabel.textContent = `t=${nextT.toFixed(2)}s`;
        this.callbacks.onScrubTime(nextT);
      }
    });

    const speedGroup = document.createElement('div');
    speedGroup.className = 'gs-tl-speeds';
    for (const sp of SPEEDS) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = `gs-tl-speed${sp === 1 ? ' active' : ''}`;
      btn.textContent = `${sp}×`;
      btn.addEventListener('click', () => {
        this.setSpeed(sp);
        this.callbacks.onSpeedChange(sp);
      });
      speedGroup.appendChild(btn);
      this.speedButtons.set(sp, btn);
    }

    const resetBtn = document.createElement('button');
    resetBtn.type = 'button';
    resetBtn.className = 'gs-tl-reset';
    resetBtn.title = 'Reset simulation clock (t = 0)';
    resetBtn.textContent = '↺';
    resetBtn.addEventListener('click', () => {
      this.setTime(0);
      this.callbacks.onResetTime();
    });

    this.timelineBar.append(this.playBtn, this.timeLabel, this.timeSlider, speedGroup, resetBtn);
  }

  updateParams(params: ParamSpec[] | undefined, visible = true): void {
    const list = params ?? [];
    if (!visible || list.length === 0) {
      this.paramPanel.classList.add('hidden');
      this.lastParamSignature = '';
      return;
    }

    this.paramPanel.classList.remove('hidden');
    const sig = list.map((p) => `${p.name}:${p.min}:${p.max}:${p.step ?? ''}:${p.label ?? ''}`).join('|');

    if (sig !== this.lastParamSignature) {
      this.lastParamSignature = sig;
      this.paramListEl.innerHTML = '';
      this.paramInputs.clear();

      for (const spec of list) {
        const row = document.createElement('div');
        row.className = 'gs-param-row';

        const meta = document.createElement('div');
        meta.className = 'gs-param-meta';
        const lbl = document.createElement('span');
        lbl.className = 'gs-param-name';
        lbl.textContent = spec.label || spec.name;

        const readout = document.createElement('span');
        readout.className = 'gs-param-val mono';
        readout.textContent = formatParamValue(spec.value, spec.step);

        meta.append(lbl, readout);

        const range = document.createElement('input');
        range.type = 'range';
        range.className = 'gs-param-slider';
        range.min = String(spec.min);
        range.max = String(spec.max);
        const step = spec.step ?? Math.max(0.005, (spec.max - spec.min) / 200);
        range.step = String(step);
        range.value = String(spec.value);
        range.dataset.paramName = spec.name;

        range.addEventListener('input', () => {
          const val = Number.parseFloat(range.value);
          if (Number.isFinite(val)) {
            readout.textContent = formatParamValue(val, step);
            this.callbacks.onSetParam(spec.name, val);
          }
        });

        row.append(meta, range);
        this.paramListEl.appendChild(row);
        this.paramInputs.set(spec.name, { range, readout });
      }
      return;
    }

    // Update live values without destroying active slider drag focus
    for (const spec of list) {
      const pair = this.paramInputs.get(spec.name);
      if (!pair) continue;
      if (document.activeElement !== pair.range) {
        pair.range.value = String(spec.value);
      }
      pair.readout.textContent = formatParamValue(spec.value, spec.step);
    }
  }

  setTimelineVisible(visible: boolean): void {
    this.timelineBar.classList.toggle('hidden', !visible);
  }

  setPlaying(running: boolean): void {
    this.playBtn.textContent = running ? '⏸' : '▶';
    this.playBtn.classList.toggle('active', running);
  }

  setTime(timeSec: number): void {
    const wrapped = timeSec % 12;
    this.timeLabel.textContent = `t=${timeSec.toFixed(2)}s`;
    if (!this.scrubbingTime) {
      this.timeSlider.value = wrapped.toFixed(2);
    }
  }

  setSpeed(speed: number): void {
    this.activeSpeed = speed;
    for (const [sp, btn] of this.speedButtons) {
      btn.classList.toggle('active', sp === this.activeSpeed);
    }
  }
}

function formatParamValue(val: number, step?: number): string {
  const decimals = step && step < 0.01 ? 3 : step && step >= 1 ? 0 : 2;
  return Number.isFinite(val) ? val.toFixed(decimals) : '0';
}
