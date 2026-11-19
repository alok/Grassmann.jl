// LeanCalculator 3D (Surface z=f(x,y,t) + Implicit Equations + STA Cl(3,1) -+++ Lab)
// + Enkimute-Inspired GAlculator Tactile Keypad (R, C, D, M, P2D, P3D, C2D, C3D, e0..e5, x1..x10)
// STRICT PURITY: Every button & input dispatches JSON InputEvents straight to Lean!

import type { CalcMeta, JsonInputEvent } from '../gsir/types';

export interface CalculatorPanelCallbacks {
  onDispatchJson: (event: JsonInputEvent) => void;
  onToggleAnim?: (running: boolean) => void;
}

const GALCULATOR_ALGEBRAS = [
  { key: 'R', label: 'R', sig: 'ℝ' },
  { key: 'C', label: 'C', sig: '0,1' },
  { key: 'D', label: 'D', sig: '0,0,1' },
  { key: 'M', label: 'M', sig: '−+++' },
  { key: 'P2D', label: 'P2D', sig: '2,0,1' },
  { key: 'P3D', label: 'P3D', sig: '3,0,1' },
  { key: 'C2D', label: 'C2D', sig: '3,1' },
  { key: 'C3D', label: 'C3D', sig: '4,1' },
];

const BASIS_KEYS = ['e0', 'e1', 'e2', 'e3', 'e4', 'e5', 'ori', 'inf', 'pss'];
const OP_KEYS = [
  { key: '^', label: '∧' },
  { key: '&', label: '∨' },
  { key: '<<', label: '●' },
  { key: '*', label: '*' },
  { key: 'Exp', label: 'Exp' },
  { key: 'Dual', label: 'Dual' },
  { key: 'Rev', label: 'Rev' },
  { key: 'Conj', label: 'Conj' },
  { key: 'Inv', label: 'x⁻¹' },
  { key: '+', label: '+' },
  { key: '-', label: '−' },
  { key: 'ST', label: 'STO' },
  { key: '=', label: '=' },
  { key: 'CLEAR', label: 'CLR' },
];

export class CalculatorStudioPanel {
  readonly element: HTMLDivElement;
  private readonly callbacks: CalculatorPanelCallbacks;

  private readonly subTabButtons = new Map<string, HTMLButtonElement>();
  private readonly subTabPanes = new Map<string, HTMLDivElement>();
  private readonly calcDisplayEl: HTMLDivElement;
  private readonly calcHistoryEl: HTMLDivElement;
  private readonly calcRegistersEl: HTMLDivElement;
  private readonly calcExprInput: HTMLInputElement;
  private readonly activeModeBadge: HTMLSpanElement;

  private activeCalcMode = 'STA';
  private eqList: string[] = ['x^2 + y^2 - 1.4', 'y - 0.6*x^2 + 0.5'];
  private readonly eqListEl: HTMLDivElement;
  private surfaceExprInput!: HTMLInputElement;
  private surfaceBoundInput!: HTMLInputElement;
  private implicit3dInput!: HTMLInputElement;
  private implicitBoundInput!: HTMLInputElement;
  private implicitGpuRaymarch = true;
  private implicitBound = 2.2;
  private syncImplicitToggle?: () => void;
  private paramFxInput!: HTMLInputElement;
  private paramFyInput!: HTMLInputElement;
  private paramFzInput!: HTMLInputElement;
  private readonly inlineErrorEl: HTMLDivElement;

  constructor(callbacks: CalculatorPanelCallbacks) {
    this.callbacks = callbacks;

    this.element = document.createElement('div');
    this.element.className = 'gs-calc-panel';

    // Sub-tabs: STA | Surface | Implicit 3D | Parametric | 2D Eq | GAlculator
    const tabBar = document.createElement('div');
    tabBar.className = 'gs-subtabs gs-subtabs-6';

    const tabs = [
      { id: 'sta', label: 'STA' },
      { id: 'surface', label: 'Surface' },
      { id: 'implicit3d', label: 'Imp 3D' },
      { id: 'parametric', label: 'Param' },
      { id: 'implicit', label: '2D Eq' },
      { id: 'galc', label: 'GAlc' },
    ];

    for (const t of tabs) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-subtab-btn';
      btn.textContent = t.label;
      btn.addEventListener('click', () => this.selectSubTab(t.id));
      tabBar.appendChild(btn);
      this.subTabButtons.set(t.id, btn);
    }

    // Build panes
    const staPane = this.buildStaPane();
    const surfacePane = this.buildSurfacePane();
    const implicit3dPane = this.buildImplicit3dPane();
    const parametricPane = this.buildParametricPane();
    const implicitPane = document.createElement('div');
    implicitPane.className = 'gs-subtab-pane';
    this.eqListEl = document.createElement('div');
    this.buildImplicitPane(implicitPane);

    const galcPane = document.createElement('div');
    galcPane.className = 'gs-subtab-pane';
    this.activeModeBadge = document.createElement('span');
    this.calcDisplayEl = document.createElement('div');
    this.calcHistoryEl = document.createElement('div');
    this.calcRegistersEl = document.createElement('div');
    this.calcExprInput = document.createElement('input');
    this.buildGAlculatorPane(galcPane);

    this.subTabPanes.set('sta', staPane);
    this.subTabPanes.set('surface', surfacePane);
    this.subTabPanes.set('implicit3d', implicit3dPane);
    this.subTabPanes.set('parametric', parametricPane);
    this.subTabPanes.set('implicit', implicitPane);
    this.subTabPanes.set('galc', galcPane);

    this.inlineErrorEl = document.createElement('div');
    this.inlineErrorEl.className = 'gs-calc-error hidden';

    this.element.append(
      tabBar,
      this.inlineErrorEl,
      staPane,
      surfacePane,
      implicit3dPane,
      parametricPane,
      implicitPane,
      galcPane
    );
    this.selectSubTab('sta');
  }

  setInlineError(message: string | null): void {
    if (!message) {
      this.inlineErrorEl.textContent = '';
      this.inlineErrorEl.classList.add('hidden');
      return;
    }
    this.inlineErrorEl.textContent = message;
    this.inlineErrorEl.classList.remove('hidden');
  }

  getSurfaceExpr(): string {
    return this.surfaceExprInput?.value.trim() ?? '';
  }

  setSurfaceExpr(expr: string, bound?: number): void {
    if (this.surfaceExprInput) this.surfaceExprInput.value = expr;
    if (this.surfaceBoundInput && typeof bound === 'number' && Number.isFinite(bound) && bound > 0) {
      this.surfaceBoundInput.value = String(bound);
    }
  }

  getSurfaceBound(): number {
    return Math.max(0.5, Number.parseFloat(this.surfaceBoundInput?.value ?? '2.5') || 2.5);
  }

  getImplicitExpr(): string {
    return this.implicit3dInput?.value.trim() ?? '';
  }

  getImplicitOptions(): { gpuRaymarch: boolean; bound: number } {
    return { gpuRaymarch: this.implicitGpuRaymarch, bound: this.implicitBound };
  }

  setImplicitExpr(expr: string, gpuRaymarch?: boolean, bound?: number): void {
    if (this.implicit3dInput) this.implicit3dInput.value = expr;
    if (typeof gpuRaymarch === 'boolean') {
      this.implicitGpuRaymarch = gpuRaymarch;
      this.syncImplicitToggle?.();
    }
    if (typeof bound === 'number' && Number.isFinite(bound) && bound > 0) {
      const clamped = Math.max(0.5, Math.min(20, bound));
      this.implicitBound = clamped;
      if (this.implicitBoundInput) this.implicitBoundInput.value = String(clamped);
    }
  }

  getParametricExpr(): { fx: string; fy: string; fz: string } {
    return {
      fx: this.paramFxInput?.value.trim() ?? '',
      fy: this.paramFyInput?.value.trim() ?? '',
      fz: this.paramFzInput?.value.trim() ?? '',
    };
  }

  setParametricExpr(expr: { fx: string; fy: string; fz: string }): void {
    if (this.paramFxInput) this.paramFxInput.value = expr.fx;
    if (this.paramFyInput) this.paramFyInput.value = expr.fy;
    if (this.paramFzInput) this.paramFzInput.value = expr.fz;
  }

  selectSubTab(id: string): void {
    for (const [k, btn] of this.subTabButtons) {
      btn.classList.toggle('active', k === id);
    }
    for (const [k, pane] of this.subTabPanes) {
      pane.classList.toggle('hidden', k !== id);
    }
  }

  updateCalcState(calc: CalcMeta | undefined): void {
    if (!calc) return;
    this.activeCalcMode = calc.mode || this.activeCalcMode;
    this.activeModeBadge.textContent = this.activeCalcMode;
    this.calcDisplayEl.textContent = calc.display || '0';

    this.calcHistoryEl.innerHTML = '';
    for (const line of calc.history.slice(-6)) {
      const row = document.createElement('div');
      row.className = 'gs-calc-history-row';
      row.textContent = line;
      this.calcHistoryEl.appendChild(row);
    }

    this.calcRegistersEl.innerHTML = '';
    const regMap = new Map(calc.registers.map((r) => [r.slot, r.formatted]));
    for (let i = 1; i <= 10; i++) {
      const slot = `x${i}`;
      const val = regMap.get(slot);
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = `gs-reg-key${val ? ' populated' : ''}`;
      btn.innerHTML = `<span class="slot">${slot}</span><span class="val">${val ?? '—'}</span>`;
      btn.addEventListener('click', () => {
        this.callbacks.onDispatchJson({ op: 'calcKey', key: slot });
      });
      this.calcRegistersEl.appendChild(btn);
    }
  }

  private buildStaPane(): HTMLDivElement {
    const pane = document.createElement('div');
    pane.className = 'gs-subtab-pane';

    const badge = document.createElement('div');
    badge.className = 'gs-sta-banner';
    badge.innerHTML =
      '<strong>Spacetime Algebra Cl(3,1) · Signature (−+++)</strong>' +
      '<span>ALOK-950 exact STA domain · Boost & bivector planes solved in Lean 4</span>';

    const aInput = document.createElement('input');
    aInput.className = 'gs-input mono';
    aInput.value = '0.2*et + 1.1*ex + 0.35*ey';

    const bInput = document.createElement('input');
    bInput.className = 'gs-input mono';
    bInput.value = '0.1*et + 0.25*ex + 0.95*ey + 0.4*ez';

    const betaVal = document.createElement('span');
    betaVal.className = 'mono strong';
    betaVal.textContent = 'β = 0.00 c';

    const betaSlider = document.createElement('input');
    betaSlider.type = 'range';
    betaSlider.min = '-0.95';
    betaSlider.max = '0.95';
    betaSlider.step = '0.01';
    betaSlider.value = '0';
    betaSlider.className = 'gs-slider';

    const axisSelect = document.createElement('select');
    axisSelect.className = 'gs-select';
    for (const ax of ['ex', 'ey', 'ez']) {
      const opt = document.createElement('option');
      opt.value = ax;
      opt.textContent = `Boost along ${ax}`;
      axisSelect.appendChild(opt);
    }

    const emitSta = (opExpr: string) => {
      const beta = Number.parseFloat(betaSlider.value);
      betaVal.textContent = `β = ${beta.toFixed(2)} c`;
      const expr = `A=${aInput.value}; B=${bInput.value}; beta=${beta.toFixed(3)}; axis=${axisSelect.value}; ${opExpr}`;
      this.callbacks.onDispatchJson({ op: 'calcEval', mode: 'STA', expr });
    };

    betaSlider.addEventListener('input', () => emitSta('boost(A ∧ B)'));

    const opRow = document.createElement('div');
    opRow.className = 'gs-chip-row';
    const ops = [
      { label: 'A ∧ B (Wedge)', expr: 'A ^ B' },
      { label: 'A * B (Geo)', expr: 'A * B' },
      { label: '~A (Rev)', expr: '~A' },
      { label: 'Lorentz Boost', expr: 'boost(A ∧ B)' },
    ];
    for (const o of ops) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-btn gs-btn-ghost';
      btn.textContent = o.label;
      btn.addEventListener('click', () => emitSta(o.expr));
      opRow.appendChild(btn);
    }

    const fA = this.field('Multivector A (et, ex, ey, ez)', aInput);
    const fB = this.field('Multivector B (et, ex, ey, ez)', bInput);

    const boostWrap = document.createElement('div');
    boostWrap.className = 'gs-field';
    const boostHead = document.createElement('div');
    boostHead.className = 'gs-row-between';
    const boostLbl = document.createElement('label');
    boostLbl.textContent = 'Lorentz Boost Velocity';
    boostHead.append(boostLbl, betaVal);
    boostWrap.append(boostHead, betaSlider, axisSelect);

    pane.append(badge, fA, fB, boostWrap, opRow);
    return pane;
  }

  private buildSurfacePane(): HTMLDivElement {
    const pane = document.createElement('div');
    pane.className = 'gs-subtab-pane';

    const exprInput = document.createElement('input');
    exprInput.className = 'gs-input mono';
    exprInput.value = 'sin(sqrt(x^2 + y^2)*3 - t) / (1 + 0.35*(x^2 + y^2))';
    this.surfaceExprInput = exprInput;

    const gridInput = document.createElement('input');
    gridInput.type = 'range';
    gridInput.min = '16';
    gridInput.max = '64';
    gridInput.step = '4';
    gridInput.value = '48';
    gridInput.className = 'gs-slider';

    const gridVal = document.createElement('span');
    gridVal.className = 'mono';
    gridVal.textContent = '48×48';

    const boundInput = document.createElement('input');
    boundInput.type = 'number';
    boundInput.className = 'gs-input gs-input-sm';
    boundInput.value = '2.5';
    boundInput.step = '0.5';
    this.surfaceBoundInput = boundInput;

    const evalSurface = () => {
      const b = Math.max(0.5, Number.parseFloat(boundInput.value) || 2.5);
      const gridN = Number.parseInt(gridInput.value, 10) || 48;
      gridVal.textContent = `${gridN}×${gridN}`;
      // #17 Fix #5: exact evalSurface JSON event
      this.callbacks.onDispatchJson({
        op: 'evalSurface',
        expr: exprInput.value.trim(),
        bounds: [-b, b, -b, b],
        gridN,
      });
    };

    gridInput.addEventListener('change', evalSurface);

    const presetsRow = document.createElement('div');
    presetsRow.className = 'gs-chip-row';
    const samples = [
      { name: 'Ripple', expr: 'sin(sqrt(x^2 + y^2)*3 - t) / (1 + 0.35*(x^2 + y^2))' },
      { name: 'Saddle', expr: '0.35*(x^2 - y^2)*cos(t)' },
      { name: 'Interference', expr: '0.45*sin(2*x + t)*cos(2*y - t)' },
      { name: 'Gaussian', expr: '1.4*exp(-(x^2 + y^2)*0.7)' },
    ];
    for (const s of samples) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-chip';
      btn.textContent = s.name;
      btn.addEventListener('click', () => {
        exprInput.value = s.expr;
        evalSurface();
      });
      presetsRow.appendChild(btn);
    }

    const actions = document.createElement('div');
    actions.className = 'gs-row-gap';
    const evalBtn = document.createElement('button');
    evalBtn.type = 'button';
    evalBtn.className = 'gs-btn gs-btn-primary';
    evalBtn.textContent = 'Evaluate Surface in Lean';
    evalBtn.addEventListener('click', evalSurface);

    let playing = false;
    const playBtn = document.createElement('button');
    playBtn.type = 'button';
    playBtn.className = 'gs-btn gs-btn-ghost';
    playBtn.textContent = '▶ Animate t';
    playBtn.addEventListener('click', () => {
      playing = !playing;
      playBtn.textContent = playing ? '⏸ Pause t' : '▶ Animate t';
      this.callbacks.onToggleAnim?.(playing);
    });
    actions.append(evalBtn, playBtn);

    const gridField = document.createElement('div');
    gridField.className = 'gs-field';
    const gHead = document.createElement('div');
    gHead.className = 'gs-row-between';
    gHead.innerHTML = '<label>Mesh Grid Density (Lean AD Normals)</label>';
    gHead.appendChild(gridVal);
    gridField.append(gHead, gridInput);

    pane.append(
      this.field('z = f(x, y, t)', exprInput),
      presetsRow,
      this.field('Domain Half-Extent (±)', boundInput),
      gridField,
      actions
    );
    return pane;
  }

  private buildImplicit3dPane(): HTMLDivElement {
    const pane = document.createElement('div');
    pane.className = 'gs-subtab-pane';

    const exprInput = document.createElement('input');
    exprInput.className = 'gs-input mono';
    exprInput.value = 'sin(x*2)*cos(y*2) + sin(y*2)*cos(z*2) + sin(z*2)*cos(x*2)';
    this.implicit3dInput = exprInput;

    // Crisp Mesh / GPU Raymarch toggle switch
    const modeSwitch = document.createElement('div');
    modeSwitch.className = 'gs-segmented';
    const meshBtn = document.createElement('button');
    meshBtn.type = 'button';
    meshBtn.className = 'gs-seg-btn';
    meshBtn.textContent = 'Marching Tet Mesh';
    const gpuBtn = document.createElement('button');
    gpuBtn.type = 'button';
    gpuBtn.className = 'gs-seg-btn active';
    gpuBtn.textContent = 'GPU Raymarch (GLSL3)';

    const boundInput = document.createElement('input');
    boundInput.type = 'number';
    boundInput.className = 'gs-input gs-input-sm';
    boundInput.value = String(this.implicitBound);
    boundInput.min = '0.5';
    boundInput.max = '20';
    boundInput.step = '0.2';
    this.implicitBoundInput = boundInput;

    const syncToggle = () => {
      meshBtn.classList.toggle('active', !this.implicitGpuRaymarch);
      gpuBtn.classList.toggle('active', this.implicitGpuRaymarch);
    };
    this.syncImplicitToggle = syncToggle;
    const emitImplicit = () => {
      const parsedBound = Number.parseFloat(boundInput.value);
      const b = Number.isFinite(parsedBound) ? Math.max(0.5, Math.min(20, parsedBound)) : this.implicitBound;
      this.implicitBound = b;
      boundInput.value = String(b);
      this.callbacks.onDispatchJson({
        op: 'evalImplicit',
        expr: exprInput.value.trim(),
        gpuRaymarch: this.implicitGpuRaymarch,
        bound: b,
        bounds: [-b, b, -b, b, -b, b],
        gridN: 24,
      });
    };
    boundInput.addEventListener('change', emitImplicit);

    meshBtn.addEventListener('click', () => {
      this.implicitGpuRaymarch = false;
      syncToggle();
      emitImplicit();
    });
    gpuBtn.addEventListener('click', () => {
      this.implicitGpuRaymarch = true;
      syncToggle();
      emitImplicit();
    });
    modeSwitch.append(meshBtn, gpuBtn);

    const chips = document.createElement('div');
    chips.className = 'gs-chip-row';
    const samples = [
      { name: 'Gyroid', expr: 'sin(x*2)*cos(y*2) + sin(y*2)*cos(z*2) + sin(z*2)*cos(x*2)' },
      { name: 'Schwarz P', expr: 'cos(x*2) + cos(y*2) + cos(z*2)' },
      { name: 'Torus', expr: '(sqrt(x^2 + z^2) - 1.2)^2 + y^2 - 0.32' },
      { name: 'Genus-2', expr: '((x^2 + y^2)^2 - x^2 + y^2)^2 + z^2 - 0.08' },
      { name: 'Metaballs', expr: '1/(0.2 + (x-0.7*cos(t))^2 + y^2 + z^2) + 1/(0.2 + (x+0.7*cos(t))^2 + y^2 + z^2) - 2.4' },
    ];
    for (const s of samples) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-chip';
      btn.textContent = s.name;
      btn.addEventListener('click', () => {
        exprInput.value = s.expr;
        emitImplicit();
      });
      chips.appendChild(btn);
    }

    const evalBtn = document.createElement('button');
    evalBtn.type = 'button';
    evalBtn.className = 'gs-btn gs-btn-primary';
    evalBtn.textContent = 'Evaluate Implicit 3D in Lean';
    evalBtn.addEventListener('click', emitImplicit);

    const note = document.createElement('div');
    note.className = 'gs-hint-text';
    note.textContent = 'Compiled live in Lean 4: either Kuhn Marching Tetrahedra or straight-line GLSL 300 es raymarching.';

    pane.append(
      this.field('Implicit f(x, y, z, t) = 0', exprInput),
      this.field('Domain Half-Extent (±)', boundInput),
      this.field('Renderer Backend (Lean 4)', modeSwitch),
      chips,
      evalBtn,
      note
    );
    return pane;
  }

  private buildParametricPane(): HTMLDivElement {
    const pane = document.createElement('div');
    pane.className = 'gs-subtab-pane';

    const fxInput = document.createElement('input');
    fxInput.className = 'gs-input mono';
    fxInput.value = '(1.2 + 0.45*v*cos(u*0.5))*cos(u)';
    this.paramFxInput = fxInput;

    const fyInput = document.createElement('input');
    fyInput.className = 'gs-input mono';
    fyInput.value = '0.45*v*sin(u*0.5)';
    this.paramFyInput = fyInput;

    const fzInput = document.createElement('input');
    fzInput.className = 'gs-input mono';
    fzInput.value = '(1.2 + 0.45*v*cos(u*0.5))*sin(u)';
    this.paramFzInput = fzInput;

    const emitParam = () => {
      this.callbacks.onDispatchJson({
        op: 'evalParametric',
        fx: fxInput.value.trim(),
        fy: fyInput.value.trim(),
        fz: fzInput.value.trim(),
        uBounds: [0, 6.283185],
        vBounds: [-1, 1],
        nu: 44,
        nv: 28,
        uRange: [0, 6.283185],
        vRange: [-1, 1],
        gridN: 36,
      });
    };

    const chips = document.createElement('div');
    chips.className = 'gs-chip-row';
    const samples = [
      {
        name: 'Möbius',
        fx: '(1.2 + 0.45*v*cos(u*0.5))*cos(u)',
        fy: '0.45*v*sin(u*0.5)',
        fz: '(1.2 + 0.45*v*cos(u*0.5))*sin(u)',
      },
      {
        name: 'Klein Bottle',
        fx: '(1.4 + cos(u*0.5)*sin(v*3.14) - sin(u*0.5)*sin(2*v*3.14))*cos(u)',
        fy: 'sin(u*0.5)*sin(v*3.14) + cos(u*0.5)*sin(2*v*3.14)',
        fz: '(1.4 + cos(u*0.5)*sin(v*3.14) - sin(u*0.5)*sin(2*v*3.14))*sin(u)',
      },
      {
        name: 'Clifford Torus',
        fx: 'cos(u) / (1.42 - sin(v*3.14))',
        fy: 'cos(v*3.14) / (1.42 - sin(v*3.14))',
        fz: 'sin(u) / (1.42 - sin(v*3.14))',
      },
      {
        name: 'Enneper',
        fx: '0.45*(u - u^3/3 + u*v^2)',
        fy: '0.45*(u^2 - v^2)',
        fz: '0.45*(v - v^3/3 + v*u^2)',
      },
    ];
    for (const s of samples) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-chip';
      btn.textContent = s.name;
      btn.addEventListener('click', () => {
        fxInput.value = s.fx;
        fyInput.value = s.fy;
        fzInput.value = s.fz;
        emitParam();
      });
      chips.appendChild(btn);
    }

    const evalBtn = document.createElement('button');
    evalBtn.type = 'button';
    evalBtn.className = 'gs-btn gs-btn-primary';
    evalBtn.textContent = 'Evaluate Parametric 3D in Lean';
    evalBtn.addEventListener('click', emitParam);

    pane.append(
      this.field('x(u, v, t)', fxInput),
      this.field('y(u, v, t)', fyInput),
      this.field('z(u, v, t)', fzInput),
      chips,
      evalBtn
    );
    return pane;
  }

  private buildImplicitPane(pane: HTMLDivElement): void {
    const desc = document.createElement('div');
    desc.className = 'gs-hint-text';
    desc.textContent = 'Implicit equations f(x,y) = 0 solved in Lean → 2D Contour Overlay & common intersections.';

    const renderEqs = () => {
      this.eqListEl.innerHTML = '';
      this.eqList.forEach((eq, idx) => {
        const row = document.createElement('div');
        row.className = 'gs-row-gap';
        const inp = document.createElement('input');
        inp.className = 'gs-input mono';
        inp.value = eq;
        inp.addEventListener('input', () => {
          this.eqList[idx] = inp.value;
        });
        const del = document.createElement('button');
        del.type = 'button';
        del.className = 'gs-icon-btn';
        del.textContent = '×';
        del.addEventListener('click', () => {
          if (this.eqList.length <= 1) return;
          this.eqList.splice(idx, 1);
          renderEqs();
        });
        row.append(inp, del);
        this.eqListEl.appendChild(row);
      });
    };
    renderEqs();

    const controls = document.createElement('div');
    controls.className = 'gs-row-gap';
    const addBtn = document.createElement('button');
    addBtn.type = 'button';
    addBtn.className = 'gs-btn gs-btn-ghost';
    addBtn.textContent = '+ Equation';
    addBtn.addEventListener('click', () => {
      this.eqList.push('x - y');
      renderEqs();
    });

    const solveBtn = document.createElement('button');
    solveBtn.type = 'button';
    solveBtn.className = 'gs-btn gs-btn-primary';
    solveBtn.textContent = 'Solve Contours in Lean';
    solveBtn.addEventListener('click', () => {
      this.callbacks.onDispatchJson({
        op: 'evalEquations',
        equations: this.eqList.map((e) => e.trim()).filter(Boolean),
        bounds: [-2.5, 2.5, -2.5, 2.5],
        gridN: 64,
      });
    });

    controls.append(addBtn, solveBtn);
    pane.append(desc, this.eqListEl, controls);
  }

  private buildGAlculatorPane(pane: HTMLDivElement): void {
    // Algebra Mode Strip (R, C, D, M, P2D, P3D, C2D, C3D)
    const algStrip = document.createElement('div');
    algStrip.className = 'gs-galc-alg-strip';
    for (const a of GALCULATOR_ALGEBRAS) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-galc-alg-key';
      btn.innerHTML = `<strong>${a.label}</strong><span>${a.sig}</span>`;
      btn.addEventListener('click', () => {
        this.activeCalcMode = a.key;
        this.activeModeBadge.textContent = a.key;
        this.callbacks.onDispatchJson({ op: 'calcKey', key: `mode:${a.key}` });
      });
      algStrip.appendChild(btn);
    }

    // Display Screen
    const screen = document.createElement('div');
    screen.className = 'gs-galc-screen';
    const screenTop = document.createElement('div');
    screenTop.className = 'gs-row-between';
    this.activeModeBadge.className = 'gs-grade-pill';
    this.activeModeBadge.textContent = this.activeCalcMode;
    const screenLbl = document.createElement('span');
    screenLbl.className = 'dim mono';
    screenLbl.textContent = 'GAlculator · Lean 4';
    screenTop.append(this.activeModeBadge, screenLbl);

    this.calcHistoryEl.className = 'gs-calc-history';
    this.calcDisplayEl.className = 'gs-galc-display mono';
    this.calcDisplayEl.textContent = '0';
    screen.append(screenTop, this.calcHistoryEl, this.calcDisplayEl);

    // Direct expression bar
    const exprRow = document.createElement('div');
    exprRow.className = 'gs-row-gap';
    this.calcExprInput.type = 'text';
    this.calcExprInput.className = 'gs-input mono';
    this.calcExprInput.placeholder = 'Enter GA expr (e.g. e1 + e2 * e12)...';
    this.calcExprInput.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') {
        const expr = this.calcExprInput.value.trim();
        if (expr) {
          this.callbacks.onDispatchJson({ op: 'calcEval', mode: this.activeCalcMode, expr });
          this.calcExprInput.value = '';
        }
      }
    });
    const evalBtn = document.createElement('button');
    evalBtn.type = 'button';
    evalBtn.className = 'gs-btn gs-btn-primary';
    evalBtn.textContent = 'Eval';
    evalBtn.addEventListener('click', () => {
      const expr = this.calcExprInput.value.trim();
      if (expr) {
        this.callbacks.onDispatchJson({ op: 'calcEval', mode: this.activeCalcMode, expr });
        this.calcExprInput.value = '';
      }
    });
    exprRow.append(this.calcExprInput, evalBtn);

    // Basis Keypad
    const basisGrid = document.createElement('div');
    basisGrid.className = 'gs-galc-grid';
    for (const k of BASIS_KEYS) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-keycap gs-keycap-basis';
      btn.textContent = k;
      btn.addEventListener('click', () => {
        this.callbacks.onDispatchJson({ op: 'calcKey', key: k });
      });
      basisGrid.appendChild(btn);
    }

    // Operator Keypad
    const opGrid = document.createElement('div');
    opGrid.className = 'gs-galc-grid';
    for (const op of OP_KEYS) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = `gs-keycap${op.key === '=' ? ' gs-keycap-eval' : op.key === 'CLEAR' ? ' gs-keycap-clr' : ''}`;
      btn.textContent = op.label;
      btn.addEventListener('click', () => {
        if (op.key === 'CLEAR') {
          this.calcExprInput.value = '';
        } else if (op.key === '=' && this.calcExprInput.value.trim()) {
          this.callbacks.onDispatchJson({
            op: 'calcEval',
            mode: this.activeCalcMode,
            expr: this.calcExprInput.value.trim(),
          });
          this.calcExprInput.value = '';
          return;
        }
        this.callbacks.onDispatchJson({ op: 'calcKey', key: op.key });
      });
      opGrid.appendChild(btn);
    }

    // Registers x1..x10
    const regHead = document.createElement('div');
    regHead.className = 'gs-section-mini-title';
    regHead.textContent = 'Registers x1–x10';
    this.calcRegistersEl.className = 'gs-reg-grid';
    for (let i = 1; i <= 10; i++) {
      const slot = `x${i}`;
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-reg-key';
      btn.innerHTML = `<span class="slot">${slot}</span><span class="val">—</span>`;
      btn.addEventListener('click', () => this.callbacks.onDispatchJson({ op: 'calcKey', key: slot }));
      this.calcRegistersEl.appendChild(btn);
    }

    pane.append(algStrip, screen, exprRow, basisGrid, opGrid, regHead, this.calcRegistersEl);
  }

  private field(label: string, control: HTMLElement): HTMLDivElement {
    const wrap = document.createElement('div');
    wrap.className = 'gs-field';
    const lbl = document.createElement('label');
    lbl.textContent = label;
    wrap.append(lbl, control);
    return wrap;
  }
}
