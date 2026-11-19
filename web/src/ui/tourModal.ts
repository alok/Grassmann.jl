// Interactive 6-Stop Guided Geometric Algebra Tour Overlay (T shortcut + Tour pill)
// Non-obstructive floating glass card ready to consume Lean's `loadTourStop` (0..5)
// once Wave 6C lands and wired cleanly to all 6 flagship Lean presets today.
// Zero GA math in JS — purely drives Lean presets & displays KaTeX guidance!

import katex from 'katex';

export interface GuidedTourStop {
  index: number;
  id: string;
  presetId: string;
  mode: 'coffeeshop' | 'wedge';
  algebra: string;
  title: string;
  formula: string;
  blurb: string;
  tryIt: string;
}

export const GUIDED_TOUR_STOPS: readonly GuidedTourStop[] = [
  {
    index: 0,
    id: 'points_lines',
    presetId: 'pga3d_points_and_lines',
    mode: 'coffeeshop',
    algebra: 'PGA3',
    title: 'Points, Lines & Planes',
    formula: 'L = A \\vee B, \\qquad P = L \\wedge \\Pi \\;\\in\\; \\mathrm{Cl}_{3,0,1}',
    blurb: 'In 3D Projective Geometric Algebra, points, lines, and planes are unified multivectors — Join (∨) spans them and Meet (∧) intersects them without coordinates.',
    tryIt: 'Drag any glowing 3D point handle to watch every Join line and Meet point recompute live in Lean 4.',
  },
  {
    index: 1,
    id: 'bunny_slicing',
    presetId: 'pga3d_slicing',
    mode: 'coffeeshop',
    algebra: 'PGA3',
    title: '3D Bunny Plane Slicing',
    formula: 'P_{\\text{cut}} = \\Pi \\wedge (A \\vee B), \\qquad \\Pi = d\\,e_0 + \\mathbf{n}',
    blurb: 'A single PGA3 plane Π clips a sculpted 3D mesh into solid & frosted-glass halves while stitching exact 2D cross-section contour loops.',
    tryIt: 'Drag the cyan slice handle vertically through the bunny and watch the bottom-left 2D Contour Slice update at 60fps.',
  },
  {
    index: 2,
    id: 'rigid_physics',
    presetId: 'pga3d_bouncing_cube',
    mode: 'coffeeshop',
    algebra: 'PGA3',
    title: 'Rigid-Body Motors & Physics',
    formula: '\\dot{M} = -\\tfrac{1}{2} M B, \\qquad M \\in \\mathrm{Spin}(3,0,1)',
    blurb: 'Rotations and translations fuse into one PGA3 motor M, integrating 8-corner rigid-body floor impulses and angular-momentum bivectors via RK4.',
    tryIt: 'Press Play (Space) or scrub Gravity, Bounce, and Initial Spin in the floating @param card on the left.',
  },
  {
    index: 3,
    id: 'conformal_raymarch',
    presetId: 'cga3d_opns_cyclide',
    mode: 'coffeeshop',
    algebra: 'CGA3',
    title: 'Conformal Spheres & GPU Raymarch',
    formula: '\\{x \\in \\mathbb{R}^3 : P(x) \\wedge S = 0\\} \\;\\subset\\; \\mathrm{Cl}_{4,1}',
    blurb: 'Conformal GA embeds spheres, circles, and Dupin cyclides as flat blades whose Outer Product Null Space (OPNS) Lean 4 compiles live into GLSL 300 es.',
    tryIt: 'Orbit smoothly around the raymarched surface — zero mesh tessellation, 100% Lean-emitted GPU fragment shader.',
  },
  {
    index: 4,
    id: 'terrell_penrose',
    presetId: 'sta_terrell_penrose',
    mode: 'coffeeshop',
    algebra: 'STA Cl(3,1)',
    title: 'Relativistic Terrell-Penrose Cl(3,1)',
    formula: "X' = B X \\widetilde{B}, \\qquad \\theta_{\\text{TP}} = \\arcsin(\\beta)",
    blurb: 'In Spacetime Algebra Cl(3,1) (−+++), combining Lorentz contraction with past light-cone photon travel time makes a relativistic cube appear rotated rather than squished.',
    tryIt: 'Scrub Speed β up to 0.90c and compare the Doppler-tinted optical cube against the dashed cyan Lorentz ghost.',
  },
  {
    index: 5,
    id: 'play_wedge',
    presetId: 'game_wedge',
    mode: 'wedge',
    algebra: 'Wedge 2D/3D',
    title: 'Play Wedge 2D & 3D!',
    formula: 'A \\vee B \\;\\text{(pull)}, \\qquad a \\wedge b \\;\\text{(push)}',
    blurb: 'Master projective constructions hands-on across 16+ 2D & 3D puzzles, 6 interactive tutorials, and procedural challenges — every move verified live in Lean 4.',
    tryIt: 'Pull points A and B apart to Join them into the red target line (or click A → click B → Join ∨).',
  },
];

export interface GuidedTourCallbacks {
  onLoadStop: (stop: GuidedTourStop) => void;
  onClose?: () => void;
}

export class GuidedTourOverlay {
  readonly element: HTMLElement;
  private readonly callbacks: GuidedTourCallbacks;
  private readonly badgeEl: HTMLSpanElement;
  private readonly stepCounterEl: HTMLSpanElement;
  private readonly titleEl: HTMLHeadingElement;
  private readonly formulaEl: HTMLDivElement;
  private readonly blurbEl: HTMLParagraphElement;
  private readonly tryItEl: HTMLDivElement;
  private readonly dotsWrap: HTMLDivElement;
  private readonly prevBtn: HTMLButtonElement;
  private readonly nextBtn: HTMLButtonElement;

  private stops: readonly GuidedTourStop[] = GUIDED_TOUR_STOPS;
  private currentIndex = 0;
  private isOpen = false;

  constructor(callbacks: GuidedTourCallbacks) {
    this.callbacks = callbacks;

    this.element = document.createElement('aside');
    this.element.className = 'gs-tour-card hidden';
    this.element.setAttribute('aria-label', 'Guided Geometric Algebra Tour');

    const head = document.createElement('div');
    head.className = 'gs-tour-head';
    const meta = document.createElement('div');
    meta.className = 'gs-tour-meta';
    this.badgeEl = document.createElement('span');
    this.badgeEl.className = 'gs-tour-badge mono';
    this.stepCounterEl = document.createElement('span');
    this.stepCounterEl.className = 'gs-tour-step mono';
    meta.append(this.badgeEl, this.stepCounterEl);

    const closeBtn = document.createElement('button');
    closeBtn.type = 'button';
    closeBtn.className = 'gs-icon-btn gs-tour-close';
    closeBtn.title = 'Close Guided Tour (Esc)';
    closeBtn.textContent = '×';
    closeBtn.addEventListener('click', () => this.close());
    head.append(meta, closeBtn);

    this.titleEl = document.createElement('h4');
    this.titleEl.className = 'gs-tour-title';

    this.formulaEl = document.createElement('div');
    this.formulaEl.className = 'gs-tour-formula';

    this.blurbEl = document.createElement('p');
    this.blurbEl.className = 'gs-tour-blurb';

    this.tryItEl = document.createElement('div');
    this.tryItEl.className = 'gs-tour-try';

    const foot = document.createElement('div');
    foot.className = 'gs-tour-foot';

    this.dotsWrap = document.createElement('div');
    this.dotsWrap.className = 'gs-tour-dots';

    const nav = document.createElement('div');
    nav.className = 'gs-tour-nav';

    this.prevBtn = document.createElement('button');
    this.prevBtn.type = 'button';
    this.prevBtn.className = 'gs-btn gs-btn-ghost gs-tour-prev';
    this.prevBtn.textContent = '← Back';
    this.prevBtn.addEventListener('click', () => this.goTo(this.currentIndex - 1));

    this.nextBtn = document.createElement('button');
    this.nextBtn.type = 'button';
    this.nextBtn.className = 'gs-btn gs-btn-primary gs-tour-next';
    this.nextBtn.textContent = 'Next →';
    this.nextBtn.addEventListener('click', () => {
      if (this.currentIndex >= this.stops.length - 1) {
        this.close();
      } else {
        this.goTo(this.currentIndex + 1);
      }
    });

    nav.append(this.prevBtn, this.nextBtn);
    foot.append(this.dotsWrap, nav);

    this.element.append(head, this.titleEl, this.formulaEl, this.blurbEl, this.tryItEl, foot);
    this.renderStop(false);
  }

  setStops(stops: readonly GuidedTourStop[]): void {
    if (stops.length === 0) return;
    this.stops = stops;
    this.currentIndex = Math.min(this.currentIndex, stops.length - 1);
    this.renderStop(false);
  }

  get opened(): boolean {
    return this.isOpen;
  }

  get activeIndex(): number {
    return this.currentIndex;
  }

  get stopCount(): number {
    return this.stops.length;
  }

  open(startIndex = 0): void {
    this.isOpen = true;
    this.element.classList.remove('hidden');
    this.goTo(startIndex);
  }

  close(): void {
    if (!this.isOpen) return;
    this.isOpen = false;
    this.element.classList.add('hidden');
    this.callbacks.onClose?.();
  }

  toggle(): void {
    if (this.isOpen) this.close();
    else this.open(this.currentIndex);
  }

  goTo(index: number): void {
    const clamped = Math.max(0, Math.min(this.stops.length - 1, index));
    this.currentIndex = clamped;
    this.renderStop(true);
  }

  private renderStop(emitLoad: boolean): void {
    const stop = this.stops[this.currentIndex];
    if (!stop) return;

    this.badgeEl.textContent = stop.algebra;
    this.stepCounterEl.textContent = `Tour ${this.currentIndex + 1} / ${this.stops.length}`;
    this.titleEl.textContent = stop.title;
    try {
      this.formulaEl.innerHTML = katex.renderToString(stop.formula, {
        throwOnError: false,
        displayMode: false,
      });
    } catch {
      this.formulaEl.textContent = stop.formula;
    }
    this.blurbEl.textContent = stop.blurb;
    this.tryItEl.innerHTML = `<strong>Try it:</strong> ${escapeText(stop.tryIt)}`;

    this.prevBtn.disabled = this.currentIndex === 0;
    this.nextBtn.textContent = this.currentIndex >= this.stops.length - 1 ? 'Done ✓' : 'Next →';

    this.dotsWrap.innerHTML = '';
    for (let i = 0; i < this.stops.length; i++) {
      const dot = document.createElement('button');
      dot.type = 'button';
      dot.className = `gs-tour-dot${i === this.currentIndex ? ' active' : ''}`;
      dot.title = `${i + 1}. ${this.stops[i]!.title}`;
      dot.setAttribute('aria-label', `Tour stop ${i + 1}: ${this.stops[i]!.title}`);
      dot.addEventListener('click', () => this.goTo(i));
      this.dotsWrap.appendChild(dot);
    }

    if (emitLoad) {
      this.callbacks.onLoadStop(stop);
    }
  }
}

function escapeText(raw: string): string {
  return raw.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
