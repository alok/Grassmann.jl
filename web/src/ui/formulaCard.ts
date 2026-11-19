// Collapsible KaTeX Math Formula & Summary Card Overlay
// Prefers Lean's `metaJson.formula` & `metaJson.summary` 100%, with pure static display fallback
// for flagship presets when connected to an earlier WASM build. Zero GA math in JS!

import katex from 'katex';
import type { GsirMetaJson } from '../gsir/types';

// Static display-only fallback dictionary for flagship presets (strictly overridden by Lean metaJson.{formula,summary})
const DISPLAY_FORMULA_FALLBACK: Record<string, { formula: string; summary: string }> = {
  pga3d_slicing: {
    formula: '\\Pi \\wedge \\mathcal{M} \\;\\in\\; \\mathrm{Cl}(3,0,1)',
    summary: 'Exact PGA3 projective plane slicing a 3D mesh into solid & ghost halves + 2D contour.',
  },
  pga3d_points_and_lines: {
    formula: 'L = A \\vee B, \\quad P = L \\wedge \\Pi',
    summary: 'Coordinate-free 3D projective Join (∨) and Meet (∧) on draggable PGA3 points.',
  },
  pga3d_physics_free_top: {
    formula: '\\dot{M} = -\\tfrac{1}{2} M B, \\quad \\dot{B} = -\\tfrac{1}{2}(B \\times I^{-1}B)',
    summary: 'Torque-free rigid body RK4 in PGA3 showcasing the Dzhanibekov intermediate-axis flip.',
  },
  pga3d_motor_orbits: {
    formula: 'M(t) = \\exp\\!\\left(-\\tfrac{t}{2}(\\omega\\, e_{23} + v\\, e_{01})\\right)',
    summary: 'Parameterized 3D PGA screw motors sweeping continuous helical orbits & surfaces.',
  },
  cga3d_intersections: {
    formula: 'C = S_1 \\wedge S_2, \\quad P_\\pm = S_1 \\wedge L \\;\\in\\; \\mathrm{Cl}(4,1)',
    summary: 'Live 3D Conformal outer-product intersections across spheres, planes, lines & circles.',
  },
  cga3d_opns_cyclide: {
    formula: '\\{x \\in \\mathbb{R}^3 : P(x) \\wedge S = 0\\}',
    summary: 'Outer Product Null Space (OPNS) sphere-traced live via Lean-compiled GLSL 300 es.',
  },
  sta_lorentz_boost: {
    formula: 'B(\\phi) = \\exp\\!\\left(-\\tfrac{\\phi}{2}\\, e_t e_x\\right), \\quad e_t^2 = -1',
    summary: 'Spacetime Algebra Cl(3,1) (−+++) Minkowski light-cone & hyperbolic Lorentz boost.',
  },
  surface_3d: {
    formula: 'z = f(x, y, t), \\quad \\mathbf{n} = \\star(\\partial_x \\mathbf{r} \\wedge \\partial_y \\mathbf{r})',
    summary: 'Explicit 3D surface evaluated in Lean 4 with exact dual-number forward-AD normals.',
  },
  implicit_expr: {
    formula: 'f(x, y, z, t) = 0',
    summary: '3D isosurface extracted live in Lean 4 via adaptive Kuhn Marching Tetrahedra.',
  },
  implicit_gpu: {
    formula: 'f(x, y, z, t) = 0 \\;\\xrightarrow{\\text{GPUInit}}\\text{GLSL 300 es}',
    summary: 'User-typed implicit surface compiled live in Lean 4 to a GPU sphere-tracing shader.',
  },
  parametric_expr: {
    formula: '\\mathbf{r}(u, v, t) = (f_x, f_y, f_z)',
    summary: 'Parametric 3D manifold meshed with exact Lean exterior-product normals.',
  },
};

export class FormulaCardOverlay {
  readonly element: HTMLDivElement;
  private readonly toggleBtn: HTMLButtonElement;
  private readonly contentWrap: HTMLDivElement;
  private readonly mathEl: HTMLDivElement;
  private readonly summaryEl: HTMLDivElement;

  private collapsed = false;
  private lastKey = '';

  constructor() {
    this.element = document.createElement('div');
    this.element.className = 'gs-formula-card hidden';

    this.contentWrap = document.createElement('div');
    this.contentWrap.className = 'gs-formula-content';

    this.mathEl = document.createElement('div');
    this.mathEl.className = 'gs-formula-math';

    this.summaryEl = document.createElement('div');
    this.summaryEl.className = 'gs-formula-summary';

    this.contentWrap.append(this.mathEl, this.summaryEl);

    this.toggleBtn = document.createElement('button');
    this.toggleBtn.type = 'button';
    this.toggleBtn.className = 'gs-formula-toggle';
    this.toggleBtn.title = 'Collapse / Expand GA Formula Card';
    this.toggleBtn.textContent = '−';
    this.toggleBtn.addEventListener('click', () => {
      this.collapsed = !this.collapsed;
      this.element.classList.toggle('collapsed', this.collapsed);
      this.toggleBtn.textContent = this.collapsed ? '∑' : '−';
    });

    this.element.append(this.contentWrap, this.toggleBtn);
  }

  update(meta: GsirMetaJson | null | undefined, visible = true): void {
    if (!visible || !meta) {
      this.element.classList.add('hidden');
      return;
    }

    const fallback = meta.presetId ? DISPLAY_FORMULA_FALLBACK[meta.presetId] : undefined;
    const formula = (meta.formula && meta.formula.trim()) || fallback?.formula || '';
    const summary = (meta.summary && meta.summary.trim()) || fallback?.summary || '';

    if (!formula && !summary) {
      this.element.classList.add('hidden');
      return;
    }

    this.element.classList.remove('hidden');
    const key = `${formula}||${summary}`;
    if (key === this.lastKey) return;
    this.lastKey = key;

    if (formula) {
      try {
        this.mathEl.innerHTML = katex.renderToString(formula, {
          throwOnError: false,
          displayMode: false,
        });
      } catch {
        this.mathEl.textContent = formula;
      }
      this.mathEl.classList.remove('hidden');
    } else {
      this.mathEl.innerHTML = '';
      this.mathEl.classList.add('hidden');
    }

    if (summary) {
      this.summaryEl.textContent = summary;
      this.summaryEl.classList.remove('hidden');
    } else {
      this.summaryEl.textContent = '';
      this.summaryEl.classList.add('hidden');
    }
  }
}
