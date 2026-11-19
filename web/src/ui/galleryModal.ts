// Visual 74-Preset Gallery Modal (G shortcut + Gallery button)
// Multi-column searchable visual browser over the live Lean preset catalog grouped by algebra family.

import type { StudioPreset } from './presets';

export interface GalleryModalCallbacks {
  onSelectPreset: (preset: StudioPreset) => void;
}

function accentForCategory(category: string, algebra: string): string {
  const c = `${category} ${algebra}`.toLowerCase();
  if (c.includes('cga')) return 'linear-gradient(90deg, #a855f7, #38bdf8)';
  if (c.includes('sta') || c.includes('spacetime') || c.includes('relativ')) {
    return 'linear-gradient(90deg, #f59e0b, #fb7185)';
  }
  if (c.includes('implicit') || c.includes('parametric')) {
    return 'linear-gradient(90deg, #22d3ee, #c084fc)';
  }
  if (c.includes('2d')) return 'linear-gradient(90deg, #34d399, #38bdf8)';
  if (c.includes('dual') || c.includes('complex')) return 'linear-gradient(90deg, #fbbf24, #34d399)';
  return 'linear-gradient(90deg, #38bdf8, #818cf8)';
}

function featureTags(preset: StudioPreset): string[] {
  const tags: string[] = [];
  const text = `${preset.id} ${preset.title} ${preset.description} ${preset.category}`.toLowerCase();
  if (text.includes('opns') || text.includes('raymarch') || text.includes('glsl')) tags.push('GPU');
  if (text.includes('slice') || text.includes('bunny')) tags.push('Slicer');
  if (text.includes('streamline') || text.includes('flow') || text.includes('rk4') || text.includes('pendulum') || text.includes('bouncing')) {
    tags.push('Physics');
  }
  if (text.includes('implicit') || text.includes('gyroid') || text.includes('parametric')) tags.push('Surface');
  if (text.includes('drag') || text.includes('interactive')) tags.push('Draggable');
  if (tags.length === 0) tags.push(preset.algebra.includes('2') ? '2D' : '3D');
  return tags.slice(0, 3);
}

export class PresetGalleryModal {
  readonly element: HTMLDivElement;
  private readonly callbacks: GalleryModalCallbacks;
  private readonly searchInput: HTMLInputElement;
  private readonly catBar: HTMLDivElement;
  private readonly gridWrap: HTMLDivElement;
  private readonly countEl: HTMLSpanElement;

  private presets: StudioPreset[] = [];
  private activePresetId = '';
  private activeCategory = 'All';
  private isOpen = false;

  constructor(callbacks: GalleryModalCallbacks) {
    this.callbacks = callbacks;

    this.element = document.createElement('div');
    this.element.className = 'gs-modal-backdrop hidden';

    const card = document.createElement('div');
    card.className = 'gs-modal-card gs-gallery-modal';

    const head = document.createElement('div');
    head.className = 'gs-modal-head';
    const titleWrap = document.createElement('div');
    titleWrap.className = 'gs-gallery-title-wrap';
    const title = document.createElement('strong');
    title.textContent = 'Grassmann Studio Preset Gallery';
    this.countEl = document.createElement('span');
    this.countEl.className = 'gs-preset-count mono';
    this.countEl.textContent = '0 presets';
    titleWrap.append(title, this.countEl);

    const closeBtn = document.createElement('button');
    closeBtn.type = 'button';
    closeBtn.className = 'gs-icon-btn';
    closeBtn.title = 'Close Gallery (Esc)';
    closeBtn.textContent = '×';
    closeBtn.addEventListener('click', () => this.close());

    head.append(titleWrap, closeBtn);

    const controls = document.createElement('div');
    controls.className = 'gs-gallery-controls';

    this.searchInput = document.createElement('input');
    this.searchInput.type = 'search';
    this.searchInput.className = 'gs-input gs-gallery-search';
    this.searchInput.placeholder = 'Search all Lean presets (bunny, gyroid, cyclide, Maxwell, Hopf, Lorentz, origami...)';
    this.searchInput.addEventListener('input', () => this.renderGrid());

    this.catBar = document.createElement('div');
    this.catBar.className = 'gs-gallery-cats';

    controls.append(this.searchInput, this.catBar);

    this.gridWrap = document.createElement('div');
    this.gridWrap.className = 'gs-gallery-scroll';

    card.append(head, controls, this.gridWrap);
    this.element.appendChild(card);

    this.element.addEventListener('click', (ev) => {
      if (ev.target === this.element) this.close();
    });
  }

  setPresets(presets: StudioPreset[], activePresetId?: string): void {
    this.presets = presets;
    if (activePresetId) this.activePresetId = activePresetId;
    this.renderCategories();
    this.renderGrid();
  }

  open(activePresetId?: string): void {
    if (activePresetId) this.activePresetId = activePresetId;
    this.isOpen = true;
    this.element.classList.remove('hidden');
    this.renderCategories();
    this.renderGrid();
    setTimeout(() => this.searchInput.focus(), 10);
  }

  close(): void {
    this.isOpen = false;
    this.element.classList.add('hidden');
  }

  toggle(activePresetId?: string): void {
    if (this.isOpen) this.close();
    else this.open(activePresetId);
  }

  get opened(): boolean {
    return this.isOpen;
  }

  private renderCategories(): void {
    const categories = ['All', ...Array.from(new Set(this.presets.map((p) => p.category)))];
    if (!categories.includes(this.activeCategory)) {
      this.activeCategory = 'All';
    }
    this.catBar.innerHTML = '';
    for (const cat of categories) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = `gs-cat-pill${cat === this.activeCategory ? ' active' : ''}`;
      const cnt = cat === 'All' ? this.presets.length : this.presets.filter((p) => p.category === cat).length;
      btn.textContent = `${cat} (${cnt})`;
      btn.addEventListener('click', () => {
        this.activeCategory = cat;
        this.renderCategories();
        this.renderGrid();
      });
      this.catBar.appendChild(btn);
    }
  }

  private renderGrid(): void {
    const q = this.searchInput.value.trim().toLowerCase();
    const filtered = this.presets.filter((p) => {
      if (this.activeCategory !== 'All' && p.category !== this.activeCategory) return false;
      if (!q) return true;
      return (
        p.title.toLowerCase().includes(q) ||
        p.id.toLowerCase().includes(q) ||
        p.algebra.toLowerCase().includes(q) ||
        p.category.toLowerCase().includes(q) ||
        p.description.toLowerCase().includes(q)
      );
    });

    this.countEl.textContent = `${filtered.length} / ${this.presets.length} presets`;
    this.gridWrap.innerHTML = '';

    if (filtered.length === 0) {
      this.gridWrap.innerHTML = '<div class="gs-empty-state">No presets match that filter.</div>';
      return;
    }

    const byCat = new Map<string, StudioPreset[]>();
    for (const p of filtered) {
      const arr = byCat.get(p.category) ?? [];
      arr.push(p);
      byCat.set(p.category, arr);
    }

    for (const [cat, items] of byCat) {
      const sec = document.createElement('section');
      sec.className = 'gs-gallery-section';

      const hdr = document.createElement('div');
      hdr.className = 'gs-gallery-sec-head';
      hdr.innerHTML = `<span>${this.escapeHtml(cat)}</span><span class="mono dim">${items.length}</span>`;
      sec.appendChild(hdr);

      const grid = document.createElement('div');
      grid.className = 'gs-gallery-grid';

      for (const preset of items) {
        const card = document.createElement('button');
        card.type = 'button';
        card.className = `gs-gallery-card${preset.id === this.activePresetId ? ' active' : ''}`;
        card.dataset.galleryPresetId = preset.id;

        const bar = document.createElement('div');
        bar.className = 'gs-gallery-accent';
        bar.style.background = accentForCategory(preset.category, preset.algebra);

        const top = document.createElement('div');
        top.className = 'gs-gallery-card-top';
        top.innerHTML = `<span class="gs-gallery-card-title">${this.escapeHtml(preset.title)}</span>` +
          `<span class="gs-gallery-alg mono">${this.escapeHtml(preset.algebra)}</span>`;

        const desc = document.createElement('div');
        desc.className = 'gs-gallery-card-desc';
        desc.textContent = preset.description;

        const footer = document.createElement('div');
        footer.className = 'gs-gallery-card-tags';
        const sigSpan = document.createElement('span');
        sigSpan.className = 'gs-gallery-sig mono';
        sigSpan.textContent = preset.signature || preset.algebra;
        footer.appendChild(sigSpan);
        for (const tag of featureTags(preset)) {
          const pill = document.createElement('span');
          pill.className = 'gs-gallery-tag';
          pill.textContent = tag;
          footer.appendChild(pill);
        }

        card.append(bar, top, desc, footer);
        card.addEventListener('click', () => {
          this.activePresetId = preset.id;
          this.close();
          this.callbacks.onSelectPreset(preset);
        });
        grid.appendChild(card);
      }

      sec.appendChild(grid);
      this.gridWrap.appendChild(sec);
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
