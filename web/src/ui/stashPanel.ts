// CoffeeShop "My Stash" Panel:
// - Save / load sketches in localStorage with auto-captured 3D thumbnails
// - Custom W×H PNG & SVG export
// - Shareable URL hash encoding (#preset=... or #alg=...&code=...)
// - Drag & drop .ga script or .gsir binary frame loader

export interface SavedStashEntry {
  id: string;
  title: string;
  algebra: string;
  code: string;
  thumbnail: string;
  savedAt: number;
}

export interface StashPanelCallbacks {
  getCurrentSketch: () => { title: string; algebra: string; code: string; thumbnail: string };
  onLoadSketch: (entry: SavedStashEntry) => void;
  onExportPng: (width: number, height: number) => void;
  onExportSvg: (width: number, height: number) => void;
  onShareUrl: () => string;
  onLoadGsirFile: (bytes: Uint8Array, name: string) => void;
  onLoadScriptFile: (code: string, name: string) => void;
}

const STORAGE_KEY = 'grassmann_studio_stash_v1';

export class MyStashPanel {
  readonly element: HTMLDivElement;
  private readonly callbacks: StashPanelCallbacks;
  private readonly titleInput: HTMLInputElement;
  private readonly widthInput: HTMLInputElement;
  private readonly heightInput: HTMLInputElement;
  private readonly cardsEl: HTMLDivElement;
  private readonly shareToastEl: HTMLSpanElement;
  private entries: SavedStashEntry[] = [];

  constructor(callbacks: StashPanelCallbacks) {
    this.callbacks = callbacks;
    this.entries = this.loadFromStorage();

    this.element = document.createElement('div');
    this.element.className = 'gs-stash-panel';

    // Save current sketch box
    const saveBox = document.createElement('div');
    saveBox.className = 'gs-stash-section';

    this.titleInput = document.createElement('input');
    this.titleInput.type = 'text';
    this.titleInput.className = 'gs-input';
    this.titleInput.placeholder = 'Sketch title...';

    const saveRow = document.createElement('div');
    saveRow.className = 'gs-row-gap';

    const saveBtn = document.createElement('button');
    saveBtn.type = 'button';
    saveBtn.className = 'gs-btn gs-btn-primary';
    saveBtn.textContent = '★ Save to Stash';
    saveBtn.addEventListener('click', () => this.saveCurrent());

    const shareBtn = document.createElement('button');
    shareBtn.type = 'button';
    shareBtn.className = 'gs-btn gs-btn-ghost';
    shareBtn.textContent = 'Copy Share URL';
    shareBtn.addEventListener('click', () => this.copyShareUrl());

    this.shareToastEl = document.createElement('span');
    this.shareToastEl.className = 'gs-copy-toast';

    saveRow.append(saveBtn, shareBtn);
    saveBox.append(this.titleInput, saveRow, this.shareToastEl);

    // Export W×H PNG/SVG
    const exportBox = document.createElement('div');
    exportBox.className = 'gs-stash-section';
    const exportLabel = document.createElement('div');
    exportLabel.className = 'gs-section-mini-title';
    exportLabel.textContent = 'Export Viewport';

    const dimRow = document.createElement('div');
    dimRow.className = 'gs-row-gap';

    this.widthInput = document.createElement('input');
    this.widthInput.type = 'number';
    this.widthInput.className = 'gs-input gs-input-sm';
    this.widthInput.value = '1600';
    this.widthInput.min = '320';
    this.widthInput.max = '4096';

    const times = document.createElement('span');
    times.className = 'dim';
    times.textContent = '×';

    this.heightInput = document.createElement('input');
    this.heightInput.type = 'number';
    this.heightInput.className = 'gs-input gs-input-sm';
    this.heightInput.value = '1000';
    this.heightInput.min = '240';
    this.heightInput.max = '4096';

    const pngBtn = document.createElement('button');
    pngBtn.type = 'button';
    pngBtn.className = 'gs-btn gs-btn-ghost';
    pngBtn.textContent = 'PNG';
    pngBtn.addEventListener('click', () => {
      const w = Number.parseInt(this.widthInput.value, 10) || 1600;
      const h = Number.parseInt(this.heightInput.value, 10) || 1000;
      this.callbacks.onExportPng(w, h);
    });

    const svgBtn = document.createElement('button');
    svgBtn.type = 'button';
    svgBtn.className = 'gs-btn gs-btn-ghost';
    svgBtn.textContent = 'SVG';
    svgBtn.addEventListener('click', () => {
      const w = Number.parseInt(this.widthInput.value, 10) || 1200;
      const h = Number.parseInt(this.heightInput.value, 10) || 800;
      this.callbacks.onExportSvg(w, h);
    });

    dimRow.append(this.widthInput, times, this.heightInput, pngBtn, svgBtn);
    exportBox.append(exportLabel, dimRow);

    // Drag & Drop .ga / .gsir dropzone
    const dropzone = document.createElement('label');
    dropzone.className = 'gs-dropzone';
    dropzone.textContent = 'Drop or click to open .gsir binary snapshot or .ga script';

    const fileInput = document.createElement('input');
    fileInput.type = 'file';
    fileInput.accept = '.gsir,.bin,.ga,.lean,.txt';
    fileInput.style.display = 'none';
    fileInput.addEventListener('change', () => {
      const file = fileInput.files?.[0];
      if (file) void this.handleFile(file);
      fileInput.value = '';
    });
    dropzone.appendChild(fileInput);

    dropzone.addEventListener('dragover', (e) => {
      e.preventDefault();
      dropzone.classList.add('dragover');
    });
    dropzone.addEventListener('dragleave', () => dropzone.classList.remove('dragover'));
    dropzone.addEventListener('drop', (e) => {
      e.preventDefault();
      dropzone.classList.remove('dragover');
      const file = e.dataTransfer?.files[0];
      if (file) void this.handleFile(file);
    });

    // Saved cards
    this.cardsEl = document.createElement('div');
    this.cardsEl.className = 'gs-stash-cards';

    this.element.append(saveBox, exportBox, dropzone, this.cardsEl);
    this.renderCards();
  }

  private saveCurrent(): void {
    const cur = this.callbacks.getCurrentSketch();
    const title = this.titleInput.value.trim() || cur.title || `Sketch ${this.entries.length + 1}`;
    const entry: SavedStashEntry = {
      id: `stash_${Date.now()}`,
      title,
      algebra: cur.algebra,
      code: cur.code,
      thumbnail: cur.thumbnail,
      savedAt: Date.now(),
    };
    this.entries.unshift(entry);
    this.entries = this.entries.slice(0, 24);
    this.persist();
    this.titleInput.value = '';
    this.renderCards();
  }

  private async copyShareUrl(): Promise<void> {
    const url = this.callbacks.onShareUrl();
    try {
      await navigator.clipboard.writeText(url);
      this.shareToastEl.textContent = 'Share URL copied to clipboard!';
    } catch {
      this.shareToastEl.textContent = 'URL hash updated in address bar';
    }
    setTimeout(() => {
      this.shareToastEl.textContent = '';
    }, 1800);
  }

  private async handleFile(file: File): Promise<void> {
    if (file.name.endsWith('.gsir') || file.name.endsWith('.bin')) {
      const ab = await file.arrayBuffer();
      this.callbacks.onLoadGsirFile(new Uint8Array(ab), file.name);
    } else {
      const text = await file.text();
      this.callbacks.onLoadScriptFile(text, file.name);
    }
  }

  private renderCards(): void {
    this.cardsEl.innerHTML = '';
    if (this.entries.length === 0) {
      this.cardsEl.innerHTML = '<div class="gs-empty-state">No saved sketches yet. Click ★ Save to Stash.</div>';
      return;
    }

    for (const entry of this.entries) {
      const card = document.createElement('div');
      card.className = 'gs-stash-card';

      if (entry.thumbnail) {
        const img = document.createElement('img');
        img.src = entry.thumbnail;
        img.alt = entry.title;
        img.className = 'gs-stash-thumb';
        card.appendChild(img);
      }

      const info = document.createElement('div');
      info.className = 'gs-stash-card-info';
      const t = document.createElement('div');
      t.className = 'gs-stash-card-title';
      t.textContent = entry.title;
      const meta = document.createElement('div');
      meta.className = 'gs-stash-card-meta';
      meta.textContent = `${entry.algebra} · ${new Date(entry.savedAt).toLocaleTimeString()}`;

      const delBtn = document.createElement('button');
      delBtn.type = 'button';
      delBtn.className = 'gs-icon-btn gs-stash-del';
      delBtn.title = 'Delete saved sketch';
      delBtn.textContent = '×';
      delBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        this.entries = this.entries.filter((x) => x.id !== entry.id);
        this.persist();
        this.renderCards();
      });

      info.append(t, meta);
      card.append(info, delBtn);
      card.addEventListener('click', () => this.callbacks.onLoadSketch(entry));
      this.cardsEl.appendChild(card);
    }
  }

  private loadFromStorage(): SavedStashEntry[] {
    try {
      const raw = localStorage.getItem(STORAGE_KEY);
      if (!raw) return [];
      const parsed = JSON.parse(raw);
      return Array.isArray(parsed) ? (parsed as SavedStashEntry[]) : [];
    } catch {
      return [];
    }
  }

  private persist(): void {
    try {
      localStorage.setItem(STORAGE_KEY, JSON.stringify(this.entries));
    } catch {
      // ignore storage quota overflow
    }
  }
}
