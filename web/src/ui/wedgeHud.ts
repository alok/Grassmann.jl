// Wedge 2D & 3D Game HUD Overlay
// Driven 100% by Lean's metaJson.wedge (WedgeHudState).
// ZERO game logic, win detection, or scoring computed in JS!

import type { StudioAudioSynth } from '../audio/synth';
import { WedgeActionCode, type WedgeActionCodeValue, type WedgeHudState } from '../gsir/types';
import { WEDGE_LEVELS } from './presets';

export interface WedgeHudCallbacks {
  onAction: (action: WedgeActionCodeValue, arg?: number) => void;
  onTutorial?: (id: 'T1' | 'T2' | 'T3' | 'T4' | 'T5' | 'T6') => void;
  onRandomChallenge?: (dim: 2 | 3, difficulty: 0 | 1 | 2, seed: number) => void;
  onClearSelection: () => void;
}

function formatClock(ms: number): string {
  const totalSec = Math.max(0, Math.floor(ms / 1000));
  const m = Math.floor(totalSec / 60);
  const s = totalSec % 60;
  return `${String(m).padStart(2, '0')}:${String(s).padStart(2, '0')}`;
}

export class WedgeGameHud {
  readonly element: HTMLDivElement;
  private readonly callbacks: WedgeHudCallbacks;
  private readonly synth: StudioAudioSynth;

  private readonly levelSelect: HTMLSelectElement;
  private readonly dimToggleBtn: HTMLButtonElement;
  private readonly titleEl: HTMLDivElement;
  private readonly goalEl: HTMLDivElement;
  private readonly tutorialEl: HTMLDivElement;
  private readonly hintEl: HTMLDivElement;
  private readonly previewBadge: HTMLDivElement;
  private readonly movesEl: HTMLSpanElement;
  private readonly clockEl: HTMLSpanElement;
  private readonly scoreEl: HTMLSpanElement;
  private readonly undoBtn: HTMLButtonElement;
  private readonly solvedBanner: HTMLDivElement;
  private readonly muteBtn: HTMLButtonElement;

  private lastPlayedOp = '';
  private lastPlayedMoves = -1;
  private wasSolved = false;
  private hintShown = false;

  constructor(synth: StudioAudioSynth, callbacks: WedgeHudCallbacks) {
    this.synth = synth;
    this.callbacks = callbacks;

    this.element = document.createElement('div');
    this.element.className = 'gs-wedge-hud hidden';

    // Top HUD Card
    const topCard = document.createElement('div');
    topCard.className = 'gs-wedge-top';

    const row1 = document.createElement('div');
    row1.className = 'gs-wedge-row';

    this.levelSelect = document.createElement('select');
    this.levelSelect.className = 'gs-select gs-wedge-select';
    for (const lv of WEDGE_LEVELS) {
      const opt = document.createElement('option');
      opt.value = String(lv.index);
      opt.textContent = lv.label;
      this.levelSelect.appendChild(opt);
    }
    this.levelSelect.addEventListener('change', () => {
      this.hintShown = false;
      this.callbacks.onClearSelection();
      this.callbacks.onAction(WedgeActionCode.GOTO_LEVEL, Number.parseInt(this.levelSelect.value, 10));
    });

    this.dimToggleBtn = document.createElement('button');
    this.dimToggleBtn.type = 'button';
    this.dimToggleBtn.className = 'gs-btn gs-btn-accent';
    this.dimToggleBtn.textContent = '2D PGA';
    this.dimToggleBtn.addEventListener('click', () => {
      this.callbacks.onClearSelection();
      this.callbacks.onAction(WedgeActionCode.TOGGLE_3D, 0);
    });

    const stats = document.createElement('div');
    stats.className = 'gs-wedge-stats';
    this.movesEl = document.createElement('span');
    this.clockEl = document.createElement('span');
    this.scoreEl = document.createElement('span');
    this.scoreEl.className = 'gs-wedge-score';
    stats.append(this.movesEl, this.clockEl, this.scoreEl);

    this.muteBtn = document.createElement('button');
    this.muteBtn.type = 'button';
    this.muteBtn.className = 'gs-icon-btn';
    this.muteBtn.title = 'Toggle Wedge Audio Synth';
    this.muteBtn.textContent = '🔊';
    this.muteBtn.addEventListener('click', () => {
      const muted = this.synth.toggleMute();
      this.muteBtn.textContent = muted ? '🔇' : '🔊';
    });

    row1.append(this.levelSelect, this.dimToggleBtn, stats, this.muteBtn);

    // Tutorial Cards T1..T6 strip + Random Challenge generator (#72)
    const row2 = document.createElement('div');
    row2.className = 'gs-wedge-extras';

    const tutStrip = document.createElement('div');
    tutStrip.className = 'gs-wedge-tut-strip';
    const tuts: Array<{ id: 'T1' | 'T2' | 'T3' | 'T4' | 'T5' | 'T6'; label: string }> = [
      { id: 'T1', label: 'T1' },
      { id: 'T2', label: 'T2 Join' },
      { id: 'T3', label: 'T3 Meet' },
      { id: 'T4', label: 'T4 Sum' },
      { id: 'T5', label: 'T5 Dot' },
      { id: 'T6', label: 'T6 3D' },
    ];
    for (const t of tuts) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-chip gs-wedge-tut-chip';
      btn.textContent = t.label;
      btn.addEventListener('click', () => {
        this.hintShown = false;
        this.callbacks.onClearSelection();
        this.callbacks.onTutorial?.(t.id);
      });
      tutStrip.appendChild(btn);
    }

    const randWrap = document.createElement('div');
    randWrap.className = 'gs-wedge-rand-wrap';
    const diffSelect = document.createElement('select');
    diffSelect.className = 'gs-select gs-wedge-diff';
    diffSelect.innerHTML =
      '<option value="0">Easy</option><option value="1" selected>Medium</option><option value="2">Hard</option>';

    const randBtn = document.createElement('button');
    randBtn.type = 'button';
    randBtn.className = 'gs-btn gs-btn-accent gs-wedge-rand-btn';
    randBtn.textContent = '🎲 Random';
    let randomCounter = 1;
    randBtn.addEventListener('click', () => {
      this.hintShown = false;
      this.callbacks.onClearSelection();
      const dim: 2 | 3 = this.dimToggleBtn.textContent?.includes('3D') ? 3 : 2;
      const diff = (Number.parseInt(diffSelect.value, 10) || 0) as 0 | 1 | 2;
      const seed = (Date.now() & 0xffff) + randomCounter++;
      this.callbacks.onRandomChallenge?.(dim, diff, seed);
    });
    randWrap.append(diffSelect, randBtn);

    row2.append(tutStrip, randWrap);

    this.titleEl = document.createElement('div');
    this.titleEl.className = 'gs-wedge-title';

    this.goalEl = document.createElement('div');
    this.goalEl.className = 'gs-wedge-goal';

    this.tutorialEl = document.createElement('div');
    this.tutorialEl.className = 'gs-wedge-tutorial hidden';

    this.hintEl = document.createElement('div');
    this.hintEl.className = 'gs-wedge-hint hidden';

    topCard.append(row1, row2, this.titleEl, this.goalEl, this.tutorialEl, this.hintEl);

    // Live Preview Op Pill
    this.previewBadge = document.createElement('div');
    this.previewBadge.className = 'gs-wedge-preview hidden';

    // Solved celebration banner
    this.solvedBanner = document.createElement('div');
    this.solvedBanner.className = 'gs-wedge-solved hidden';
    this.solvedBanner.innerHTML = '<span>✦ Target Reconstructed!</span>';
    const nextSolvedBtn = document.createElement('button');
    nextSolvedBtn.type = 'button';
    nextSolvedBtn.className = 'gs-btn gs-btn-primary';
    nextSolvedBtn.textContent = 'Next Level →';
    nextSolvedBtn.addEventListener('click', () => {
      this.hintShown = false;
      this.callbacks.onAction(WedgeActionCode.NEXT, 0);
    });
    this.solvedBanner.appendChild(nextSolvedBtn);

    // Bottom action dock
    const dock = document.createElement('div');
    dock.className = 'gs-wedge-dock';

    const prevBtn = this.makeDockBtn('← Prev', () => this.callbacks.onAction(WedgeActionCode.PREV, 0));
    this.undoBtn = this.makeDockBtn('↶ Undo', () => this.callbacks.onAction(WedgeActionCode.UNDO, 0));
    const hintBtn = this.makeDockBtn('💡 Hint', () => {
      this.hintShown = true;
      this.callbacks.onAction(WedgeActionCode.HINT, 0);
    });
    const resetBtn = this.makeDockBtn('↺ Reset', () => {
      this.hintShown = false;
      this.callbacks.onClearSelection();
      this.callbacks.onAction(WedgeActionCode.RESET, 0);
    });
    const nextBtn = this.makeDockBtn('Next →', () => {
      this.hintShown = false;
      this.callbacks.onAction(WedgeActionCode.NEXT, 0);
    });

    const guide = document.createElement('span');
    guide.className = 'gs-wedge-gesture-guide';
    guide.textContent = 'Drag 2 white objects: Apart = Join (∨) · Together = Meet (∧) · Hold + Drag = Dot (⌋)';

    dock.append(prevBtn, this.undoBtn, hintBtn, resetBtn, nextBtn, guide);

    this.element.append(topCard, this.previewBadge, this.solvedBanner, dock);
  }

  setVisible(visible: boolean): void {
    this.element.classList.toggle('hidden', !visible);
  }

  update(hud: WedgeHudState | undefined, visible: boolean): void {
    this.setVisible(visible);
    if (!visible) return;

    if (!hud) {
      this.titleEl.textContent = 'Wedge — The Coordinate-Free Geometric Algebra Game';
      this.goalEl.textContent = 'Connect to Lean backend to play L1–L9 (PGA2D) & L10–L16 (PGA3D).';
      this.movesEl.textContent = 'Moves: 0';
      this.clockEl.textContent = '00:00';
      this.scoreEl.textContent = 'Score: 1000';
      this.tutorialEl.classList.add('hidden');
      this.hintEl.classList.add('hidden');
      this.previewBadge.classList.add('hidden');
      this.solvedBanner.classList.add('hidden');
      return;
    }

    this.dimToggleBtn.textContent = hud.is3D ? '3D PGA (Spatial)' : '2D PGA (Planar)';
    const matchedLevel = WEDGE_LEVELS.find(
      (lv) => lv.is3D === hud.is3D && lv.label.includes(`L${hud.level} `)
    );
    if (matchedLevel) {
      this.levelSelect.value = String(matchedLevel.index);
    }
    this.titleEl.textContent = `Level ${hud.level}/${hud.totalLevels} · ${hud.title}`;
    this.goalEl.textContent = hud.goal;
    this.movesEl.textContent = `Moves: ${hud.moves}`;
    this.clockEl.textContent = formatClock(hud.elapsedMs);
    this.scoreEl.textContent = `Score: ${hud.score}`;
    this.undoBtn.disabled = !hud.canUndo;

    if (hud.tutorialText) {
      this.tutorialEl.textContent = hud.tutorialText;
      this.tutorialEl.classList.remove('hidden');
    } else {
      this.tutorialEl.classList.add('hidden');
    }

    if (hud.hintText && (this.hintShown || hud.hintText.length > 0)) {
      this.hintEl.textContent = `Hint: ${hud.hintText}`;
      this.hintEl.classList.remove('hidden');
    } else {
      this.hintEl.classList.add('hidden');
    }

    if (hud.previewOp) {
      this.previewBadge.textContent = `Preview: ${hud.previewOp.toUpperCase()}`;
      this.previewBadge.classList.remove('hidden');
    } else {
      this.previewBadge.classList.add('hidden');
    }

    this.solvedBanner.classList.toggle('hidden', !hud.solved);

    // Trigger subtle Web Audio synth cues strictly driven by Lean's state transitions
    if (hud.solved && !this.wasSolved) {
      this.synth.play('win');
    } else if (hud.lastOp && (hud.moves !== this.lastPlayedMoves || hud.lastOp !== this.lastPlayedOp)) {
      const op = hud.lastOp.toLowerCase();
      if (op === 'join' || op === 'wedge' || op === 'add' || op === 'dot' || op === 'invalid') {
        this.synth.play(op);
      }
    }
    this.wasSolved = hud.solved;
    this.lastPlayedMoves = hud.moves;
    this.lastPlayedOp = hud.lastOp;
  }

  private makeDockBtn(label: string, onClick: () => void): HTMLButtonElement {
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'gs-btn gs-btn-ghost';
    btn.textContent = label;
    btn.addEventListener('click', onClick);
    return btn;
  }
}
