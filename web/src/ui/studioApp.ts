// Master Studio Application Orchestrator
// Coordinates:
// - Pluggable Lean StudioTransport (Native ga-server HTTP/WS | Lean WASM C ABI | Static .gsir snapshot)
// - Stateful GsirSessionDecoder (dirtyHash mesh cache + metaJsonLen=0 delta + opnsShaders cache)
// - GrassmannSceneRenderer (Three.js PBR/Fresnel/OPNS/Line2/Contour PiP/WebXR)
// - 4 Cohesive Studio Modes: CoffeeShop IDE, Wedge 2D/3D, LeanCalculator 3D, GAlculator

import katex from 'katex';
import { StudioAudioSynth } from '../audio/synth';
import {
  GsirSessionDecoder,
  WedgeActionCode,
  buildAllSectionsFixtureBytes,
  encodeDragHandle,
  encodeEditCoeff,
  encodeSetCamera,
  encodeTick,
  encodeWedgeAction,
  encodeWedgeGesture,
  type GsirFrame,
  type JsonInputEvent,
  type WedgeActionCodeValue,
} from '../gsir';
import { GrassmannSceneRenderer } from '../render';
import {
  OrderedStudioEventQueue,
  ServerTransport,
  StaticGsirTransport,
  WasmTransport,
  connectLeanBackend,
  resolveTransportConfigFromEnv,
  type QueuedStudioEvent,
  type StudioTransport,
} from '../transport';
import { CalculatorStudioPanel } from './calculatorPanel';
import { CoffeeShopCodeEditor } from './codeEditor';
import {
  decodeExperimentFromHash,
  encodeExperimentToHash,
  parseGrassmannExperiment,
  serializeExperiment,
  type GrassmannExperimentV1,
} from './experiment';
import { InspectStashPanel } from './inspectPanel';
import { createAboutModal, createConnectionModal } from './modals';
import { KATEX_CHEAT_SHEET, STUDIO_PRESETS, type StudioPreset } from './presets';
import { MyStashPanel } from './stashPanel';
import { WedgeGameHud } from './wedgeHud';

export type StudioMode = 'coffeeshop' | 'wedge' | 'calculator' | 'galculator';
type LeftTab = 'presets' | 'stash' | 'inspect' | 'help';

export class GrassmannStudioApp {
  private readonly root: HTMLElement;
  private readonly decoder = new GsirSessionDecoder();
  private readonly synth = new StudioAudioSynth();
  private transport: StudioTransport | null = null;
  private readonly renderer: GrassmannSceneRenderer;

  private readonly codeEditor: CoffeeShopCodeEditor;
  private readonly inspectPanel: InspectStashPanel;
  private readonly stashPanel: MyStashPanel;
  private readonly wedgeHud: WedgeGameHud;
  private readonly calcPanel: CalculatorStudioPanel;
  private readonly connModal: ReturnType<typeof createConnectionModal>;
  private readonly aboutModal: ReturnType<typeof createAboutModal>;

  // Layout elements
  private readonly leftPane: HTMLElement;
  private readonly leftGutter: HTMLDivElement;
  private readonly rightPane: HTMLElement;
  private readonly rightGutter: HTMLDivElement;
  private readonly statusPill: HTMLButtonElement;
  private readonly telemetryPill: HTMLDivElement;
  private readonly telemetryText: HTMLSpanElement;
  private readonly sparkCanvas: HTMLCanvasElement;
  private readonly sparkCtx: CanvasRenderingContext2D | null;
  private readonly sparkSamples: number[] = [];
  private readonly playBtn: HTMLButtonElement;
  private readonly xrBtn: HTMLButtonElement;
  private readonly updatingPill: HTMLDivElement;
  private readonly offlineBanner: HTMLDivElement;
  private readonly modeButtons = new Map<StudioMode, HTMLButtonElement>();
  private readonly leftTabButtons = new Map<LeftTab, HTMLButtonElement>();
  private readonly leftTabPanes = new Map<LeftTab, HTMLDivElement>();
  private readonly algebraSelect: HTMLSelectElement;

  // State
  private mode: StudioMode = 'coffeeshop';
  private activeAlgebra = 'PGA3';
  private activePresetId = 'pga3d_slicing';
  private darkTheme = true;
  private gridVisible = true;
  private wireframe = false;
  private animRunning = false;
  private animTimeSec = 0;
  private lastAnimTickMs = 0;
  private animRafId = 0;
  private lastLeanUs = 0;
  private lastDecodeUs = 0;
  private lastP95Ms = 0;
  private lastDroppedFrames = 0;
  private lastWedgeSeed = 42;
  private lastFrame: GsirFrame | null = null;
  private dispatchedEventLog: string[] = [];
  private livePresets: StudioPreset[] = [...STUDIO_PRESETS];
  private rebuildPresetBrowser: (() => void) | null = null;

  // Unified ordered event pump (coalesces continuous drag/tick/camera, preserves all discrete actions)
  private readonly eventQueue: OrderedStudioEventQueue;
  private updatingDelayTimer: ReturnType<typeof setTimeout> | null = null;

  constructor(root: HTMLElement) {
    this.root = root;
    this.root.className = 'gs-app';
    this.root.dataset.theme = 'dark';

    const envCfg = resolveTransportConfigFromEnv();

    // =========================================================================
    // 1. Top Studio Header Bar
    // =========================================================================
    const topBar = document.createElement('header');
    topBar.className = 'gs-topbar';

    const brand = document.createElement('div');
    brand.className = 'gs-brand';
    brand.innerHTML =
      '<span class="gs-brand-mark">⋀</span>' +
      '<span class="gs-brand-name">Grassmann Studio</span>' +
      '<span class="gs-brand-tag">Lean 4 · GSIR v1</span>';

    // 4 Cohesive Mode Switcher
    const modeNav = document.createElement('nav');
    modeNav.className = 'gs-mode-nav';
    const modeDefs: Array<{ id: StudioMode; label: string }> = [
      { id: 'coffeeshop', label: 'CoffeeShop IDE' },
      { id: 'wedge', label: 'Wedge 2D/3D' },
      { id: 'calculator', label: 'LeanCalculator 3D' },
      { id: 'galculator', label: 'GAlculator' },
    ];
    for (const m of modeDefs) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-mode-btn';
      btn.textContent = m.label;
      btn.addEventListener('click', () => this.setMode(m.id));
      modeNav.appendChild(btn);
      this.modeButtons.set(m.id, btn);
    }

    // Right status & utility controls
    const topRight = document.createElement('div');
    topRight.className = 'gs-topbar-right';

    this.telemetryPill = document.createElement('div');
    this.telemetryPill.className = 'gs-telemetry-pill mono';
    this.sparkCanvas = document.createElement('canvas');
    this.sparkCanvas.className = 'gs-sparkline';
    this.sparkCanvas.width = 52;
    this.sparkCanvas.height = 16;
    this.sparkCtx = this.sparkCanvas.getContext('2d');
    this.telemetryText = document.createElement('span');
    this.telemetryText.textContent = '60 FPS · 0 µs';
    this.telemetryPill.append(this.sparkCanvas, this.telemetryText);

    this.statusPill = document.createElement('button');
    this.statusPill.type = 'button';
    this.statusPill.className = 'gs-status-pill connecting';
    this.statusPill.textContent = 'Connecting Lean…';
    this.statusPill.addEventListener('click', () => this.connModal.open());

    this.xrBtn = document.createElement('button');
    this.xrBtn.type = 'button';
    this.xrBtn.className = 'gs-btn gs-btn-accent hidden';
    this.xrBtn.textContent = 'Enter XR';
    this.xrBtn.addEventListener('click', () => {
      void this.renderer.xr.toggleSession().then((active) => {
        this.xrBtn.textContent = active ? 'Exit XR' : 'Enter XR';
      });
    });

    const themeBtn = document.createElement('button');
    themeBtn.type = 'button';
    themeBtn.className = 'gs-icon-btn gs-theme-btn';
    themeBtn.title = 'Toggle Obsidian / Gallery Daylight Theme';
    themeBtn.textContent = '◐';
    themeBtn.addEventListener('click', () => {
      this.darkTheme = !this.darkTheme;
      this.root.dataset.theme = this.darkTheme ? 'dark' : 'light';
      this.renderer.setThemeOverride(this.darkTheme);
    });

    const aboutBtn = document.createElement('button');
    aboutBtn.type = 'button';
    aboutBtn.className = 'gs-icon-btn';
    aboutBtn.title = 'About & Credits';
    aboutBtn.textContent = '?';
    aboutBtn.addEventListener('click', () => this.aboutModal.open());

    topRight.append(this.telemetryPill, this.statusPill, this.xrBtn, themeBtn, aboutBtn);
    topBar.append(brand, modeNav, topRight);

    // =========================================================================
    // 2. Main 3-Pane Resizable Workspace
    // =========================================================================
    const workspace = document.createElement('main');
    workspace.className = 'gs-workspace';

    // Left Sidebar
    this.leftPane = document.createElement('aside');
    this.leftPane.className = 'gs-pane gs-left-pane';
    this.leftPane.style.width = '310px';

    const leftTabsBar = document.createElement('div');
    leftTabsBar.className = 'gs-left-tabs';
    const lTabs: Array<{ id: LeftTab; label: string }> = [
      { id: 'presets', label: 'Presets' },
      { id: 'stash', label: 'My Stash' },
      { id: 'inspect', label: 'Inspect' },
      { id: 'help', label: '?' },
    ];
    for (const t of lTabs) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'gs-left-tab-btn';
      btn.textContent = t.label;
      btn.addEventListener('click', () => this.selectLeftTab(t.id));
      leftTabsBar.appendChild(btn);
      this.leftTabButtons.set(t.id, btn);
    }

    const leftBody = document.createElement('div');
    leftBody.className = 'gs-left-body';

    // Tab 1: Presets & Algebras
    this.algebraSelect = document.createElement('select');
    const presetsPane = this.buildPresetsPane();

    // Tab 2: My Stash
    const stashPane = document.createElement('div');
    stashPane.className = 'gs-left-pane-content hidden';
    this.stashPanel = new MyStashPanel({
      getCurrentSketch: () => ({
        title: this.lastFrame?.meta?.title ?? this.activePresetId,
        algebra: this.activeAlgebra,
        code: this.codeEditor.getCode(),
        thumbnail: this.renderer.exportPng(360, 220),
      }),
      onLoadSketch: (entry) => {
        this.activeAlgebra = entry.algebra;
        this.algebraSelect.value = entry.algebra;
        this.codeEditor.setCode(entry.code);
        void this.dispatchJson({ op: 'evalScript', algebra: entry.algebra, code: entry.code });
      },
      onExportPng: (w, h) => this.downloadDataUrl(this.renderer.exportPng(w, h), `grassmann-${Date.now()}.png`),
      onExportSvg: (w, h) => {
        const svg = this.renderer.exportSvg(w, h);
        const blob = new Blob([svg], { type: 'image/svg+xml' });
        this.downloadDataUrl(URL.createObjectURL(blob), `grassmann-${Date.now()}.svg`);
      },
      onExportExperiment: () => {
        const json = serializeExperiment(this.buildExperimentSnapshot());
        const blob = new Blob([json], { type: 'application/json' });
        this.downloadDataUrl(URL.createObjectURL(blob), `${this.activePresetId || 'experiment'}.grassmann.json`);
      },
      onCopyExperimentJson: () => serializeExperiment(this.buildExperimentSnapshot()),
      onLoadExperimentJson: (json) => {
        const parsed = parseGrassmannExperiment(json);
        if (parsed) {
          void this.applyExperiment(parsed);
        } else {
          this.codeEditor.setDiagnostics([{ severity: 'error', message: 'Invalid .grassmann.json experiment file' }]);
        }
      },
      onShareUrl: () => this.buildShareUrl(),
      onLoadGsirFile: (bytes, name) => this.loadStaticGsirBytes(bytes, name),
      onLoadScriptFile: (code) => {
        this.codeEditor.setCode(code);
        void this.dispatchJson({ op: 'evalScript', algebra: this.activeAlgebra, code });
      },
    });
    stashPane.appendChild(this.stashPanel.element);

    // Tab 3: Inspect Stash
    const inspectPane = document.createElement('div');
    inspectPane.className = 'gs-left-pane-content hidden';
    this.inspectPanel = new InspectStashPanel({
      onEditCoeff: (entryIdx, bladeIdx, val) => {
        this.enqueueBinaryEvent(encodeEditCoeff(entryIdx, bladeIdx, val));
      },
    });
    inspectPane.appendChild(this.inspectPanel.element);

    // Tab 4: ? KaTeX Cheat Sheet
    const helpPane = this.buildHelpPane();

    this.leftTabPanes.set('presets', presetsPane);
    this.leftTabPanes.set('stash', stashPane);
    this.leftTabPanes.set('inspect', inspectPane);
    this.leftTabPanes.set('help', helpPane);

    leftBody.append(presetsPane, stashPane, inspectPane, helpPane);
    this.leftPane.append(leftTabsBar, leftBody);

    // Left Draggable Gutter (double-click collapses)
    this.leftGutter = this.createSplitGutter('left', this.leftPane, 220, 480, 310);

    // Center 3D Viewport
    const viewportWrap = document.createElement('section');
    viewportWrap.className = 'gs-viewport-wrap';

    const canvasHost = document.createElement('div');
    canvasHost.className = 'gs-canvas-host';
    viewportWrap.appendChild(canvasHost);

    // Floating Viewport Quick Toolbar (top-right inside viewport)
    const vpTools = document.createElement('div');
    vpTools.className = 'gs-vp-toolbar';
    this.playBtn = this.makeVpBtn('▶ Play', () => this.setAnimationRunning(!this.animRunning));
    vpTools.append(
      this.playBtn,
      this.makeVpBtn('Grid', () => {
        this.gridVisible = !this.gridVisible;
        this.renderer.setGridVisible(this.gridVisible);
      }),
      this.makeVpBtn('Wire', () => {
        this.wireframe = !this.wireframe;
        this.renderer.setWireframeOverride(this.wireframe);
        if (this.lastFrame) this.renderer.applyFrame(this.lastFrame, this.decoder);
      }),
      this.makeVpBtn('Reset (R)', () => this.renderer.resetCamera()),
      this.makeVpBtn('PNG', () =>
        this.downloadDataUrl(this.renderer.exportPng(1600, 1000), `grassmann-${Date.now()}.png`)
      ),
      this.makeVpBtn('SVG', () => {
        const svg = this.renderer.exportSvg(1200, 800);
        const blob = new Blob([svg], { type: 'image/svg+xml' });
        this.downloadDataUrl(URL.createObjectURL(blob), `grassmann-${Date.now()}.svg`);
      })
    );
    viewportWrap.appendChild(vpTools);

    // Subtle non-blocking Updating… pill for heavy Lean 3D remeshes (keeps last accepted mesh visible)
    this.updatingPill = document.createElement('div');
    this.updatingPill.className = 'gs-updating-pill hidden';
    this.updatingPill.innerHTML = '<span class="gs-spinner"></span><span>Updating in Lean 4…</span>';
    viewportWrap.appendChild(this.updatingPill);

    // Offline / Connect Banner inside viewport
    this.offlineBanner = document.createElement('div');
    this.offlineBanner.className = 'gs-offline-banner hidden';
    const offText = document.createElement('span');
    offText.innerHTML =
      '<strong>Lean 4 backend not connected.</strong> Start <code>lake exe ga-server</code> (<code>:8787</code>), load <code>grassmann.wasm</code>, or inspect a static GSIR binary fixture.';
    const offConnBtn = document.createElement('button');
    offConnBtn.type = 'button';
    offConnBtn.className = 'gs-btn gs-btn-primary';
    offConnBtn.textContent = 'Connect / Options';
    offConnBtn.addEventListener('click', () => this.connModal.open());
    const offFixBtn = document.createElement('button');
    offFixBtn.type = 'button';
    offFixBtn.className = 'gs-btn gs-btn-ghost';
    offFixBtn.textContent = 'Inspect Static GSIR Fixture';
    offFixBtn.addEventListener('click', () => {
      this.loadStaticGsirBytes(buildAllSectionsFixtureBytes(), 'All-Sections Static GSIR Fixture');
    });
    this.offlineBanner.append(offText, offConnBtn, offFixBtn);
    viewportWrap.appendChild(this.offlineBanner);

    // Wedge 2D/3D Game HUD overlay inside viewport
    this.wedgeHud = new WedgeGameHud(this.synth, {
      onAction: (action: WedgeActionCodeValue, arg = 0) => {
        this.enqueueBinaryEvent(encodeWedgeAction(action, arg));
      },
      onTutorial: (id) => {
        void this.dispatchJson({ op: 'wedgeTutorial', id, forceFullSnapshot: true });
      },
      onRandomChallenge: (dim, difficulty, seed) => {
        this.lastWedgeSeed = seed;
        void this.dispatchJson({ op: 'wedgeRandom', dim, difficulty, seed, forceFullSnapshot: true });
      },
      onClearSelection: () => this.renderer.clearWedgeSelection(),
    });
    viewportWrap.appendChild(this.wedgeHud.element);

    // Right Pane (hosts Code Editor in CoffeeShop mode OR Calculator/GAlculator in Calc modes)
    this.rightPane = document.createElement('aside');
    this.rightPane.className = 'gs-pane gs-right-pane';
    this.rightPane.style.width = '380px';

    this.codeEditor = new CoffeeShopCodeEditor({
      onRun: (code) => {
        void this.dispatchJson({ op: 'evalScript', algebra: this.activeAlgebra, code });
      },
    });
    this.codeEditor.setCode(STUDIO_PRESETS[0]!.defaultCode);

    this.calcPanel = new CalculatorStudioPanel({
      onDispatchJson: (ev) => void this.dispatchJson(ev),
      onToggleAnim: (running) => this.setAnimationRunning(running),
    });
    this.calcPanel.element.classList.add('hidden');

    this.rightPane.append(this.codeEditor.element, this.calcPanel.element);

    // Right Draggable Gutter
    this.rightGutter = this.createSplitGutter('right', this.rightPane, 260, 620, 380);

    workspace.append(this.leftPane, this.leftGutter, viewportWrap, this.rightGutter, this.rightPane);

    // =========================================================================
    // 3. Attribution Footer Bar
    // =========================================================================
    const footer = document.createElement('footer');
    footer.className = 'gs-footer';
    footer.innerHTML =
      '<div class="gs-footer-left"><span>Pure Lean 4 GSIR v1 Engine</span><span class="sep">·</span><span>Zero JS GA Math</span></div>' +
      '<div class="gs-footer-credits">Credits: <strong>Michael Reed</strong> (<code>chakravala</code> / Grassmann.jl) &amp; <strong>Steven De Keninck</strong> (<code>enkimute</code> / ganja.js)</div>';

    // Modals
    this.connModal = createConnectionModal(
      envCfg.serverUrl ?? 'http://127.0.0.1:8787',
      envCfg.wasmUrl ?? './grassmann.wasm',
      {
        onConnectServer: (url) => void this.connectTransport(new ServerTransport({ baseUrl: url })),
        onConnectWasm: (url) => void this.connectTransport(new WasmTransport({ wasmUrl: url })),
        onInspectStaticFixture: () =>
          this.loadStaticGsirBytes(buildAllSectionsFixtureBytes(), 'All-Sections Static GSIR Fixture'),
      }
    );
    this.aboutModal = createAboutModal();

    this.root.append(topBar, workspace, footer, this.connModal.element, this.aboutModal.element);

    // Unified ordered event pump (binary + JSON)
    this.eventQueue = new OrderedStudioEventQueue({
      execute: (item) => this.executeQueuedEvent(item),
      onBusyChange: (busy, _pending, isHeavy) => {
        if (busy && isHeavy) {
          if (!this.updatingDelayTimer) {
            this.updatingDelayTimer = setTimeout(() => {
              this.updatingPill.classList.remove('hidden');
            }, 45);
          }
        } else if (!busy) {
          if (this.updatingDelayTimer) {
            clearTimeout(this.updatingDelayTimer);
            this.updatingDelayTimer = null;
          }
          this.updatingPill.classList.add('hidden');
        }
      },
      onError: (err, item) => {
        const msg = (err as Error).message || 'Lean dispatch error';
        if (item.kind === 'json') {
          this.calcPanel.setInlineError(msg);
          this.codeEditor.setDiagnostics([{ severity: 'error', message: msg }]);
        } else {
          this.setStatus('error', `Dispatch err: ${msg}`);
        }
      },
    });

    // Global drag-and-drop for portable .grassmann.json / .gsir files anywhere on the Studio
    this.root.addEventListener('dragover', (ev) => {
      if (ev.dataTransfer?.types.includes('Files')) ev.preventDefault();
    });
    this.root.addEventListener('drop', (ev) => {
      const file = ev.dataTransfer?.files?.[0];
      if (!file) return;
      if (file.name.endsWith('.grassmann.json') || file.name.endsWith('.json')) {
        ev.preventDefault();
        void file.text().then((txt) => {
          const parsed = parseGrassmannExperiment(txt);
          if (parsed) void this.applyExperiment(parsed);
        });
      } else if (file.name.endsWith('.gsir')) {
        ev.preventDefault();
        void file.arrayBuffer().then((ab) => this.loadStaticGsirBytes(new Uint8Array(ab), file.name));
      }
    });

    // =========================================================================
    // 4. Initialize Three.js Scene Renderer
    // =========================================================================
    this.renderer = new GrassmannSceneRenderer(canvasHost, {
      onDragHandle: (handleId, pos) => {
        this.enqueueBinaryEvent(encodeDragHandle(handleId, pos[0], pos[1], pos[2]));
      },
      onSelectObject: ({ handleId, label }) => {
        if (this.mode !== 'wedge' && this.inspectPanel.selectByHandleOrLabel(handleId, label)) {
          this.selectLeftTab('inspect');
        }
      },
      onWedgeGesture: (idA, idB, dirA, dirB, isPreview) => {
        this.enqueueBinaryEvent(encodeWedgeGesture(idA, idB, dirA, dirB, isPreview));
      },
      onWedgeSelectSound: () => this.synth.play('select'),
      onCameraChange: (motor, fovDeg, distance) => {
        if (this.transport && this.transport.kind !== 'fixture') {
          this.enqueueBinaryEvent(encodeSetCamera(motor, fovDeg, distance));
        }
      },
      onTelemetry: ({ fps, renderUs, p95InputToPresentMs, droppedFrames, cachedMeshes }) => {
        this.lastP95Ms = p95InputToPresentMs;
        this.lastDroppedFrames = droppedFrames;
        this.telemetryText.textContent = `${fps} FPS · p95 ${p95InputToPresentMs.toFixed(1)}ms · ${droppedFrames} drop · ${cachedMeshes}m`;
        this.pushSparkSample(Math.max(p95InputToPresentMs, (renderUs + this.lastDecodeUs) / 1000));
      },
    });

    // Global keyboard shortcuts (1/2/3/4 modes, Space play/pause, R reset camera, Cmd/Ctrl+Z undo, H hint, Shift+Enter eval)
    window.addEventListener('keydown', this.onGlobalKeyDown);

    // Expose read-only diagnostics handle for Playwright E2E visual & interaction audits
    (window as unknown as Record<string, unknown>).__grassmannStudio = {
      getState: () => ({
        mode: this.mode,
        theme: this.darkTheme ? 'dark' : 'light',
        transportKind: this.transport?.kind ?? null,
        transportLabel: this.transport?.label ?? null,
        lastLeanUs: this.lastLeanUs,
        lastDecodeUs: this.lastDecodeUs,
        p95InputToPresentMs: this.lastP95Ms,
        droppedFrames: this.lastDroppedFrames,
        frameSeq: this.lastFrame ? this.lastFrame.header.frameSeq.toString() : null,
        presetId: this.lastFrame?.meta?.presetId ?? this.activePresetId,
        title: this.lastFrame?.meta?.title ?? null,
        cachedMeshes: this.decoder.getCachedMeshCount(),
        presetCount: this.livePresets.length,
        opnsCount: this.lastFrame?.opnsUniforms.length ?? 0,
        wedge: this.lastFrame?.meta?.wedge ?? null,
        calc: this.lastFrame?.meta?.calc ?? null,
        points: this.lastFrame?.points.map((p) => ({
          handleId: p.handleId,
          draggable: p.draggable,
          pos: p.pos,
        })) ?? [],
        inspect: this.lastFrame?.meta?.inspect ?? [],
        recentEvents: this.dispatchedEventLog.slice(-12),
      }),
      getHandleScreenPos: (handleId?: number) => this.renderer.getInteractiveHandleScreenPos(handleId),
      exportExperiment: () => this.buildExperimentSnapshot(),
      importExperiment: (exp: GrassmannExperimentV1) => this.applyExperiment(exp),
    };

    // Probe WebXR support (Vision Pro / Quest)
    void this.renderer.xr.detectSupport().then((mode) => {
      if (mode) {
        this.xrBtn.textContent = mode === 'immersive-ar' ? 'Enter AR' : 'Enter VR';
        this.xrBtn.classList.remove('hidden');
      }
    });

    this.selectLeftTab('presets');
    this.setMode('coffeeshop', false);

    // Auto-connect to Lean backend (native ga-server / compiled grassmann.wasm)
    void this.autoConnect(envCfg);
  }

  private async autoConnect(cfg: ReturnType<typeof resolveTransportConfigFromEnv>): Promise<void> {
    this.setStatus('connecting', 'Connecting Lean…');
    try {
      const { transport, initialFrame } = await connectLeanBackend(cfg);
      // Measure warm per-frame Lean call separately from one-time WASM download/compile
      const tWarm = performance.now();
      await transport.getFrame();
      this.lastLeanUs = (performance.now() - tWarm) * 1000;
      this.transport?.dispose();
      this.transport = transport;
      this.decoder.reset();
      this.offlineBanner.classList.add('hidden');
      this.updateEngineBadge();
      this.ingestRawFrame(initialFrame, true);
      await this.syncPresetCatalogFromLean(transport);
      this.applyUrlHashOnConnect();
    } catch (err) {
      this.setStatus('error', 'Lean Offline · Connect');
      this.offlineBanner.classList.remove('hidden');
      console.info('[Grassmann Studio] No live Lean backend detected:', (err as Error).message);
    }
  }

  private async connectTransport(next: StudioTransport): Promise<void> {
    this.setStatus('connecting', `Connecting ${next.label}…`);
    try {
      const t0 = performance.now();
      const bytes = await next.connect();
      this.lastLeanUs = (performance.now() - t0) * 1000;
      this.transport?.dispose();
      this.transport = next;
      this.decoder.reset();
      this.offlineBanner.classList.add('hidden');
      this.updateEngineBadge();
      this.ingestRawFrame(bytes, true);
      await this.syncPresetCatalogFromLean(next);
    } catch (err) {
      next.dispose();
      this.setStatus('error', 'Connection Failed');
      this.connModal.open((err as Error).message);
    }
  }

  private async syncPresetCatalogFromLean(transport: StudioTransport): Promise<void> {
    if (!transport.getPresetCatalog) return;
    try {
      const items = await transport.getPresetCatalog();
      if (items.length === 0) return;
      this.livePresets = items.map((it) => ({
        id: it.id,
        title: it.title,
        category: it.category || it.algebra || 'General',
        algebra: it.algebra || 'PGA3',
        signature: it.signature ?? it.algebra ?? 'Cl(p,q,r)',
        badge: it.badge,
        description: it.description || '',
        defaultCode: it.sampleCode ?? `// ${it.title}\npreset ${it.id}`,
      }));
      // Sync editor sample code for active preset so Shift+Enter always runs valid Lean GA script!
      const active = this.livePresets.find((p) => p.id === this.activePresetId) ?? this.livePresets[0];
      if (active) {
        this.activePresetId = active.id;
        this.activeAlgebra = active.algebra;
        this.codeEditor.setCode(active.defaultCode);
      }
      this.rebuildPresetBrowser?.();
    } catch {
      // Keep fallback presets if catalog endpoint not supported
    }
  }

  private updateEngineBadge(): void {
    if (!this.transport) return;
    const ms = Math.max(0.01, this.lastLeanUs / 1000).toFixed(2);
    if (this.transport.kind === 'wasm') {
      this.setStatus('connected', `Lean 4.36 WASM • ${ms}ms`);
    } else if (this.transport.kind === 'server') {
      this.setStatus('connected', `Lean Native Server • ${ms}ms`);
    } else {
      this.setStatus('connected', `Static GSIR • ${ms}ms`);
    }
  }

  private loadStaticGsirBytes(bytes: Uint8Array, label: string): void {
    const tr = new StaticGsirTransport(bytes, label);
    this.transport?.dispose();
    this.transport = tr;
    this.decoder.reset();
    this.offlineBanner.classList.add('hidden');
    this.setStatus('connected', `Snapshot · ${label}`);
    this.ingestRawFrame(bytes, true);
  }

  private setMode(next: StudioMode, notifyLean = true): void {
    this.mode = next;
    for (const [id, btn] of this.modeButtons) {
      btn.classList.toggle('active', id === next);
    }

    const showLeft = next === 'coffeeshop' || next === 'calculator';
    const showRight = next !== 'wedge';

    this.leftPane.classList.toggle('hidden', !showLeft);
    this.leftGutter.classList.toggle('hidden', !showLeft);
    this.rightPane.classList.toggle('hidden', !showRight);
    this.rightGutter.classList.toggle('hidden', !showRight);

    this.codeEditor.element.classList.toggle('hidden', next !== 'coffeeshop');
    this.calcPanel.element.classList.toggle('hidden', next !== 'calculator' && next !== 'galculator');

    if (next === 'galculator') {
      this.calcPanel.selectSubTab('galc');
    } else if (next === 'calculator') {
      this.calcPanel.selectSubTab('sta');
    }

    this.wedgeHud.update(this.lastFrame?.meta?.wedge, next === 'wedge');

    if (notifyLean && this.transport && this.transport.kind !== 'fixture') {
      if (next === 'wedge') {
        void this.dispatchJson({ op: 'loadPreset', id: 'game_wedge', forceFullSnapshot: true });
      } else if (next === 'calculator') {
        void this.dispatchJson({ op: 'loadPreset', id: 'sta_lorentz_boost', forceFullSnapshot: true });
      }
    }
  }

  private selectLeftTab(tab: LeftTab): void {
    for (const [id, btn] of this.leftTabButtons) {
      btn.classList.toggle('active', id === tab);
    }
    for (const [id, pane] of this.leftTabPanes) {
      pane.classList.toggle('hidden', id !== tab);
    }
  }

  private buildPresetsPane(): HTMLDivElement {
    const pane = document.createElement('div');
    pane.className = 'gs-left-pane-content';

    // Algebra selector pill
    const algRow = document.createElement('div');
    algRow.className = 'gs-algebra-bar';
    const algLabel = document.createElement('label');
    algLabel.textContent = 'Algebra';
    this.algebraSelect.className = 'gs-select';
    for (const alg of ['PGA3', 'PGA2', 'CGA3', 'CGA2', 'STA', 'R3', 'Complex', 'Dual', 'Quaternion']) {
      const opt = document.createElement('option');
      opt.value = alg;
      opt.textContent = alg === 'STA' ? 'STA Cl(3,1) −+++' : alg;
      this.algebraSelect.appendChild(opt);
    }
    this.algebraSelect.value = this.activeAlgebra;
    this.algebraSelect.addEventListener('change', () => {
      this.activeAlgebra = this.algebraSelect.value;
    });
    algRow.append(algLabel, this.algebraSelect);

    // Search input + count badge
    const searchRow = document.createElement('div');
    searchRow.className = 'gs-row-gap';
    const search = document.createElement('input');
    search.type = 'search';
    search.className = 'gs-input';
    search.placeholder = 'Filter presets (slicing, gyroid, CGA, STA)...';
    const countBadge = document.createElement('span');
    countBadge.className = 'gs-preset-count mono';
    searchRow.append(search, countBadge);

    // Horizontally scrollable category filter carousel (dynamically synced with Lean preset catalog!)
    let selectedCat = 'All';
    const catBar = document.createElement('div');
    catBar.className = 'gs-cat-carousel';

    const listEl = document.createElement('div');
    listEl.className = 'gs-preset-list';

    const renderList = (query: string) => {
      const q = query.trim().toLowerCase();
      listEl.innerHTML = '';

      let matchedCount = 0;
      const grouped = new Map<string, StudioPreset[]>();
      for (const p of this.livePresets) {
        if (selectedCat !== 'All' && p.category !== selectedCat) continue;
        if (
          q &&
          !p.title.toLowerCase().includes(q) &&
          !p.id.toLowerCase().includes(q) &&
          !p.algebra.toLowerCase().includes(q) &&
          !p.category.toLowerCase().includes(q) &&
          !p.description.toLowerCase().includes(q)
        ) {
          continue;
        }
        matchedCount++;
        const arr = grouped.get(p.category) ?? [];
        arr.push(p);
        grouped.set(p.category, arr);
      }

      countBadge.textContent = `${matchedCount}`;

      for (const [cat, items] of grouped) {
        const catHead = document.createElement('div');
        catHead.className = 'gs-preset-category';
        catHead.textContent = cat;
        listEl.appendChild(catHead);

        for (const p of items) {
          const card = document.createElement('button');
          card.type = 'button';
          card.dataset.presetId = p.id;
          card.className = `gs-preset-card${p.id === this.activePresetId ? ' active' : ''}`;
          card.innerHTML =
            `<div class="gs-preset-card-head">` +
            `<span class="gs-preset-title">${p.title}</span>` +
            `<span class="gs-preset-sig">${p.badge ? `<em>${p.badge}</em> · ` : ''}${p.signature}</span>` +
            `</div>` +
            `<div class="gs-preset-desc">${p.description}</div>`;
          card.addEventListener('click', () => {
            this.loadPreset(p);
            renderList(search.value);
          });
          listEl.appendChild(card);
        }
      }
    };

    const rebuildCategories = () => {
      const categories = ['All', ...Array.from(new Set(this.livePresets.map((p) => p.category)))];
      if (!categories.includes(selectedCat)) selectedCat = 'All';
      catBar.innerHTML = '';
      for (const cat of categories) {
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = `gs-cat-pill${cat === selectedCat ? ' active' : ''}`;
        btn.textContent = cat === 'Implicit & Parametric 3D' ? 'Implicit 3D' : cat;
        btn.addEventListener('click', () => {
          selectedCat = cat;
          rebuildCategories();
          renderList(search.value);
        });
        catBar.appendChild(btn);
      }
      renderList(search.value);
    };

    this.rebuildPresetBrowser = rebuildCategories;
    search.addEventListener('input', () => renderList(search.value));
    rebuildCategories();

    pane.append(algRow, searchRow, catBar, listEl);
    return pane;
  }

  private buildHelpPane(): HTMLDivElement {
    const pane = document.createElement('div');
    pane.className = 'gs-left-pane-content hidden';

    const title = document.createElement('div');
    title.className = 'gs-section-mini-title';
    title.textContent = 'GA Operator & Notation Reference';
    pane.appendChild(title);

    for (const item of KATEX_CHEAT_SHEET) {
      const row = document.createElement('div');
      row.className = 'gs-help-row';
      const mathEl = document.createElement('div');
      mathEl.className = 'gs-help-math';
      try {
        mathEl.innerHTML = katex.renderToString(item.latex, { throwOnError: false });
      } catch {
        mathEl.textContent = item.latex;
      }
      const meta = document.createElement('div');
      meta.className = 'gs-help-meta';
      meta.innerHTML = `<code class="mono">${item.syntax}</code><span>${item.meaning}</span>`;
      row.append(mathEl, meta);
      pane.appendChild(row);
    }

    const keys = document.createElement('div');
    keys.className = 'gs-help-shortcuts';
    keys.innerHTML =
      '<strong>Studio Shortcuts</strong>' +
      '<div><kbd>1</kbd><kbd>2</kbd><kbd>3</kbd><kbd>4</kbd> Switch studio modes</div>' +
      '<div><kbd>Space</kbd> Play / Pause simulation clock</div>' +
      '<div><kbd>R</kbd> Smooth reset camera</div>' +
      '<div><kbd>⌘/Ctrl Z</kbd> / <kbd>H</kbd> Wedge Undo / Hint</div>' +
      '<div><kbd>⇧ Enter</kbd> Evaluate script in Lean</div>' +
      '<div><kbd>Select Number</kbd> Inline drag-to-scrub slider</div>' +
      '<div><kbd>Select 0xRRGGBB</kbd> Inline hex color picker</div>';
    pane.appendChild(keys);

    return pane;
  }

  private loadPreset(preset: StudioPreset): void {
    this.activePresetId = preset.id;
    this.activeAlgebra = preset.algebra;
    this.algebraSelect.value = preset.algebra;
    this.codeEditor.setCode(preset.defaultCode);
    if (typeof window !== 'undefined') {
      window.history.replaceState(null, '', `#${preset.id}`);
    }
    void this.dispatchJson({ op: 'loadPreset', id: preset.id, forceFullSnapshot: true });
  }

  private applyUrlHashOnConnect(): void {
    if (typeof window === 'undefined' || !window.location.hash) return;
    const raw = window.location.hash.slice(1).trim();
    if (!raw) return;

    if (raw.includes('=')) {
      const params = new URLSearchParams(raw);
      const expParam = params.get('exp');
      if (expParam) {
        const exp = decodeExperimentFromHash(expParam);
        if (exp) {
          void this.applyExperiment(exp);
          return;
        }
      }
      const presetId = params.get('preset');
      const code = params.get('code');
      const alg = params.get('alg');
      if (presetId) {
        const found = this.livePresets.find((p) => p.id === presetId);
        if (found) this.loadPreset(found);
        else void this.dispatchJson({ op: 'loadPreset', id: presetId, forceFullSnapshot: true });
      } else if (code) {
        if (alg) {
          this.activeAlgebra = alg;
          this.algebraSelect.value = alg;
        }
        this.codeEditor.setCode(code);
        void this.dispatchJson({ op: 'evalScript', algebra: this.activeAlgebra, code });
      }
      return;
    }

    // Direct CoffeeShop bookmark hash like #pga3d_slicing
    const cleanId = raw.split('&')[0]!;
    if (cleanId === 'game_wedge') {
      this.setMode('wedge', true);
      return;
    }
    const preset = this.livePresets.find((p) => p.id === cleanId);
    if (preset) {
      this.loadPreset(preset);
    } else {
      void this.dispatchJson({ op: 'loadPreset', id: cleanId, forceFullSnapshot: true });
    }
  }

  private buildShareUrl(): string {
    const hash = encodeExperimentToHash(this.buildExperimentSnapshot());
    const url = `${window.location.origin}${window.location.pathname}#${hash}`;
    window.history.replaceState(null, '', `#${hash}`);
    return url;
  }

  private buildExperimentSnapshot(): GrassmannExperimentV1 {
    const handles = (this.lastFrame?.points ?? [])
      .filter((p) => p.draggable)
      .map((p) => ({
        handleId: p.handleId,
        pos: [p.pos[0], p.pos[1], p.pos[2]] as [number, number, number],
      }));
    const cam = this.renderer.getCameraState();
    return {
      version: 1,
      mode: this.mode,
      presetId: this.lastFrame?.meta?.presetId ?? this.activePresetId,
      algebra: this.activeAlgebra,
      script: this.codeEditor.getCode(),
      implicitExpr: this.calcPanel.getImplicitExpr(),
      parametricExpr: this.calcPanel.getParametricExpr(),
      handles,
      wedgeLevel: this.lastFrame?.meta?.wedge?.level ?? 1,
      wedgeSeed: this.lastWedgeSeed,
      camera: {
        pos: [cam.pos[0], cam.pos[1], cam.pos[2]],
        target: [cam.target[0], cam.target[1], cam.target[2]],
        isOrtho: cam.isOrtho,
      },
    };
  }

  private async applyExperiment(exp: GrassmannExperimentV1): Promise<void> {
    this.activePresetId = exp.presetId;
    this.activeAlgebra = exp.algebra;
    this.algebraSelect.value = exp.algebra;
    this.lastWedgeSeed = exp.wedgeSeed;
    this.codeEditor.setCode(exp.script);
    this.calcPanel.setImplicitExpr(exp.implicitExpr);
    this.calcPanel.setParametricExpr(exp.parametricExpr);
    this.setMode(exp.mode, false);

    if (exp.mode === 'wedge') {
      this.enqueueBinaryEvent(encodeWedgeAction(WedgeActionCode.GOTO_LEVEL, exp.wedgeLevel));
    } else if (exp.presetId) {
      await this.dispatchJson({ op: 'loadPreset', id: exp.presetId, forceFullSnapshot: true });
    } else if (exp.script.trim()) {
      await this.dispatchJson({ op: 'evalScript', algebra: exp.algebra, code: exp.script });
    }

    for (const h of exp.handles) {
      this.enqueueBinaryEvent(encodeDragHandle(h.handleId, h.pos[0], h.pos[1], h.pos[2]));
    }
    this.renderer.setCameraState(exp.camera.pos, exp.camera.target, exp.camera.isOrtho);
  }

  private enqueueBinaryEvent(bytes: Uint8Array): void {
    if (!this.transport) return;
    const kindHex = bytes.byteLength > 0 ? `bin:0x${bytes[0]!.toString(16)}` : 'bin';
    this.dispatchedEventLog.push(kindHex);
    if (this.dispatchedEventLog.length > 40) this.dispatchedEventLog.shift();
    this.eventQueue.enqueueBinary(bytes, performance.now());
  }

  private dispatchJson(ev: JsonInputEvent): Promise<void> {
    if (!this.transport) {
      this.offlineBanner.classList.remove('hidden');
      return Promise.resolve();
    }
    this.dispatchedEventLog.push(`json:${ev.op}`);
    if (this.dispatchedEventLog.length > 40) this.dispatchedEventLog.shift();
    return this.eventQueue.enqueueJson(ev, {
      syncCamera: ev.op === 'loadPreset',
      inputTimestampMs: performance.now(),
    });
  }

  private async executeQueuedEvent(item: QueuedStudioEvent): Promise<void> {
    if (!this.transport) return;
    const t0 = performance.now();
    const frameBytes =
      item.kind === 'bin'
        ? await this.transport.dispatchBin(item.bytes)
        : await this.transport.dispatchJson(item.event);
    this.lastLeanUs = (performance.now() - t0) * 1000;
    this.updateEngineBadge();
    this.ingestRawFrame(frameBytes, item.syncCamera, item.inputTimestampMs);

    if (
      item.kind === 'json' &&
      (item.event.op === 'evalSurface' || item.event.op === 'evalImplicit' || item.event.op === 'evalParametric')
    ) {
      const b = item.event.op === 'evalSurface' ? item.event.bounds : item.event.op === 'evalImplicit' ? item.event.bounds : undefined;
      const extent = b ? Math.max(Math.abs(b[0] ?? 2.5), Math.abs(b[1] ?? 2.5)) : 2.8;
      this.renderer.frameRadius(extent);
    }
  }

  private ingestRawFrame(bytes: Uint8Array, syncCamera: boolean, inputTimestampMs?: number): void {
    try {
      const frame = this.decoder.decode(bytes);
      this.lastFrame = frame;
      this.lastDecodeUs = frame.decodeTimeUs;
      this.renderer.applyFrame(frame, this.decoder, syncCamera, inputTimestampMs);
      this.inspectPanel.update(frame);
      this.codeEditor.setDiagnostics(frame.meta?.diagnostics);
      const errDiag = frame.meta?.diagnostics?.find((d) =>
        typeof d === 'string' ? d.trim().length > 0 : d.severity === 'error'
      );
      this.calcPanel.setInlineError(
        errDiag ? (typeof errDiag === 'string' ? errDiag : errDiag.message) : null
      );
      this.calcPanel.updateCalcState(frame.meta?.calc);
      this.wedgeHud.update(frame.meta?.wedge, this.mode === 'wedge' || Boolean(frame.meta?.wedge));
    } catch (err) {
      const msg = (err as Error).message;
      this.codeEditor.setDiagnostics([{ severity: 'error', message: msg }]);
      this.calcPanel.setInlineError(msg);
    }
  }

  private setAnimationRunning(running: boolean): void {
    this.animRunning = running;
    this.playBtn.textContent = running ? '⏸ Pause' : '▶ Play';
    this.playBtn.classList.toggle('active', running);
    if (running) {
      this.lastAnimTickMs = performance.now();
      const step = () => {
        if (!this.animRunning) return;
        const now = performance.now();
        const dt = Math.min(0.1, Math.max(0.001, (now - this.lastAnimTickMs) * 0.001));
        this.lastAnimTickMs = now;
        this.animTimeSec += dt;
        this.enqueueBinaryEvent(encodeTick(dt, this.animTimeSec));
        this.animRafId = requestAnimationFrame(step);
      };
      this.animRafId = requestAnimationFrame(step);
    } else if (this.animRafId) {
      cancelAnimationFrame(this.animRafId);
      this.animRafId = 0;
    }
  }

  private setStatus(state: 'connecting' | 'connected' | 'error', text: string): void {
    this.statusPill.className = `gs-status-pill ${state}`;
    this.statusPill.textContent = text;
  }

  private makeVpBtn(label: string, onClick: () => void): HTMLButtonElement {
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'gs-vp-btn';
    btn.textContent = label;
    btn.addEventListener('click', onClick);
    return btn;
  }

  private createSplitGutter(
    side: 'left' | 'right',
    pane: HTMLElement,
    minW: number,
    maxW: number,
    defaultW: number
  ): HTMLDivElement {
    const gutter = document.createElement('div');
    gutter.className = 'gs-gutter';
    gutter.title = 'Drag to resize · Double-click to collapse';
    let collapsed = false;
    let savedWidth = defaultW;

    gutter.addEventListener('dblclick', () => {
      collapsed = !collapsed;
      if (collapsed) {
        savedWidth = pane.getBoundingClientRect().width || defaultW;
        pane.style.width = '0px';
        pane.classList.add('collapsed');
      } else {
        pane.classList.remove('collapsed');
        pane.style.width = `${savedWidth}px`;
      }
    });

    gutter.addEventListener('pointerdown', (ev) => {
      ev.preventDefault();
      gutter.classList.add('dragging');
      const startX = ev.clientX;
      const startW = pane.getBoundingClientRect().width;
      const onMove = (me: PointerEvent) => {
        const delta = side === 'left' ? me.clientX - startX : startX - me.clientX;
        const nextW = Math.max(minW, Math.min(maxW, startW + delta));
        collapsed = false;
        pane.classList.remove('collapsed');
        pane.style.width = `${nextW}px`;
      };
      const onUp = () => {
        gutter.classList.remove('dragging');
        window.removeEventListener('pointermove', onMove);
        window.removeEventListener('pointerup', onUp);
      };
      window.addEventListener('pointermove', onMove);
      window.addEventListener('pointerup', onUp);
    });

    return gutter;
  }

  private downloadDataUrl(url: string, filename: string): void {
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    a.remove();
  }

  private pushSparkSample(ms: number): void {
    this.sparkSamples.push(ms);
    if (this.sparkSamples.length > 26) this.sparkSamples.shift();
    const ctx = this.sparkCtx;
    if (!ctx) return;
    const w = this.sparkCanvas.width;
    const h = this.sparkCanvas.height;
    ctx.clearRect(0, 0, w, h);
    const maxMs = Math.max(8, ...this.sparkSamples);
    const barW = 2;
    for (let i = 0; i < this.sparkSamples.length; i++) {
      const v = this.sparkSamples[i]!;
      const barH = Math.max(2, Math.round((v / maxMs) * (h - 2)));
      ctx.fillStyle = v <= 6 ? '#34d399' : v <= 16.7 ? '#38bdf8' : '#fbbf24';
      ctx.fillRect(i * barW, h - barH, barW - 0.5, barH);
    }
  }

  private readonly onGlobalKeyDown = (ev: KeyboardEvent): void => {
    const target = ev.target as HTMLElement | null;
    const isTyping =
      target !== null &&
      (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA' || target.tagName === 'SELECT');

    if (ev.key === 'Enter' && ev.shiftKey) {
      ev.preventDefault();
      void this.dispatchJson({ op: 'evalScript', algebra: this.activeAlgebra, code: this.codeEditor.getCode() });
      return;
    }

    if (isTyping) return;

    if (!ev.metaKey && !ev.ctrlKey && !ev.altKey) {
      if (ev.key === '1') {
        this.setMode('coffeeshop');
        return;
      }
      if (ev.key === '2') {
        this.setMode('wedge');
        return;
      }
      if (ev.key === '3') {
        this.setMode('calculator');
        return;
      }
      if (ev.key === '4') {
        this.setMode('galculator');
        return;
      }
      if (ev.key === ' ') {
        ev.preventDefault();
        this.setAnimationRunning(!this.animRunning);
        return;
      }
      if (ev.key === 'r' || ev.key === 'R') {
        this.renderer.resetCamera();
        return;
      }
      if ((ev.key === 'h' || ev.key === 'H') && this.mode === 'wedge') {
        this.enqueueBinaryEvent(encodeWedgeAction(WedgeActionCode.HINT, 0));
        return;
      }
    }

    if ((ev.metaKey || ev.ctrlKey) && ev.key.toLowerCase() === 'z' && this.mode === 'wedge') {
      ev.preventDefault();
      this.enqueueBinaryEvent(encodeWedgeAction(WedgeActionCode.UNDO, 0));
    }
  };

  dispose(): void {
    window.removeEventListener('keydown', this.onGlobalKeyDown);
    if (this.updatingDelayTimer) {
      clearTimeout(this.updatingDelayTimer);
      this.updatingDelayTimer = null;
    }
    this.eventQueue.dispose();
    this.setAnimationRunning(false);
    this.transport?.dispose();
    this.renderer.dispose();
    this.codeEditor.dispose();
    this.synth.dispose();
  }
}
