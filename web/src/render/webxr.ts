// WebXR Session Manager (Vision Pro / Quest / Desktop XR)
// Implements RayTrace4D (#8) visionOS lessons:
//  1. Listens on ALL 4 controller slots (0..3) because visionOS exposes tracked hands on slots 0/1
//     and gaze+pinch transient-pointer sources on slots 2/3.
//  2. Uses wrist joint when hand-tracking is active to avoid fingertip pinch convergence drift.
//  3. Caps WebXR framebuffer scale factor at 1.5x to respect Vision Pro high-DPI VRAM budget.

import * as THREE from 'three';

export interface XrPinchDragEvent {
  slot: number;
  rayOrigin: THREE.Vector3;
  rayDirection: THREE.Vector3;
  anchorWorld: THREE.Vector3;
  deltaWorld: THREE.Vector3;
  phase: 'start' | 'move' | 'end';
}

export interface WebXrManagerCallbacks {
  onSessionChange?: (active: boolean) => void;
  onPinch?: (event: XrPinchDragEvent) => void;
  onTwoHandPinch?: (slotA: XrPinchDragEvent, slotB: XrPinchDragEvent, commit: boolean) => void;
}

interface SlotState {
  active: boolean;
  startPos: THREE.Vector3;
  lastPos: THREE.Vector3;
  rayOrigin: THREE.Vector3;
  rayDir: THREE.Vector3;
}

const MAX_XR_SLOTS = 4;
const XR_FRAMEBUFFER_SCALE_CAP = 1.5;

export class WebXrManager {
  private readonly renderer: THREE.WebGLRenderer;
  private readonly scene: THREE.Scene;
  private readonly callbacks: WebXrManagerCallbacks;
  private readonly controllers: THREE.XRTargetRaySpace[] = [];
  private readonly hands: THREE.XRHandSpace[] = [];
  private readonly slotStates: SlotState[] = [];
  private session: XRSession | null = null;
  private supportedMode: 'immersive-ar' | 'immersive-vr' | null = null;

  private readonly tmpMatrix = new THREE.Matrix4();
  private readonly tmpPos = new THREE.Vector3();
  private readonly tmpDir = new THREE.Vector3();

  constructor(renderer: THREE.WebGLRenderer, scene: THREE.Scene, callbacks: WebXrManagerCallbacks = {}) {
    this.renderer = renderer;
    this.scene = scene;
    this.callbacks = callbacks;

    for (let slot = 0; slot < MAX_XR_SLOTS; slot++) {
      this.slotStates.push({
        active: false,
        startPos: new THREE.Vector3(),
        lastPos: new THREE.Vector3(),
        rayOrigin: new THREE.Vector3(),
        rayDir: new THREE.Vector3(0, 0, -1),
      });

      const controller = renderer.xr.getController(slot);
      controller.addEventListener('selectstart', () => this.handleSelectStart(slot));
      controller.addEventListener('selectend', () => this.handleSelectEnd(slot));
      scene.add(controller);
      this.controllers.push(controller);

      const hand = renderer.xr.getHand(slot);
      scene.add(hand);
      this.hands.push(hand);
    }
  }

  async detectSupport(): Promise<'immersive-ar' | 'immersive-vr' | null> {
    if (typeof navigator === 'undefined' || !navigator.xr) {
      this.supportedMode = null;
      return null;
    }
    try {
      if (await navigator.xr.isSessionSupported('immersive-ar')) {
        this.supportedMode = 'immersive-ar';
        return 'immersive-ar';
      }
      if (await navigator.xr.isSessionSupported('immersive-vr')) {
        this.supportedMode = 'immersive-vr';
        return 'immersive-vr';
      }
    } catch {
      // ignore insecure context / unsupported error
    }
    this.supportedMode = null;
    return null;
  }

  isActive(): boolean {
    return this.session !== null;
  }

  getSupportedMode(): 'immersive-ar' | 'immersive-vr' | null {
    return this.supportedMode;
  }

  async toggleSession(): Promise<boolean> {
    if (this.session) {
      await this.session.end();
      return false;
    }
    if (!navigator.xr) {
      throw new Error('WebXR is not available in this browser');
    }
    const mode = this.supportedMode ?? (await this.detectSupport());
    if (!mode) {
      throw new Error('No immersive WebXR session supported on this device');
    }

    // Cap framebuffer scale factor strictly at 1.5x (RayTrace4D #8)
    const scale = Math.min(XR_FRAMEBUFFER_SCALE_CAP, window.devicePixelRatio || 1);
    this.renderer.xr.setFramebufferScaleFactor(scale);
    this.renderer.xr.enabled = true;

    const session = await navigator.xr.requestSession(mode, {
      optionalFeatures: ['local-floor', 'bounded-floor', 'hand-tracking'],
    });
    this.session = session;

    session.addEventListener('end', () => {
      this.session = null;
      this.renderer.xr.enabled = false;
      for (const st of this.slotStates) st.active = false;
      this.callbacks.onSessionChange?.(false);
    });

    await this.renderer.xr.setSession(session);
    this.callbacks.onSessionChange?.(true);
    return true;
  }

  /**
   * Called once per animation frame during active XR sessions.
   */
  updateFrame(): void {
    if (!this.session) return;

    const activeEvents: XrPinchDragEvent[] = [];
    for (let slot = 0; slot < MAX_XR_SLOTS; slot++) {
      const state = this.slotStates[slot]!;
      if (!state.active) continue;
      this.sampleSlotPose(slot, this.tmpPos, this.tmpDir);
      state.lastPos.copy(this.tmpPos);
      state.rayOrigin.copy(this.tmpPos);
      state.rayDir.copy(this.tmpDir);

      const ev: XrPinchDragEvent = {
        slot,
        rayOrigin: state.rayOrigin.clone(),
        rayDirection: state.rayDir.clone(),
        anchorWorld: state.startPos.clone(),
        deltaWorld: state.lastPos.clone().sub(state.startPos),
        phase: 'move',
      };
      activeEvents.push(ev);
      if (activeEvents.length === 1) {
        this.callbacks.onPinch?.(ev);
      }
    }

    if (activeEvents.length >= 2) {
      this.callbacks.onTwoHandPinch?.(activeEvents[0]!, activeEvents[1]!, false);
    }
  }

  private handleSelectStart(slot: number): void {
    const state = this.slotStates[slot]!;
    this.sampleSlotPose(slot, this.tmpPos, this.tmpDir);
    state.active = true;
    state.startPos.copy(this.tmpPos);
    state.lastPos.copy(this.tmpPos);
    state.rayOrigin.copy(this.tmpPos);
    state.rayDir.copy(this.tmpDir);

    this.callbacks.onPinch?.({
      slot,
      rayOrigin: state.rayOrigin.clone(),
      rayDirection: state.rayDir.clone(),
      anchorWorld: state.startPos.clone(),
      deltaWorld: new THREE.Vector3(),
      phase: 'start',
    });
  }

  private handleSelectEnd(slot: number): void {
    const state = this.slotStates[slot]!;
    if (!state.active) return;

    // Check if another slot is simultaneously active -> commit two-hand gesture
    const partnerSlot = this.slotStates.findIndex((s, i) => i !== slot && s.active);
    this.sampleSlotPose(slot, this.tmpPos, this.tmpDir);
    state.lastPos.copy(this.tmpPos);

    const endEv: XrPinchDragEvent = {
      slot,
      rayOrigin: this.tmpPos.clone(),
      rayDirection: this.tmpDir.clone(),
      anchorWorld: state.startPos.clone(),
      deltaWorld: state.lastPos.clone().sub(state.startPos),
      phase: 'end',
    };

    if (partnerSlot >= 0) {
      const p = this.slotStates[partnerSlot]!;
      const partnerEv: XrPinchDragEvent = {
        slot: partnerSlot,
        rayOrigin: p.rayOrigin.clone(),
        rayDirection: p.rayDir.clone(),
        anchorWorld: p.startPos.clone(),
        deltaWorld: p.lastPos.clone().sub(p.startPos),
        phase: 'move',
      };
      this.callbacks.onTwoHandPinch?.(partnerEv, endEv, true);
    }

    state.active = false;
    this.callbacks.onPinch?.(endEv);
  }

  /**
   * Prefers tracked hand wrist joint (avoids fingertip pinch drift per RayTrace4D #8),
   * falling back to target-ray controller world pose.
   */
  private sampleSlotPose(slot: number, outPos: THREE.Vector3, outDir: THREE.Vector3): void {
    const controller = this.controllers[slot]!;
    const hand = this.hands[slot] as unknown as { joints?: Record<string, THREE.Object3D> };

    this.tmpMatrix.identity().extractRotation(controller.matrixWorld);
    outDir.set(0, 0, -1).applyMatrix4(this.tmpMatrix).normalize();

    const wrist = hand?.joints?.['wrist'];
    if (wrist && wrist.visible) {
      wrist.getWorldPosition(outPos);
    } else {
      outPos.setFromMatrixPosition(controller.matrixWorld);
    }
  }

  dispose(): void {
    if (this.session) {
      void this.session.end();
      this.session = null;
    }
    for (const c of this.controllers) this.scene.remove(c);
    for (const h of this.hands) this.scene.remove(h);
  }
}
