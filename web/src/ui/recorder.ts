// 60fps WebM Video Recorder for the 3D WebGL Viewport
// Uses canvas.captureStream(60) + MediaRecorder (VP9 -> VP8 -> default WebM) with auto download.

export interface RecorderState {
  recording: boolean;
  remainingSec: number;
  progress: number;
}

export class ViewportVideoRecorder {
  private recorder: MediaRecorder | null = null;
  private chunks: Blob[] = [];
  private timerId: ReturnType<typeof setInterval> | null = null;
  private stopTimeoutId: ReturnType<typeof setTimeout> | null = null;
  private onState?: (state: RecorderState) => void;

  static isSupported(canvas: HTMLCanvasElement): boolean {
    return (
      typeof MediaRecorder !== 'undefined' &&
      typeof (canvas as unknown as { captureStream?: unknown }).captureStream === 'function'
    );
  }

  get isRecording(): boolean {
    return this.recorder !== null && this.recorder.state === 'recording';
  }

  start(
    canvas: HTMLCanvasElement,
    options: {
      durationSec?: number;
      filenamePrefix?: string;
      onState?: (state: RecorderState) => void;
    } = {}
  ): boolean {
    if (this.isRecording) {
      this.stop();
      return false;
    }
    if (!ViewportVideoRecorder.isSupported(canvas)) {
      return false;
    }

    const durationSec = Math.max(1, options.durationSec ?? 5);
    const prefix = (options.filenamePrefix || 'grassmann-studio').replace(/[^a-zA-Z0-9_-]/g, '_');
    this.onState = options.onState;
    this.chunks = [];

    const stream = canvas.captureStream(60);
    const mimeCandidates = [
      'video/webm;codecs=vp9',
      'video/webm;codecs=vp8',
      'video/webm',
    ];
    const mimeType = mimeCandidates.find((m) => MediaRecorder.isTypeSupported(m)) ?? '';

    const rec = mimeType
      ? new MediaRecorder(stream, { mimeType, videoBitsPerSecond: 6_000_000 })
      : new MediaRecorder(stream);

    this.recorder = rec;

    rec.ondataavailable = (ev) => {
      if (ev.data && ev.data.size > 0) {
        this.chunks.push(ev.data);
      }
    };

    rec.onstop = () => {
      this.cleanupTimers();
      this.recorder = null;
      this.onState?.({ recording: false, remainingSec: 0, progress: 0 });
      if (this.chunks.length > 0) {
        const blob = new Blob(this.chunks, { type: mimeType || 'video/webm' });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = `${prefix}-${Date.now()}.webm`;
        document.body.appendChild(a);
        a.click();
        a.remove();
        setTimeout(() => URL.revokeObjectURL(url), 5000);
      }
      this.chunks = [];
    };

    const startMs = performance.now();
    rec.start(200);
    this.onState?.({ recording: true, remainingSec: durationSec, progress: 0 });

    this.timerId = setInterval(() => {
      const elapsed = (performance.now() - startMs) * 0.001;
      const remaining = Math.max(0, durationSec - elapsed);
      const progress = Math.min(1, elapsed / durationSec);
      this.onState?.({ recording: true, remainingSec: remaining, progress });
    }, 100);

    this.stopTimeoutId = setTimeout(() => {
      this.stop();
    }, durationSec * 1000);

    return true;
  }

  stop(): void {
    this.cleanupTimers();
    if (this.recorder && this.recorder.state === 'recording') {
      try {
        this.recorder.stop();
      } catch {
        // Ignore stop errors if stream already closed
      }
    }
  }

  dispose(): void {
    this.stop();
  }

  private cleanupTimers(): void {
    if (this.timerId) {
      clearInterval(this.timerId);
      this.timerId = null;
    }
    if (this.stopTimeoutId) {
      clearTimeout(this.stopTimeoutId);
      this.stopTimeoutId = null;
    }
  }
}
