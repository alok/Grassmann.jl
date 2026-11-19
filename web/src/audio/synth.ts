// Pure Web Audio API Synthesizer for Wedge Game & Interactive Cues
// Zero audio asset dependencies; subtle, crisp harmonic tones triggered strictly by Lean's WedgeHudState.lastOp / solved.

export type WedgeAudioCue = 'join' | 'wedge' | 'add' | 'dot' | 'win' | 'invalid' | 'select';

export class StudioAudioSynth {
  private ctx: AudioContext | null = null;
  private muted = false;

  isMuted(): boolean {
    return this.muted;
  }

  setMuted(muted: boolean): void {
    this.muted = muted;
  }

  toggleMute(): boolean {
    this.muted = !this.muted;
    return this.muted;
  }

  play(cue: WedgeAudioCue): void {
    if (this.muted || typeof window === 'undefined') return;
    const AudioCtx = window.AudioContext ?? (window as unknown as { webkitAudioContext?: typeof AudioContext }).webkitAudioContext;
    if (!AudioCtx) return;

    if (!this.ctx) {
      this.ctx = new AudioCtx();
    }
    if (this.ctx.state === 'suspended') {
      void this.ctx.resume();
    }

    const now = this.ctx.currentTime;
    switch (cue) {
      case 'select':
        this.tone(now, 660, 0.06, 'sine', 0.05);
        break;
      case 'join':
        // Rising perfect fifth (C5 -> G5)
        this.tone(now, 523.25, 0.14, 'triangle', 0.08);
        this.tone(now + 0.06, 783.99, 0.22, 'sine', 0.09);
        break;
      case 'wedge':
        // Crisp crystalline convergence (A5 -> E5)
        this.tone(now, 880.0, 0.12, 'sine', 0.08);
        this.tone(now + 0.05, 659.25, 0.2, 'triangle', 0.07);
        break;
      case 'add':
        // Warm balanced dyad (D5 + F#5)
        this.tone(now, 587.33, 0.22, 'sine', 0.07);
        this.tone(now, 739.99, 0.22, 'triangle', 0.06);
        break;
      case 'dot':
        // Crisp orthogonal chime (B5 -> F#5)
        this.tone(now, 987.77, 0.08, 'sine', 0.07);
        this.tone(now + 0.04, 739.99, 0.16, 'sine', 0.07);
        break;
      case 'win': {
        // Luminous major-9th arpeggio fanfare
        const notes = [523.25, 659.25, 783.99, 987.77, 1174.66];
        notes.forEach((freq, idx) => {
          this.tone(now + idx * 0.075, freq, 0.38, idx % 2 === 0 ? 'sine' : 'triangle', 0.08);
        });
        break;
      }
      case 'invalid':
        this.tone(now, 220, 0.11, 'sawtooth', 0.04);
        this.tone(now + 0.07, 185, 0.14, 'sawtooth', 0.035);
        break;
    }
  }

  private tone(
    startTime: number,
    freq: number,
    duration: number,
    type: OscillatorType,
    peakGain: number
  ): void {
    if (!this.ctx) return;
    const osc = this.ctx.createOscillator();
    const gain = this.ctx.createGain();
    osc.type = type;
    osc.frequency.setValueAtTime(freq, startTime);

    gain.gain.setValueAtTime(0.0001, startTime);
    gain.gain.exponentialRampToValueAtTime(peakGain, startTime + 0.012);
    gain.gain.exponentialRampToValueAtTime(0.0001, startTime + duration);

    osc.connect(gain);
    gain.connect(this.ctx.destination);
    osc.start(startTime);
    osc.stop(startTime + duration + 0.02);
  }

  dispose(): void {
    if (this.ctx) {
      void this.ctx.close();
      this.ctx = null;
    }
  }
}
