import { describe, expect, it } from 'vitest';
import {
  WedgeActionCode,
  decodeGsirFrame,
  encodeWedgeAction,
  GSIR_HEADER_SIZE,
  GSIR_MAGIC,
  GSIR_VERSION,
} from '../src/gsir';
import { OrderedStudioEventQueue } from '../src/transport';

describe('Wave 4B: setParam Coalescing in OrderedStudioEventQueue', () => {
  it('coalesces consecutive setParam events per parameter name while strictly respecting discrete barriers & distinct params', async () => {
    const executed: string[] = [];
    let releaseFirst!: () => void;

    const queue = new OrderedStudioEventQueue({
      execute: async (item) => {
        if (item.kind === 'json' && item.event.op === 'loadPreset' && item.event.id === 'slow_init') {
          executed.push('slow_init:start');
          await new Promise<void>((r) => {
            releaseFirst = r;
          });
          executed.push('slow_init:done');
          return;
        }
        if (item.kind === 'json' && item.event.op === 'setParam') {
          executed.push(`param:${item.event.name}=${item.event.value.toFixed(2)}`);
          return;
        }
        if (item.kind === 'bin') {
          executed.push(`bin:0x${item.bytes[0]!.toString(16)}`);
          return;
        }
        if (item.kind === 'json') {
          executed.push(`json:${item.event.op}`);
        }
      },
    });

    const p0 = queue.enqueueJson({ op: 'loadPreset', id: 'slow_init' });

    // Rapid drags on 'beta' -> coalesce to 0.85, and superseded promises MUST still resolve!
    const pBeta1 = queue.enqueueJson({ op: 'setParam', name: 'beta', value: 0.25 });
    const pBeta2 = queue.enqueueJson({ op: 'setParam', name: 'beta', value: 0.55 });
    const pBeta3 = queue.enqueueJson({ op: 'setParam', name: 'beta', value: 0.85 });

    // Different parameter 'gravity' does NOT clobber 'beta', and coalesces its own drags to 9.81
    const pGrav1 = queue.enqueueJson({ op: 'setParam', name: 'gravity', value: 4.0 });
    const pGrav2 = queue.enqueueJson({ op: 'setParam', name: 'gravity', value: 9.81 });

    // Discrete WedgeAction barrier -> subsequent 'gravity' drag must stay AFTER it!
    queue.enqueueBinary(encodeWedgeAction(WedgeActionCode.RESET, 0));
    const pGrav3 = queue.enqueueJson({ op: 'setParam', name: 'gravity', value: 1.62 });

    releaseFirst();
    await Promise.all([p0, pBeta1, pBeta2, pBeta3, pGrav1, pGrav2, pGrav3]);

    expect(executed).toEqual([
      'slow_init:start',
      'slow_init:done',
      'param:beta=0.85',
      'param:gravity=9.81',
      'bin:0x7',
      'param:gravity=1.62',
    ]);
  });
});

describe('Wave 4B: GSIR v1 metaJson.{params, formula, summary} Decoding', () => {
  it('decodes params[], LaTeX formula, and summary cleanly from GSIR v1 binary frames', () => {
    const meta = {
      version: 1,
      presetId: 'sta_terrell_penrose',
      title: 'STA Terrell-Penrose Rotation',
      formula: 'B(\\phi) = \\exp(-\\tfrac{\\phi}{2} e_t e_x)',
      summary: 'Lorentz-contracted + optical-aberration rotated 3D lattice cube.',
      params: [
        { name: 'beta', label: 'Velocity β = v/c', value: 0.65, min: 0, max: 0.95, step: 0.01 },
        { name: 'tilt', label: 'Camera Pitch', value: 0.3, min: -1, max: 1, step: 0.05 },
      ],
    };
    const metaBytes = new TextEncoder().encode(JSON.stringify(meta));
    const metaOffset = GSIR_HEADER_SIZE;
    const totalLen = (metaOffset + metaBytes.byteLength + 7) & ~7;
    const buf = new ArrayBuffer(totalLen);
    const dv = new DataView(buf);
    dv.setUint32(0, GSIR_MAGIC, true);
    dv.setUint16(4, GSIR_VERSION, true);
    dv.setUint16(6, 1, true);
    dv.setBigUint64(8, 1n, true);
    dv.setUint32(32, totalLen, true);
    dv.setUint32(36, metaOffset, true);
    dv.setUint32(40, metaBytes.byteLength, true);
    new Uint8Array(buf, metaOffset, metaBytes.byteLength).set(metaBytes);

    const frame = decodeGsirFrame(new Uint8Array(buf));
    expect(frame.meta?.formula).toBe(meta.formula);
    expect(frame.meta?.summary).toBe(meta.summary);
    expect(frame.meta?.params).toHaveLength(2);
    expect(frame.meta?.params?.[0]).toEqual(meta.params[0]);
    expect(frame.meta?.params?.[1]?.name).toBe('tilt');
  });
});
