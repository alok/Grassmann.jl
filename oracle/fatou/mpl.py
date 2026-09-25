"""matplotlib oracle for `Fatou.Raster.toRGBA8` (port-notes/fatou.md §4.8, G13).

    uv run --with matplotlib --with numpy python oracle/fatou/mpl.py

Reads the raster dumps written by `oracle/fatou/gen.jl` and writes
`oracle/golden/fatou/mpl.json`: for each (set, plotted field, colormap) the 256-entry lookup
table as bytes (what the Lean test passes as `cmap`) and the RGBA bytes of
`cmap(Normalize(nanmin, nanmax)(data), bytes=True)`, i.e. what PyPlot's `imshow` colours
each pixel with before any resampling (NaN pixels get the transparent "bad" colour).
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib
import numpy as np
from matplotlib.colors import Normalize

GOLDEN = Path(__file__).resolve().parent.parent / "golden" / "fatou"


def fnv1a(data: bytes) -> str:
    h = 0xCBF29CE484222325
    for b in data:
        h = ((h ^ b) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"{h:016x}"


def load(name: str, field: str, rows: int, cols: int) -> np.ndarray:
    if field == "iter":
        a = np.fromfile(GOLDEN / f"{name}.iter.u16", dtype="<u2")
    else:
        a = np.fromfile(GOLDEN / f"{name}.mix.f64", dtype="<f8")
    return a.reshape(rows, cols)


def main() -> None:
    sets = {s["name"]: s for s in json.loads((GOLDEN / "sets.json").read_text())["sets"]}
    cases = [
        ("readme_filled_julia", "iter", "gnuplot"),
        ("readme_mandelbrot", "mix", "gist_earth"),
        ("readme_newton", "iter", "jet"),
        ("readme_gen_newton", "iter", "cubehelix"),
        ("readme_gen_newton", "mix", "viridis"),
        ("default_juliafill", "mix", "viridis"),
        ("newton_mhalf", "mix", "hsv"),
    ]
    out = []
    for name, field, cmapname in cases:
        meta = sets[name]
        data = load(name, field, meta["rows"], meta["cols"])
        cmap = matplotlib.colormaps[cmapname]
        lut = cmap(np.arange(cmap.N), bytes=True)[:, :3]
        masked = np.ma.masked_invalid(data)
        norm = Normalize(vmin=float(masked.min()), vmax=float(masked.max()))
        rgba = cmap(norm(masked), bytes=True)
        raw = np.ascontiguousarray(rgba, dtype=np.uint8).tobytes()
        out.append({
            "set": name, "field": field, "cmap": cmapname, "N": int(cmap.N),
            "lut": [int(v) for v in lut.reshape(-1)], "bad": [int(v) for v in cmap(np.nan, bytes=True)],
            "fnv": fnv1a(raw), "head": list(raw[:512]),
        })
        print(name, field, cmapname, fnv1a(raw))
    (GOLDEN / "mpl.json").write_text(json.dumps({"matplotlib": matplotlib.__version__, "cases": out}))


if __name__ == "__main__":
    main()
