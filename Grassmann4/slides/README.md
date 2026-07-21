# SF Lean Verso slides

This is a separate presentation package so `VersoSlides` and its documentation
dependencies do not enter the reusable `Grassmann`, `GrassmannFields`, or
`GrassmannViz` library closures. It uses the official `verso-slides` v4.32.0
release and produces a fully offline reveal.js deck.

Build the complete talk portal—deck, browser demo, Lean-generated scene,
tutorial, cue card, and fallback:

```bash
./preflight.sh
uv run python -m http.server 8765 --directory _site
```

Then open `http://127.0.0.1:8765/`. The generated `_site/` directory has the
same path layout used by the public deployment:

- `/slides/` — the Verso deck;
- `/demo/` — the standalone mount of the same React/SVG component;
- `/tutorial/` — the source-cited presenter guide;
- `/cue-card/` — the one-screen 12-minute route.

To build only the deck:

```bash
lake update
lake build
lake exe sflean-slides
```

Serve only the deck locally:

```bash
uv run python -m http.server 8765 --directory _slides
```

Then open `http://127.0.0.1:8765`. Press `S` for the speaker view. The generated
`_slides/` and `_site/` directories are intentionally ignored; all source,
dependency pins, speaker notes, styling, and site-generation logic are
versioned here. `build-site.sh` calls the outer Lake package to export the
validated scene JSON, so the browser demo never recomputes the Clifford field.

The Scarf slide is deliberately precise: Scarf moved new API work to Python and
is gradually shrinking its Haskell footprint; it did not perform a single
big-bang deletion. The framing after that slide is Alok's inference, not a
claim attributed to Scarf or Avi Press.
