import LeanPlot

/-!
# Pixel agreement of two renders

The Lean and Julia PNGs of a figure have the same size (both are rendered at one pixel per
unit of the same figure size), so they can be compared pixel by pixel: the mean absolute
difference of the RGB channels (in units of 1/255) and the fraction of pixels whose largest
channel difference exceeds 64/255. This is a coarse visual metric (fonts, anti-aliasing and
Makie's 3D shading differ by design); the plotted data is compared exactly elsewhere.
-/

namespace Gallery.ImageDiff

/-- Pixel statistics of two same-size RGBA8 images. -/
structure Stats where
  /-- width -/
  w : Nat
  /-- height -/
  h : Nat
  /-- mean `|Δ|` over the RGB channels, in `1/255` -/
  meanAbs : Float
  /-- fraction of pixels with a channel difference above `64/255` -/
  fracBig : Float

/-- The scan over pixels: sum of channel differences and count of large ones. -/
def scan (a b : ByteArray) (n : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, s, big => (s, big)
  | k + 1, s, big =>
    let i := n - (k + 1)
    let d (c : Nat) : Nat :=
      let x := (a.get! (4 * i + c)).toNat
      let y := (b.get! (4 * i + c)).toNat
      if x ≥ y then x - y else y - x
    let dr := d 0
    let dg := d 1
    let db := d 2
    scan a b n k (s + dr + dg + db) (if max dr (max dg db) > 64 then big + 1 else big)

/-- Compare two PNG files (decoded with LeanPlot's reader). -/
def comparePNG (fa fb : ByteArray) : Except String Stats := do
  let (wa, ha, a) ← LeanPlot.PNG.decodeRGBA fa
  let (wb, hb, b) ← LeanPlot.PNG.decodeRGBA fb
  if wa != wb || ha != hb then throw s!"sizes differ: {wa}×{ha} vs {wb}×{hb}"
  let n := wa * ha
  let (s, big) := scan a b n n 0 0
  let nf := n.toUInt64.toFloat
  return { w := wa, h := ha, meanAbs := s.toUInt64.toFloat / (3 * nf), fracBig := big.toUInt64.toFloat / nf }

/-- One-line summary, e.g. `mean |ΔRGB| 1.3/255, 0.8% of pixels > 64/255`. -/
def Stats.summary (s : Stats) : String :=
  let r1 (x : Float) : String :=
    let v := (x * 10).round / 10
    let str := toString v
    match str.splitOn "." with
    | [a, b] => a ++ "." ++ b.take 1
    | _ => str
  s!"mean |ΔRGB| {r1 s.meanAbs}/255, {r1 (100 * s.fracBig)}% of pixels > 64/255"

end Gallery.ImageDiff
