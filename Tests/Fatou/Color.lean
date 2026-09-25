import Tests.Fatou.Catalog

/-!
Colouring against the oracles (port-notes/fatou.md G11, G13):

* `schemes.json`: Julia's `(C::ColorScheme)(K)` on catalog sets, for `jet` (9 stops),
  `balance`, `gnuplot`, `cubehelix`, `RdGy`, iteration and `mix` modes.
* `mpl.json` (written by `oracle/fatou/mpl.py`): matplotlib's `Normalize` + colormap
  lookup (`bytes=True`) of the same rasters, compared byte for byte with
  `Raster.toRGBA8` fed matplotlib's 256-entry tables.
-/

namespace Tests.Fatou.Color

open _root_.Fatou Tests.Fatou Tests.Fatou.Catalog

/-- The reduced column count of a set in `sets.json`. -/
def reducedN (sets : Array Lean.Json) (name : String) : IO Nat := do
  for s in sets do
    if (← gStr s "name") == name then return ← gNat s "n"
  throw <| IO.userError s!"{name} not in sets.json"

/-- A computed set of the catalog whose counts and `mix` are replaced by Julia's dumps, so
the colouring is tested on exactly Julia's values. -/
def dumpedSet (name : String) (K : Define) : IO (FilledSet K.spec.rect.rows K.spec.rect.cols) := do
  let Z := fatou K
  let it ← readU16 s!"{name}.iter.u16"
  let mix ← readF64 s!"{name}.mix.f64"
  return FilledSet.ofChunk K Z.bounds (fun _ => ⟨0, 0⟩) ⟨it, Z.zre, Z.zim, mix⟩

/-- Run the suite. -/
def run : TestM Unit := do
  let sets ← gArr (← readJson "sets.json") "sets"
  let j ← readJson "schemes.json"
  let schemes ← field j "schemes"
  for f in ← gArr j "functor" do
    let name ← gStr f "set"
    let s ← gStr f "scheme"
    let stops ← gFs schemes s
    let colors := floatArrayOfFn stops.size fun i => stops[i]!
    let some mk := find? name | check s!"{name} in the Lean catalog" false; continue
    let K := mk (← reducedN sets name)
    let rgb := (← dumpedSet name K).colorScheme colors
    checkEq s!"ColorScheme {s} on {name} (fnv)" (fnv1a (floatBytes rgb)) (← gStr f "fnv")
    let head ← gFs f "rgb"
    check s!"ColorScheme {s} on {name} (head)" ((rgb.toList.zip head.toList).all fun (a, e) => sameF a e)
    -- on the Lean-computed set: `mix` differs from Julia's by at most a few ulps
    let rgb' := (fatou K).colorScheme colors
    check s!"ColorScheme {s} on computed {name}" ((rgb'.toList.zip rgb.toList).all fun (a, e) =>
      closeF a e 1024 1e-12)
  let m ← readJson "mpl.json"
  for c in ← gArr m "cases" do
    let name ← gStr c "set"
    let fieldName ← gStr c "field"
    let cm ← gStr c "cmap"
    let lut : Array Nat ← (← gArr c "lut").mapM (fun x => (nat x : IO Nat))
    let bad : Array Nat ← (← gArr c "bad").mapM (fun x => (nat x : IO Nat))
    let N ← gNat c "N"
    let some mk := find? name | check s!"{name} in the Lean catalog" false; continue
    -- render Julia's dumped values, so this checks the colouring alone
    let K := mk (← reducedN sets name)
    let rows := K.spec.rect.rows
    let cols := K.spec.rect.cols
    let data ← if fieldName == "iter" then do
        let it ← readU16 s!"{name}.iter.u16"
        pure (floatArrayOfFn (rows * cols) fun i => Float.ofNat (getU16 it i).toNat)
      else readF64 s!"{name}.mix.f64"
    if h : data.size = rows * cols then
      let r : Raster rows cols := ⟨data, K.spec.rect.bounds, h⟩
      let cmap (i : Nat) : UInt8 × UInt8 × UInt8 :=
        (lut[3 * i]!.toUInt8, lut[3 * i + 1]!.toUInt8, lut[3 * i + 2]!.toUInt8)
      let px := r.toRGBA8 cmap N (bad[0]!.toUInt8, bad[1]!.toUInt8, bad[2]!.toUInt8, bad[3]!.toUInt8)
      checkEq s!"toRGBA8 {name}.{fieldName} {cm}" (fnv1a px) (← gStr c "fnv")
      let head : Array Nat ← (← gArr c "head").mapM (fun x => (nat x : IO Nat))
      check s!"toRGBA8 {name}.{fieldName} {cm} (head)" ((List.range head.size).all fun i => px[i]!.toNat == head[i]!)
    else check s!"{name} raster size" false
  -- the same through a computed set: Julia's `plot(K)` shows `iter` when `iter = true`
  let Z := fatou (readmeNewton 100)
  let viaSet := Z.toRGBA8 fun i => (i.toUInt8, 0, 0)
  let viaRaster := Z.iterRaster.toRGBA8 fun i => (i.toUInt8, 0, 0)
  check "FilledSet.toRGBA8 uses iter" (viaSet == viaRaster)

end Tests.Fatou.Color
