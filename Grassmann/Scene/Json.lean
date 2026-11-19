import Grassmann.Scene.Types

/-!
# Init-Only Zero-Dependency JSON Serializer & Parser for `SceneIR` v1

Deliberately avoids importing `Lean.Data.Json` so the compiled runtime C ABI / WASM
library links ONLY `Init` + `Grassmann` runtime kernels (preventing 180–264 MB dylib bloat).
-/

namespace Grassmann.Scene.Json

/-! ## Formatting Helpers -/

/-- Escape a string for JSON output. -/
def escapeString (s : String) : String :=
  let rec go (cs : List Char) (acc : List Char) : String :=
    match cs with
    | [] => String.ofList acc.reverse
    | c :: rest =>
      match c with
      | '"'  => go rest ('"' :: '\\' :: acc)
      | '\\' => go rest ('\\' :: '\\' :: acc)
      | '\n' => go rest ('n' :: '\\' :: acc)
      | '\r' => go rest ('r' :: '\\' :: acc)
      | '\t' => go rest ('t' :: '\\' :: acc)
      | _ =>
        if c.val < 0x20 then
          let hexDigit (n : UInt32) : Char :=
            if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
          let d1 := hexDigit ((c.val >>> 4) &&& 0xF)
          let d0 := hexDigit (c.val &&& 0xF)
          go rest (d0 :: d1 :: '0' :: '0' :: 'u' :: '\\' :: acc)
        else
          go rest (c :: acc)
  go s.toList []

@[inline] def quote (s : String) : String := "\"" ++ escapeString s ++ "\""

/-- Format a `Float` cleanly as valid JSON number (maps NaN/Inf to `0`). -/
def fmtFloat (x : Float) : String :=
  if !x.isFinite || x.isNaN then "0"
  else if Float.abs x < 1e-15 then "0"
  else
    let s := toString x
    if s.endsWith ".000000" then
      (s.dropEnd 7).toString
    else
      s

def joinSep (sep : String) (xs : Array String) : String :=
  let rec go (i : Nat) (acc : String) : String :=
    if i < xs.size then
      let next := if i == 0 then xs[i]! else acc ++ sep ++ xs[i]!
      go (i + 1) next
    else acc
  go 0 ""

@[inline] def arrJson (xs : Array String) : String := "[" ++ joinSep "," xs ++ "]"
@[inline] def objJson (fields : Array (String × String)) : String :=
  "{" ++ joinSep "," (fields.map fun (k, v) => quote k ++ ":" ++ v) ++ "}"

def fmtVec3 (v : Vec3) : String :=
  "[" ++ fmtFloat v.x ++ "," ++ fmtFloat v.y ++ "," ++ fmtFloat v.z ++ "]"

def fmtRGBA (c : RGBA) : String :=
  "[" ++ fmtFloat c.r ++ "," ++ fmtFloat c.g ++ "," ++ fmtFloat c.b ++ "," ++ fmtFloat c.a ++ "]"

def fmtFloatArray (xs : FloatArray) : String :=
  let rec go (i : Nat) (acc : Array String) : Array String :=
    if i < xs.size then go (i + 1) (acc.push (fmtFloat (xs.get! i))) else acc
  arrJson (go 0 (Array.mkEmpty xs.size))

/-! ## `SceneFrame` Metadata JSON (`metaJson` chunk in `GSIR` v1) -/

/-- Collect all unique label strings across frame primitives in deterministic order,
returning `(labelsTable, lookupIdx)`. -/
def buildLabelTable (f : SceneFrame) : Array String := Id.run do
  let mut tbl : Array String := #[]
  let pushUnique := fun (arr : Array String) (s : String) =>
    if s.isEmpty || arr.contains s then arr else arr.push s
  for p in f.points do tbl := pushUnique tbl p.label
  for l in f.lines do tbl := pushUnique tbl l.label
  for p in f.planes do tbl := pushUnique tbl p.label
  for c in f.circles do tbl := pushUnique tbl c.label
  for s in f.spheres do tbl := pushUnique tbl s.label
  for pp in f.pointPairs do tbl := pushUnique tbl pp.label
  for lb in f.labels do tbl := pushUnique tbl lb.text
  match f.contourOverlay with
  | some co =>
    for pt in co.intersections do tbl := pushUnique tbl pt.label
  | none => pure ()
  return tbl

/-- Look up a label index (`0xFFFFFFFF` if empty/missing). -/
def findLabelIdx (tbl : Array String) (s : String) : UInt32 :=
  if s.isEmpty then 0xFFFFFFFF
  else
    let rec go (i : Nat) : UInt32 :=
      if i < tbl.size then
        if tbl[i]! == s then i.toUInt32 else go (i + 1)
      else 0xFFFFFFFF
    go 0

def algebraMetaJson (a : AlgebraMeta) : String :=
  objJson #[
    ("name", quote a.name),
    ("p", toString a.p.toNat),
    ("q", toString a.q.toNat),
    ("r", toString a.r.toNat),
    ("conformalWitt", if a.conformalWitt then "true" else "false"),
    ("basisNames", arrJson (a.basisNames.map quote)),
    ("basisMetric", arrJson (a.basisMetric.map fun m => toString m.toInt))
  ]

def inspectEntryJson (e : InspectEntry) : String :=
  objJson #[
    ("idx", toString e.idx.toNat),
    ("name", quote e.name),
    ("grade", toString e.grade.toNat),
    ("formatted", quote e.formatted),
    ("editable", if e.editable then "true" else "false")
  ]

def opnsShaderJson (s : OpnsShaderSource) : String :=
  objJson #[
    ("hash", quote s.hash),
    ("wgsl", quote s.wgsl),
    ("glsl", quote s.glsl),
    ("msl", quote s.msl)
  ]

def calcHudJson (c : CalcHudState) : String :=
  objJson #[
    ("mode", quote c.mode),
    ("display", quote c.display),
    ("history", arrJson (c.history.map quote)),
    ("registers", arrJson (c.registers.map fun r =>
      objJson #[("slot", quote r.slot), ("formatted", quote r.formatted)]))
  ]

def wedgeHudJson (w : WedgeHudState) : String :=
  objJson #[
    ("is3D", if w.is3D then "true" else "false"),
    ("level", toString w.level.toNat),
    ("totalLevels", toString w.totalLevels.toNat),
    ("title", quote w.title),
    ("goal", quote w.goal),
    ("tutorialText", quote w.tutorialText),
    ("moves", toString w.moves.toNat),
    ("score", toString w.score.toNat),
    ("elapsedMs", toString w.elapsedMs.toNat),
    ("lastOp", quote w.lastOp),
    ("previewOp", quote w.previewOp),
    ("hintText", quote w.hintText),
    ("solved", if w.solved then "true" else "false"),
    ("canUndo", if w.canUndo then "true" else "false")
  ]

def paramSpecJson (p : ParamSpec) : String :=
  objJson #[
    ("name", quote p.name),
    ("label", quote (if p.label.isEmpty then p.name else p.label)),
    ("value", fmtFloat p.value),
    ("min", fmtFloat p.min),
    ("max", fmtFloat p.max),
    ("step", fmtFloat p.step)
  ]

/-- Emit the canonical `GSIR` v1 `metaJson` UTF-8 JSON chunk for `SceneFrame`. -/
def toMetaJson (f : SceneFrame) (labelsTbl : Array String) : String :=
  let base : Array (String × String) := #[
    ("version", "1"),
    ("algebra", algebraMetaJson f.algebra),
    ("presetId", quote f.presetId),
    ("title", quote f.title),
    ("script", quote f.script),
    ("params", arrJson (f.params.map paramSpecJson)),
    ("formula", quote f.formula),
    ("summary", quote f.summary),
    ("labels", arrJson (labelsTbl.map quote)),
    ("inspect", arrJson (f.inspect.map inspectEntryJson)),
    ("opnsShaders", arrJson (f.opnsShaders.map opnsShaderJson)),
    ("calc", match f.calcHud with | some c => calcHudJson c | none => "null"),
    ("wedge", match f.wedgeHud with | some w => wedgeHudJson w | none => "null"),
    ("diagnostics", arrJson (f.diagnostics.map quote))
  ]
  objJson base

/-- Emit a complete standalone JSON representation (for debugging / JSON-only endpoints). -/
def toFullJson (f : SceneFrame) : String :=
  let labelsTbl := buildLabelTable f
  let pts := arrJson (f.points.map fun p => objJson #[
    ("id", toString p.handleId.toNat), ("pos", fmtVec3 p.pos), ("r", fmtFloat p.radius),
    ("rgba", fmtRGBA p.color), ("draggable", if p.role.draggable then "true" else "false"),
    ("label", quote p.label)
  ])
  let segs := arrJson (f.segments.map fun s => objJson #[
    ("a", fmtVec3 s.a), ("b", fmtVec3 s.b), ("w", fmtFloat s.width), ("rgba", fmtRGBA s.color)
  ])
  let lns := arrJson (f.lines.map fun l => objJson #[
    ("origin", fmtVec3 l.origin), ("dir", fmtVec3 l.dir), ("clip", fmtFloat l.clip),
    ("rgba", fmtRGBA l.color), ("label", quote l.label)
  ])
  let pls := arrJson (f.planes.map fun pl => objJson #[
    ("center", fmtVec3 pl.center), ("u", fmtVec3 pl.u), ("v", fmtVec3 pl.v),
    ("extent", fmtFloat pl.extent), ("rgba", fmtRGBA pl.color), ("label", quote pl.label)
  ])
  let circs := arrJson (f.circles.map fun c => objJson #[
    ("center", fmtVec3 c.center), ("u", fmtVec3 c.u), ("v", fmtVec3 c.v),
    ("radius", fmtFloat c.radius), ("imaginary", if c.imaginary then "true" else "false"),
    ("rgba", fmtRGBA c.color), ("label", quote c.label)
  ])
  let sphs := arrJson (f.spheres.map fun s => objJson #[
    ("center", fmtVec3 s.center), ("radius", fmtFloat s.radius),
    ("imaginary", if s.imaginary then "true" else "false"),
    ("rgba", fmtRGBA s.color), ("label", quote s.label)
  ])
  objJson #[
    ("meta", toMetaJson f labelsTbl),
    ("frameSeq", toString f.frameSeq.toNat),
    ("simTime", fmtFloat f.simTime),
    ("is2D", if f.is2D then "true" else "false"),
    ("points", pts),
    ("segments", segs),
    ("lines", lns),
    ("planes", pls),
    ("circles", circs),
    ("spheres", sphs),
    ("meshRefCount", toString f.meshRefs.size),
    ("meshAssetCount", toString f.meshAssets.size),
    ("curveCount", toString f.curves.size)
  ]

/-! ## Lightweight Init-Only JSON Parser (for JSON `InputEvent` Control Messages) -/

inductive JVal where
  | null
  | bool (b : Bool)
  | num (x : Float)
  | str (s : String)
  | arr (xs : Array JVal)
  | obj (kvs : Array (String × JVal))
  deriving Repr, Inhabited

namespace JVal

def get? (v : JVal) (key : String) : Option JVal :=
  match v with
  | .obj kvs => (kvs.find? fun kv => kv.1 == key).map (·.2)
  | _ => none

def asStr? : JVal → Option String
  | .str s => some s
  | _ => none

def asNum? : JVal → Option Float
  | .num x => some x
  | _ => none

def asBool? : JVal → Option Bool
  | .bool b => some b
  | _ => none

def asArr? : JVal → Option (Array JVal)
  | .arr xs => some xs
  | _ => none

def asVec3? (v : JVal) : Option Vec3 := do
  let xs ← v.asArr?
  if xs.size < 3 then none
  else
    let x ← xs[0]!.asNum?
    let y ← xs[1]!.asNum?
    let z ← xs[2]!.asNum?
    some ⟨x, y, z⟩

end JVal

private structure PState where
  chars : Array Char
  pos   : Nat

private def PState.peek (st : PState) : Option Char := st.chars[st.pos]?

private def PState.skipWs (st : PState) : PState :=
  let rec go (i : Nat) : Nat :=
    if h : i < st.chars.size then
      let c := st.chars[i]
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then go (i + 1) else i
    else i
  { st with pos := go st.pos }

private def parseFloatStr (s : String) : Option Float :=
  let cs := s.toList
  let (neg, cs) := match cs with | '-' :: r => (true, r) | '+' :: r => (false, r) | _ => (false, cs)
  let intPart := cs.takeWhile Char.isDigit
  let r1 := cs.drop intPart.length
  let (fracPart, r2) := match r1 with
    | '.' :: r =>
      let fp := r.takeWhile Char.isDigit
      (fp, r.drop fp.length)
    | _ => ([], r1)
  if intPart.isEmpty && fracPart.isEmpty then none
  else
    let (expNeg, expDigits) := match r2 with
      | 'e' :: '+' :: r | 'E' :: '+' :: r => (false, r.takeWhile Char.isDigit)
      | 'e' :: '-' :: r | 'E' :: '-' :: r => (true, r.takeWhile Char.isDigit)
      | 'e' :: r | 'E' :: r => (false, r.takeWhile Char.isDigit)
      | _ => (false, [])
    let digitsToFloat (ds : List Char) : Float :=
      ds.foldl (fun acc c => acc * 10.0 + (c.toNat - 48).toFloat) 0.0
    let mant := digitsToFloat intPart + digitsToFloat fracPart / Float.pow 10.0 fracPart.length.toFloat
    let expVal := expDigits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
    let scaled :=
      if expVal == 0 then mant
      else if expNeg then mant / Float.pow 10.0 expVal.toFloat
      else mant * Float.pow 10.0 expVal.toFloat
    some (if neg then -scaled else scaled)

private partial def parseStringRaw (st : PState) : Except String (String × PState) := do
  if st.peek != some '"' then throw "expected '\"'"
  let rec go (i : Nat) (acc : List Char) : Except String (String × PState) :=
    if h : i < st.chars.size then
      let c := st.chars[i]
      if c == '"' then .ok (String.ofList acc.reverse, { st with pos := i + 1 })
      else if c == '\\' then
        if h2 : i + 1 < st.chars.size then
          let esc := st.chars[i + 1]
          let ch := match esc with
            | '"'  => '"'  | '\\' => '\\' | '/'  => '/'
            | 'n'  => '\n' | 'r'  => '\r' | 't'  => '\t'
            | _    => esc
          go (i + 2) (ch :: acc)
        else throw "unterminated escape"
      else go (i + 1) (c :: acc)
    else throw "unterminated string"
  go (st.pos + 1) []

private partial def parseVal (st : PState) : Except String (JVal × PState) := do
  let st := st.skipWs
  match st.peek with
  | none => throw "unexpected EOF"
  | some '"' =>
    let (s, st) ← parseStringRaw st
    return (.str s, st)
  | some '{' =>
    let mut st := { st with pos := st.pos + 1 }.skipWs
    let mut kvs : Array (String × JVal) := #[]
    if st.peek == some '}' then return (.obj kvs, { st with pos := st.pos + 1 })
    repeat
      let (k, st1) ← parseStringRaw st.skipWs
      let st2 := st1.skipWs
      if st2.peek != some ':' then throw "expected ':'"
      let (v, st3) ← parseVal { st2 with pos := st2.pos + 1 }
      kvs := kvs.push (k, v)
      let st4 := st3.skipWs
      match st4.peek with
      | some ',' => st := { st4 with pos := st4.pos + 1 }.skipWs
      | some '}' => return (.obj kvs, { st4 with pos := st4.pos + 1 })
      | _ => throw "expected ',' or '}'"
    return (.obj kvs, st)
  | some '[' =>
    let mut st := { st with pos := st.pos + 1 }.skipWs
    let mut xs : Array JVal := #[]
    if st.peek == some ']' then return (.arr xs, { st with pos := st.pos + 1 })
    repeat
      let (v, st1) ← parseVal st
      xs := xs.push v
      let st2 := st1.skipWs
      match st2.peek with
      | some ',' => st := { st2 with pos := st2.pos + 1 }.skipWs
      | some ']' => return (.arr xs, { st2 with pos := st2.pos + 1 })
      | _ => throw "expected ',' or ']'"
    return (.arr xs, st)
  | some 't' =>
    if st.pos + 4 ≤ st.chars.size then return (.bool true, { st with pos := st.pos + 4 })
    else throw "invalid literal"
  | some 'f' =>
    if st.pos + 5 ≤ st.chars.size then return (.bool false, { st with pos := st.pos + 5 })
    else throw "invalid literal"
  | some 'n' =>
    if st.pos + 4 ≤ st.chars.size then return (.null, { st with pos := st.pos + 4 })
    else throw "invalid literal"
  | some c =>
    if c == '-' || c == '+' || c.isDigit then
      let rec scan (i : Nat) : Nat :=
        if h : i < st.chars.size then
          let ch := st.chars[i]
          if ch.isDigit || ch == '.' || ch == '-' || ch == '+' || ch == 'e' || ch == 'E' then
            scan (i + 1)
          else i
        else i
      let stop := scan st.pos
      let tok := String.ofList (st.chars.extract st.pos stop).toList
      match parseFloatStr tok with
      | some x => return (.num x, { st with pos := stop })
      | none => throw s!"invalid number: {tok}"
    else throw s!"unexpected char: {c}"

/-- Parse a JSON text into `JVal`. -/
def parseJson (s : String) : Except String JVal := do
  let (v, _) ← parseVal { chars := s.toList.toArray, pos := 0 }
  return v

/-- Parse a JSON `InputEvent` message matching `docs/SCENE_IR_V1.md` §4.2. -/
def parseInputEventJson (s : String) : Except String InputEvent := do
  let j ← parseJson s
  let some op := (j.get? "op").bind JVal.asStr? | throw "missing 'op' string"
  match op with
  | "dragHandle" =>
    let id := ((j.get? "id").bind JVal.asNum?).getD 0.0
    let some pos := (j.get? "pos").bind JVal.asVec3? | throw "dragHandle missing pos[3]"
    return .dragHandle id.toUInt32 pos
  | "tick" =>
    let dt := ((j.get? "dt").bind JVal.asNum?).getD 0.016
    let t := ((j.get? "t").bind JVal.asNum?).getD 0.0
    return .tick dt t
  | "evalScript" =>
    let alg := ((j.get? "algebra").bind JVal.asStr?).getD "PGA3"
    let code := ((j.get? "code").bind JVal.asStr?).getD ""
    return .evalScript alg code
  | "evalSurface" =>
    let expr := ((j.get? "expr").bind JVal.asStr?).getD "sin(x*2+t)*cos(y*2)"
    let bArr := ((j.get? "bounds").bind JVal.asArr?).getD #[]
    let minX := (bArr[0]?.bind JVal.asNum?).getD (-2.0)
    let maxX := (bArr[1]?.bind JVal.asNum?).getD 2.0
    let minY := (bArr[2]?.bind JVal.asNum?).getD (-2.0)
    let maxY := (bArr[3]?.bind JVal.asNum?).getD 2.0
    let gridN := ((j.get? "gridN").bind JVal.asNum?).getD 48.0
    return .evalSurface expr minX maxX minY maxY gridN.toUInt32
  | "editCoeff" =>
    let entryIdx := ((j.get? "entryIdx").bind JVal.asNum?).getD 0.0
    let bladeIdx := ((j.get? "bladeIdx").bind JVal.asNum?).getD 0.0
    let val := ((j.get? "val").bind JVal.asNum?).getD 0.0
    return .editCoeff entryIdx.toUInt32 bladeIdx.toUInt32 val
  | "loadPreset" =>
    let id := ((j.get? "id").bind JVal.asStr?).getD "pga3d_slicing"
    return .loadPreset id
  | "wedgeGesture" =>
    let idA := ((j.get? "idA").bind JVal.asNum?).getD 0.0
    let idB := ((j.get? "idB").bind JVal.asNum?).getD 0.0
    let dirA := ((j.get? "dirA").bind JVal.asVec3?).getD Vec3.zero
    let dirB := ((j.get? "dirB").bind JVal.asVec3?).getD Vec3.zero
    let holdA := ((j.get? "holdA").bind JVal.asBool?).getD false
    let holdB := ((j.get? "holdB").bind JVal.asBool?).getD false
    let isPreview := ((j.get? "isPreview").bind JVal.asBool?).getD false
    return .wedgeGesture idA.toUInt32 idB.toUInt32 dirA dirB holdA holdB isPreview
  | "snapshot" => return .snapshot
  | "wedgeAction" =>
    let act := ((j.get? "action").bind JVal.asStr?).getD "reset"
    let arg := ((j.get? "arg").bind JVal.asNum?).getD 0.0
    let k : WedgeActionKind := match act with
      | "undo"     => .undo
      | "reset"    => .reset
      | "next"     => .next
      | "prev"     => .prev
      | "toggle3D" => .toggle3D
      | "hint"     => .hint
      | "goto"     => .gotoLevel
      | _          => .reset
    return .wedgeAction k arg.toUInt32
  | "calcKey" =>
    let key := ((j.get? "key").bind JVal.asStr?).getD ""
    return .calcKey key
  | "calcEval" =>
    let mode := ((j.get? "mode").bind JVal.asStr?).getD "STA"
    let expr := ((j.get? "expr").bind JVal.asStr?).getD "0"
    return .calcEval mode expr
  | "setCamera" =>
    let motArr := ((j.get? "motor").bind JVal.asArr?).getD #[]
    let mut fa := FloatArray.emptyWithCapacity 8
    for v in motArr do
      fa := fa.push (v.asNum?.getD 0.0)
    let mot := if fa.size ≥ 8 then Motor3.ofFloatArray fa else Motor3.identity
    let fov := ((j.get? "fovDeg").bind JVal.asNum?).getD 45.0
    let dist := ((j.get? "distance").bind JVal.asNum?).getD 5.2
    return .setCamera mot fov dist
  | "slicePlane" =>
    let motArr := ((j.get? "motor").bind JVal.asArr?).getD #[]
    let mut fa := FloatArray.emptyWithCapacity 8
    for v in motArr do
      fa := fa.push (v.asNum?.getD 0.0)
    return .slicePlane (if fa.size ≥ 8 then Motor3.ofFloatArray fa else Motor3.identity)
  | "evalEquations" =>
    let eqsArr := ((j.get? "equations").bind JVal.asArr?).getD #[]
    let eqs := eqsArr.filterMap JVal.asStr?
    let bArr := ((j.get? "bounds").bind JVal.asArr?).getD #[]
    let minX := (bArr[0]?.bind JVal.asNum?).getD (-2.0)
    let maxX := (bArr[1]?.bind JVal.asNum?).getD 2.0
    let minY := (bArr[2]?.bind JVal.asNum?).getD (-2.0)
    let maxY := (bArr[3]?.bind JVal.asNum?).getD 2.0
    let gridN := ((j.get? "gridN").bind JVal.asNum?).getD 48.0
    return .evalEquations eqs minX maxX minY maxY gridN.toUInt32
  | "evalImplicit" =>
    let expr := ((j.get? "expr").bind JVal.asStr?).getD "cos(x*2)*sin(y*2)+cos(y*2)*sin(z*2)+cos(z*2)*sin(x*2)"
    let gpuRay := ((j.get? "gpuRaymarch").bind JVal.asBool?).getD false
    let bound := ((j.get? "bound").bind JVal.asNum?).getD 1.6
    let gridN := ((j.get? "gridN").bind JVal.asNum?).getD 18.0
    return .evalImplicit expr gpuRay bound gridN.toUInt32
  | "evalParametric" =>
    let fx := ((j.get? "fx").bind JVal.asStr?).getD "(1.1 + 0.42*cos(v))*cos(u)"
    let fy := ((j.get? "fy").bind JVal.asStr?).getD "0.42*sin(v)"
    let fz := ((j.get? "fz").bind JVal.asStr?).getD "(1.1 + 0.42*cos(v))*sin(u)"
    let uArr := ((j.get? "uBounds").bind JVal.asArr?).getD #[]
    let vArr := ((j.get? "vBounds").bind JVal.asArr?).getD #[]
    let uMin := (uArr[0]?.bind JVal.asNum?).getD 0.0
    let uMax := (uArr[1]?.bind JVal.asNum?).getD 6.283185307179586
    let vMin := (vArr[0]?.bind JVal.asNum?).getD 0.0
    let vMax := (vArr[1]?.bind JVal.asNum?).getD 6.283185307179586
    let nu := ((j.get? "nu").bind JVal.asNum?).getD 40.0
    let nv := ((j.get? "nv").bind JVal.asNum?).getD 24.0
    return .evalParametric fx fy fz uMin uMax vMin vMax nu.toUInt32 nv.toUInt32
  | "wedgeTutorial" =>
    let id := ((j.get? "id").bind JVal.asStr?).getD "T1"
    return .wedgeTutorial id
  | "wedgeRandom" =>
    let dim := ((j.get? "dim").bind JVal.asNum?).getD 2.0
    let diff := ((j.get? "difficulty").bind JVal.asNum?).getD 1.0
    let seed := ((j.get? "seed").bind JVal.asNum?).getD 0.0
    return .wedgeRandom (dim ≥ 2.5) diff.toUInt32 seed.toUInt64
  | "setParam" =>
    let some name := (j.get? "name").bind JVal.asStr? | throw "setParam missing 'name' string"
    let val :=
      match (j.get? "value").bind JVal.asNum? with
      | some v => v
      | none   => ((j.get? "val").bind JVal.asNum?).getD 0.0
    return .setParam name val
  | _ => throw s!"unknown InputEvent op: {op}"

end Grassmann.Scene.Json
