import Grassmann.Scene.Types
import Grassmann.Eval.ImplicitExpr

/-!
# 100% Strictly `Init`-Only Live GPU Shader Compiler (GLSL 300 es + WGSL + Metal MSL)

Zero `Lean.*`, zero `Std.*`, zero `DirectSum` — compiles straight into both the tiny
2.5 MB standalone macOS/visionOS dylib AND the Lean 4.36 → C → Emscripten WASM bundle,
generating pixel-perfect sphere-tracing GPU shaders at runtime in `< 1 ms`!

Two unified compilers sharing one studio-grade raymarching template (dual-light PBR +
Fresnel rim + soft AO + exact `gl_FragDepth` depth compositing):
1. **Pure-`Init` Clifford Algebra `Cl(p, q, r)` OPNS / IPNS Compiler** (`compileGaOpnsBundle`):
   - Computes exact exterior (`∧` OPNS) & metric left-contraction (`⌋` IPNS) blade products
     directly via bitmask Clifford arithmetic (supporting Euclidean `R3`, Projective `PGA2/3`,
     Conformal Witt `CGA2/3`, Spacetime `STA`, and Conic `CSGA`).
   - Emits verbatim drop-in shaders matching:
     - **WebGL2 / Three.js `THREE.GLSL3`** (`web/src/render/materials.ts` `OpnsShaderCache`:
       `in vec3 vWorldPos`, `uCoeffs[64]`, `uColor`, `uThresh`, `uMaxSteps`, `uStepSize`,
       `uSimTime`, `uResolution`, `uInvViewProj`, `gl_FragDepth`)
     - **WebGPU `WGSL`** (`@fragment fn fs_main`, 16-byte uniform-aligned `array<vec4<f32>, 16>`)
     - **Apple Metal `MSL`** (`LeanCalculator/Sources/Spatial3D/OPNSMetalRenderer.swift`:
       exact 96-byte `struct OpnsUniforms` + `float blade[64]`, `inline float product_len`,
       AND direct `kernel void gsir_lean_opns_compute`!)
2. **Live User-Typed `ImplicitExpr` → GPU Raymarcher Compiler** (`compileImplicitExprToGpu`):
   - Compiles ANY user-typed 3D implicit equation `f(x, y, z, t) = 0` from
     `Grassmann.Eval.ImplicitExpr.Expr` directly into GLSL 300 es, WGSL, and Metal MSL
     sphere-tracing shaders with sign-change bisection refinement for razor-sharp
     60 FPS infinite-resolution rendering on Web & Apple Vision Pro!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.Codegen.GPUInit

open Grassmann.Scene Grassmann.Eval.ImplicitExpr

/-- Target GPU shading language. -/
inductive GpuTarget where
  | glsl
  | wgsl
  | msl
  deriving DecidableEq, Repr, Inhabited

/-- Lightweight `Init`-only Clifford algebra specification for GPU shader compilation. -/
structure AlgSpec where
  name          : String
  p             : Nat
  q             : Nat
  r             : Nat
  conformalWitt : Bool := false
  deriving Repr, Inhabited

namespace AlgSpec
def dim (a : AlgSpec) : Nat := a.p + a.q + a.r
def r3   : AlgSpec := { name := "R3",   p := 3, q := 0, r := 0 }
def pga2 : AlgSpec := { name := "PGA2", p := 2, q := 0, r := 1 }
def pga3 : AlgSpec := { name := "PGA3", p := 3, q := 0, r := 1 }
def cga2 : AlgSpec := { name := "CGA2", p := 3, q := 1, r := 0, conformalWitt := true }
def cga3 : AlgSpec := { name := "CGA3", p := 4, q := 1, r := 0, conformalWitt := true }
def sta  : AlgSpec := { name := "STA",  p := 3, q := 1, r := 0 }
end AlgSpec

/-! ## 1. Pure-`Init` Bitmask Clifford Algebra Engine -/

private def popcount (m : Nat) : Nat :=
  let rec go (x acc fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 => if x == 0 then acc else go (x >>> 1) (acc + (x &&& 1)) f
  go m 0 32

/-- Swap sign `(-1)^swaps` for reordering single vector bit `1 <<< i` before blade `bMask`. -/
private def swapSignBit (i bMask : Nat) : Int :=
  let below := popcount (bMask &&& ((1 <<< i) - 1))
  if below % 2 == 0 then 1 else -1

/-- Basis vector metric `e_i² ∈ {-1, 0, +1}` for non-Witt diagonal `AlgSpec`.
Follows `ganja.js` / `PGA` ordering: degenerate `r` bits first (`0`), then `p` (`+1`), then `q` (`-1`).
For `STA` (`p=3, q=1, r=0`, `-+++` convention), bit 0 is `-1` and bits `1..3` are `+1`. -/
private def diagMetric (alg : AlgSpec) (i : Nat) : Int :=
  if alg.name == "STA" then
    if i == 0 then -1 else 1
  else if i < alg.r then 0
  else if i < alg.r + alg.p then 1
  else -1

/-- Enumerate all grade-`k` basis blade bitmasks in canonical bitmask order (`0 .. 2^n - 1`). -/
private def gradeBlades (n k : Nat) : Array Nat := Id.run do
  let total := 1 <<< n
  let mut out : Array Nat := #[]
  for m in [:total] do
    if popcount m == k then out := out.push m
  return out

/-- Default 3D point lifting expressions `up(x, y, z)` for standard algebras:
- Conformal Witt `CGA3` (`e∞, e∅, e1, e2, e3`): `[0.5*(x²+y²+z²), 1.0, x, y, z]`
- Conformal Witt `CGA2` (`e∞, e∅, e1, e2`):     `[0.5*(x²+y²), 1.0, x, y]`
- Projective `PGA3` (`e0, e1, e2, e3`):         `[1.0, x, y, z]`
- Euclidean `R3` (`e1, e2, e3`):                `[x, y, z]` -/
def defaultUpExprs (alg : AlgSpec) : Array String :=
  let n := alg.dim
  if alg.conformalWitt && n == 5 then
    #["0.5*(x*x+y*y+z*z)", "1.0", "x", "y", "z"]
  else if alg.conformalWitt && n == 4 then
    #["0.5*(x*x+y*y)", "1.0", "x", "y"]
  else if alg.r == 1 && n == 4 then
    #["1.0", "x", "y", "z"]
  else if alg.r == 1 && n == 3 then
    #["1.0", "x", "y"]
  else if n == 4 then
    #["0.0", "x", "y", "z"]
  else
    (Array.range n).map fun i =>
      match i with | 0 => "x" | 1 => "y" | 2 => "z" | _ => "0.0"

private def digitChar (d : Nat) : Char :=
  Char.ofNat ('0'.toNat + (d % 10))

/-- Format a GPU float literal to 9 significant digits (full IEEE-754 float32
round-trip precision, e.g. `1.0`, `-0.5`, `0.5000004`, `2.0e-7`, `1.0e8`),
avoiding bare integer syntax, avoiding 6-decimal precision collapse
(`0.5000004` vs `0.5000001`), and never underflowing tiny float32 constants
(`0.0000001` → `1.0e-7`). Pure integer digit extraction guarantees byte-for-byte
identical GLSL 300 es, WebGPU WGSL, and Apple Metal MSL across Native C ABI,
`ga-server`, and WASM. -/
private def fmtFloat (v : Float) : String :=
  if v.isNaN || v == 0.0 then "0.0"
  else if v.isInf then (if v < 0.0 then "-3.4e38" else "3.4e38")
  else
    let sign := if v < 0.0 then "-" else ""
    -- Clamp nonzero extremes to normal IEEE-754 float32 range so WGSL/GLSL/MSL
    -- never reject oversized literals (> FLT_MAX) or flush subnormals to 0.0f (FTZ).
    let av := max 1e-35 (min 3.4e38 (Float.abs v))
    let exp0 : Int := (Float.floor (Float.log av / Float.log 10.0)).toInt64.toInt
    Id.run do
      let mut e := exp0
      let mut m :=
        if e < 0 then av * Float.pow 10.0 (Float.ofInt (-e))
        else av / Float.pow 10.0 (Float.ofInt e)
      for _ in [:8] do
        if m >= 10.0 then
          m := m / 10.0
          e := e + 1
        else if m < 1.0 && m > 0.0 then
          m := m * 10.0
          e := e - 1
      let mut sc : Nat := (Float.floor (m * 100000000.0 + 0.5)).toUInt64.toNat
      if sc >= 1000000000 then
        sc := 100000000
        e := e + 1
      else if sc < 100000000 then
        sc := 100000000
      -- Extract 9 decimal digits msb-first (ds[0]..ds[8]) via pure Nat arithmetic.
      let mut ds : Array Nat := Array.replicate 9 0
      let mut tmp := sc
      for k in [:9] do
        ds := ds.set! (8 - k) (tmp % 10)
        tmp := tmp / 10
      -- Last non-zero digit index in [0..8]
      let mut lastNz : Nat := 0
      for k in [:9] do
        if ds[k]! != 0 then lastNz := k
      let mut out := sign
      if e >= -4 && e < 7 then
        if e >= 0 then
          let intCount := e.toNat + 1
          for k in [:intCount] do
            out := out.push (digitChar ds[k]!)
          out := out.push '.'
          if lastNz < intCount then
            out := out.push '0'
          else
            for k in [intCount:lastNz + 1] do
              out := out.push (digitChar ds[k]!)
        else
          out := out ++ "0."
          let leadZeros := ((-e).toNat) - 1
          for _ in [:leadZeros] do
            out := out.push '0'
          for k in [:lastNz + 1] do
            out := out.push (digitChar ds[k]!)
      else
        out := out.push (digitChar ds[0]!)
        out := out.push '.'
        if lastNz == 0 then
          out := out.push '0'
        else
          for k in [1:lastNz + 1] do
            out := out.push (digitChar ds[k]!)
        out := out.push 'e'
        if e < 0 then
          out := out ++ s!"-{(-e).toNat}"
        else
          out := out ++ s!"{e.toNat}"
      return out

/-- Compute an FNV-1a 64-bit hex cache hash string for `OpnsShaderSource.hash`. -/
private def hashShaderTag (tag : String) (payload : String) : String := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for b in payload.toUTF8.data do
    h := (h ^^^ b.toUInt64) * 1099511628211
  return s!"{tag}_{h}"

/-! ## 2. Straight-Line Unrolled OPNS / IPNS `product_len` Body Emitter -/

/-- Compute sparse `(outSlot, vecIdx, bladeIdx, sign)` entries for `up(p) ∧ b` (OPNS)
or `up(p) ⌋ b` (IPNS) directly in pure `Init` (zero `DirectSum` imports!). -/
private def buildNullSpaceTerms (alg : AlgSpec) (grade : Nat) (isIPNS : Bool) :
    Except String (Nat × Nat × Array (Array (Nat × Nat × Int))) := do
  let n := alg.dim
  if n == 0 || n > 6 then
    throw s!"Unsupported algebra dimension n={n} for real-time GPU OPNS (expected 1..6)"
  let outGrade := if isIPNS then (if grade ≥ 1 then grade - 1 else 0) else grade + 1
  if grade > n || outGrade > n then
    throw s!"Invalid grade={grade} for n={n} (isIPNS={isIPNS})"
  let inBlades := gradeBlades n grade
  let outBlades := gradeBlades n outGrade
  let findOutSlot (mask : Nat) : Option Nat :=
    outBlades.findIdx? (· == mask)
  let mut buckets : Array (Array (Nat × Nat × Int)) := Array.replicate outBlades.size #[]
  for j in [:inBlades.size] do
    let bMask := inBlades[j]!
    for i in [:n] do
      let bitI := 1 <<< i
      if !isIPNS then
        -- Exterior product (OPNS): metric-independent `e_i ∧ bMask`
        if (bMask &&& bitI) == 0 then
          let outMask := bMask ||| bitI
          match findOutSlot outMask with
          | some ic =>
            let sgn := swapSignBit i bMask
            buckets := buckets.set! ic (buckets[ic]!.push (i, j, sgn))
          | none => pure ()
      else
        -- Left contraction (IPNS): `e_i ⌋ bMask`
        if alg.conformalWitt && i < 2 then
          -- Witt null pair: e0 · e1 = e1 · e0 = -1
          let partner := 1 - i
          let bitP := 1 <<< partner
          if (bMask &&& bitP) != 0 then
            let outMask := bMask ^^^ bitP
            match findOutSlot outMask with
            | some ic =>
              let sgn := -(swapSignBit partner bMask)
              buckets := buckets.set! ic (buckets[ic]!.push (i, j, sgn))
            | none => pure ()
        else
          let m := diagMetric alg i
          if m != 0 && (bMask &&& bitI) != 0 then
            let outMask := bMask ^^^ bitI
            match findOutSlot outMask with
            | some ic =>
              let sgn := m * swapSignBit i bMask
              buckets := buckets.set! ic (buckets[ic]!.push (i, j, sgn))
            | none => pure ()
  return (inBlades.size, outBlades.size, buckets)

private def emitTermSum (terms : Array (Nat × Nat × Int)) (fmtB : Nat → String) : String := Id.run do
  if terms.isEmpty then return "0.0"
  let mut acc := ""
  for k in [:terms.size] do
    let (vi, bi, sgn) := terms[k]!
    let prod := s!"u{vi} * {fmtB bi}"
    if k == 0 then
      acc := if sgn < 0 then s!"-({prod})" else prod
    else
      acc := if sgn < 0 then s!"{acc} - {prod}" else s!"{acc} + {prod}"
  return acc

private def emitProductLenBody (target : GpuTarget) (alg : AlgSpec) (grade : Nat)
    (isIPNS : Bool) (upExprs : Array String := defaultUpExprs alg) :
    Except String (Nat × String) := do
  let (inDim, outDim, buckets) ← buildNullSpaceTerms alg grade isIPNS
  let declF := match target with | .wgsl => "let" | _ => "float"
  let varSum := match target with | .wgsl => "var sum: f32 = 0.0;" | _ => "float sum = 0.0;"
  let fmtB : Nat → String :=
    match target with
    | .wgsl => fun j => s!"b[{j / 4}][{j % 4}]"
    | _     => fun j => s!"b[{j}]"
  let mut lines : Array String := #[]
  for i in [:alg.dim] do
    let expr := upExprs.getD i "0.0"
    lines := lines.push s!"  {declF} u{i} = {expr};"
  lines := lines.push s!"  {varSum}"
  for ic in [:outDim] do
    if !buckets[ic]!.isEmpty then
      let sumExpr := emitTermSum buckets[ic]! fmtB
      lines := lines.push s!"  {declF} c{ic} = {sumExpr};"
      lines := lines.push s!"  sum += c{ic} * c{ic};"
  lines := lines.push "  return sqrt(max(0.0, sum));"
  return (inDim, "\n".intercalate lines.toList)

/-! ## 3. Drop-In GLSL 300 es, WGSL & Metal MSL Shaders for GA OPNS/IPNS -/

/-- Emit a complete **GLSL 300 es (`THREE.GLSL3`)** sphere-tracing fragment shader matching
`web/src/render/materials.ts` `OpnsShaderCache` verbatim (`uCoeffs[64]`, `uColor`, `uThresh`,
`uMaxSteps`, `uStepSize`, `uSimTime`, `uResolution`, `uInvViewProj`, `gl_FragDepth`). -/
def emitGaOpnsGlsl (alg : AlgSpec) (grade : Nat) (isIPNS : Bool := false) :
    Except String String := do
  let (_, body) ← emitProductLenBody .glsl alg grade isIPNS
  let mode := if isIPNS then "IPNS" else "OPNS"
  return s!"#version 300 es
// Auto-generated by Grassmann.Codegen.GPUInit ({mode}, {alg.name}, grade={grade})
precision highp float;
in vec3 vWorldPos;
in vec3 vLocalPos;
out vec4 fragColor;

uniform vec4 uColor;
uniform float uCoeffs[64];
uniform int uGrade;
uniform float uThresh;
uniform int uMaxSteps;
uniform float uStepSize;
uniform int uIsIPNS;
uniform float uSimTime;
uniform vec2 uResolution;
uniform mat4 uInvViewProj;
uniform mat4 projectionMatrix;

float product_len(vec3 p, float b[64]) \{
  float x = p.x; float y = p.y; float z = p.z;
{body}
}

vec2 intersectSphere(vec3 ro, vec3 rd, float r) \{
  float b = dot(ro, rd);
  float c = dot(ro, ro) - r * r;
  float h = b * b - c;
  if (h < 0.0) return vec2(1.0, -1.0);
  h = sqrt(h);
  return vec2(max(0.0, -b - h), -b + h);
}

void main() \{
  vec3 ro = cameraPosition;
  vec3 rd = normalize(vWorldPos - cameraPosition);
  vec2 hitRange = intersectSphere(ro, rd, 2.6);
  if (hitRange.y < hitRange.x) discard;

  float t = hitRange.x;
  float tMax = hitRange.y;
  float thresh = max(0.002, uThresh);
  float stepBase = max(0.004, uStepSize);
  int steps = clamp(uMaxSteps, 16, 128);
  float lastd = 1e4;
  bool hit = false;
  vec3 pos = ro + rd * t;

  for (int i = 0; i < 128; i++) \{
    if (i >= steps || t > tMax) break;
    pos = ro + rd * t;
    float d = product_len(pos, uCoeffs);
    float stepLen = clamp(stepBase * (1.0 + 42.0 * d), stepBase * 0.5, 0.14);
    if (d < thresh) \{
      float a = clamp((lastd - thresh) / max(1e-5, lastd - d), 0.0, 1.0);
      t -= (1.0 - a) * stepLen;
      pos = ro + rd * t;
      hit = true;
      break;
    }
    lastd = d;
    t += stepLen;
  }
  if (!hit) discard;

  float h = 0.0015;
  vec3 g = vec3(
    product_len(pos + vec3(h,0.0,0.0), uCoeffs) - product_len(pos - vec3(h,0.0,0.0), uCoeffs),
    product_len(pos + vec3(0.0,h,0.0), uCoeffs) - product_len(pos - vec3(0.0,h,0.0), uCoeffs),
    product_len(pos + vec3(0.0,0.0,h), uCoeffs) - product_len(pos - vec3(0.0,0.0,h), uCoeffs)
  );
  vec3 N = length(g) > 1e-6 ? normalize(g) : vec3(0.0, 1.0, 0.0);
  if (dot(N, -rd) < 0.0) N = -N;
  vec3 V = -rd;
  vec3 Lk = normalize(vec3(0.55, 0.78, 0.38));
  vec3 Lr = normalize(vec3(-0.62, 0.36, -0.68));
  float diffKey = max(0.0, dot(N, Lk));
  float diffRim = max(0.0, dot(N, Lr));
  float spec = pow(max(0.0, dot(N, normalize(Lk + V))), 48.0);
  float fres = pow(1.0 - max(0.0, dot(N, V)), 3.0);
  float ao = clamp(0.65 + 0.35 * product_len(pos + N * 0.08, uCoeffs) / max(0.05, thresh * 10.0), 0.45, 1.0);
  vec3 lit = uColor.rgb * ao * (0.24 + 0.74 * diffKey)
           + vec3(0.52, 0.85, 1.0) * (0.30 * diffRim + 0.42 * fres)
           + vec3(1.0, 0.97, 0.92) * (0.55 * spec);

  vec4 clipPos = projectionMatrix * viewMatrix * vec4(pos, 1.0);
  gl_FragDepth = clamp((clipPos.z / clipPos.w) * 0.5 + 0.5, 0.0, 1.0);
  fragColor = vec4(clamp(lit, 0.0, 1.0), clamp(uColor.a, 0.25, 0.98));
}
"

/-- Emit a complete **WebGPU `WGSL`** sphere-tracing fragment shader (16-byte `vec4<f32>`
uniform alignment). -/
def emitGaOpnsWgsl (alg : AlgSpec) (grade : Nat) (isIPNS : Bool := false) :
    Except String String := do
  let (_, body) ← emitProductLenBody .wgsl alg grade isIPNS
  let mode := if isIPNS then "IPNS" else "OPNS"
  return s!"// Auto-generated by Grassmann.Codegen.GPUInit ({mode}, {alg.name}, grade={grade})
struct OpnsUniforms \{
  camPos   : vec4<f32>,
  camRight : vec4<f32>,
  camUp    : vec4<f32>,
  camFwd   : vec4<f32>,
  color    : vec4<f32>,
  params   : vec4<f32>, // x=thresh, y=stepSize, z=maxSteps, w=simTime
  blade    : array<vec4<f32>, 16>, // 64 blade floats, 16-byte uniform aligned
};
@group(0) @binding(0) var<uniform> u : OpnsUniforms;

fn product_len(p: vec3<f32>, b: array<vec4<f32>, 16>) -> f32 \{
  let x = p.x; let y = p.y; let z = p.z;
{body}
}

@fragment
fn fs_main(@location(0) uv: vec2<f32>) -> @location(0) vec4<f32> \{
  let ndc = uv * 2.0 - vec2<f32>(1.0, 1.0);
  let ro = u.camPos.xyz;
  let rd = normalize(u.camFwd.xyz + ndc.x * u.camRight.xyz + ndc.y * u.camUp.xyz);
  let bDot = dot(ro, rd);
  let cDot = dot(ro, ro) - 6.76;
  let disc = bDot * bDot - cDot;
  if (disc < 0.0) \{ discard; }
  let sqD = sqrt(disc);
  var t = max(0.0, -bDot - sqD);
  let tMax = -bDot + sqD;
  let thresh = max(0.002, u.params.x);
  let stepBase = max(0.004, u.params.y);
  let maxSteps = clamp(i32(u.params.z), 16, 128);
  var lastd: f32 = 10000.0;
  var hit: bool = false;
  var pos = ro + rd * t;
  for (var i: i32 = 0; i < 128; i = i + 1) \{
    if (i >= maxSteps || t > tMax) \{ break; }
    pos = ro + rd * t;
    let d = product_len(pos, u.blade);
    let stepLen = clamp(stepBase * (1.0 + 42.0 * d), stepBase * 0.5, 0.14);
    if (d < thresh) \{
      let a = clamp((lastd - thresh) / max(1e-5, lastd - d), 0.0, 1.0);
      t = t - (1.0 - a) * stepLen;
      pos = ro + rd * t;
      hit = true;
      break;
    }
    lastd = d;
    t = t + stepLen;
  }
  if (!hit) \{ discard; }
  let h: f32 = 0.0015;
  let g = vec3<f32>(
    product_len(pos + vec3<f32>(h,0.0,0.0), u.blade) - product_len(pos - vec3<f32>(h,0.0,0.0), u.blade),
    product_len(pos + vec3<f32>(0.0,h,0.0), u.blade) - product_len(pos - vec3<f32>(0.0,h,0.0), u.blade),
    product_len(pos + vec3<f32>(0.0,0.0,h), u.blade) - product_len(pos - vec3<f32>(0.0,0.0,h), u.blade)
  );
  var N = select(vec3<f32>(0.0, 1.0, 0.0), normalize(g), length(g) > 1e-6);
  if (dot(N, -rd) < 0.0) \{ N = -N; }
  let V = -rd;
  let Lk = normalize(vec3<f32>(0.55, 0.78, 0.38));
  let Lr = normalize(vec3<f32>(-0.62, 0.36, -0.68));
  let diffKey = max(0.0, dot(N, Lk));
  let diffRim = max(0.0, dot(N, Lr));
  let spec = pow(max(0.0, dot(N, normalize(Lk + V))), 48.0);
  let fres = pow(1.0 - max(0.0, dot(N, V)), 3.0);
  let lit = u.color.rgb * (0.24 + 0.74 * diffKey)
          + vec3<f32>(0.52, 0.85, 1.0) * (0.30 * diffRim + 0.42 * fres)
          + vec3<f32>(1.0, 0.97, 0.92) * (0.55 * spec);
  return vec4<f32>(clamp(lit, vec3<f32>(0.0), vec3<f32>(1.0)), clamp(u.color.a, 0.25, 0.98));
}
"

/-- Emit a complete **Apple Metal `MSL`** compute shader matching
`LeanCalculator/Sources/Spatial3D/OPNSMetalRenderer.swift` verbatim (`struct OpnsUniforms`,
`inline float product_len(float3, constant float*)`, AND `kernel void gsir_lean_opns_compute`). -/
def emitGaOpnsMsl (alg : AlgSpec) (grade : Nat) (isIPNS : Bool := false) :
    Except String String := do
  let (_, body) ← emitProductLenBody .msl alg grade isIPNS
  let mode := if isIPNS then "IPNS" else "OPNS"
  return s!"// Auto-generated by Grassmann.Codegen.GPUInit ({mode}, {alg.name}, grade={grade})
#include <metal_stdlib>
using namespace metal;

struct OpnsUniforms \{
  float4 camPos;
  float4 camRight;
  float4 camUp;
  float4 camFwd;
  float4 color;
  float4 params; // x=thresh, y=stepSize, z=maxSteps, w=simTime
  float  blade[64];
};

inline float product_len(float3 p, constant float* b) \{
  float x = p.x; float y = p.y; float z = p.z;
{body}
}

kernel void gsir_lean_opns_compute(
    texture2d<half, access::write> outTex [[texture(0)]],
    constant OpnsUniforms& u [[buffer(0)]],
    uint2 gid [[thread_position_in_grid]]
) \{
  uint w = outTex.get_width(), h = outTex.get_height();
  if (gid.x >= w || gid.y >= h) return;
  float2 uv = (float2(gid) + 0.5f) / float2(float(w), float(h));
  float2 ndc = uv * 2.0f - 1.0f;
  ndc.y = -ndc.y;
  float3 ro = u.camPos.xyz;
  float3 rd = normalize(u.camFwd.xyz + ndc.x * u.camRight.xyz + ndc.y * u.camUp.xyz);
  float bDot = dot(ro, rd);
  float cDot = dot(ro, ro) - 6.76f;
  float disc = bDot * bDot - cDot;
  if (disc < 0.0f) \{ outTex.write(half4(0.0h), gid); return; }
  float sqD = sqrt(disc);
  float t = max(0.0f, -bDot - sqD);
  float tMax = -bDot + sqD;
  float thresh = max(0.002f, u.params.x);
  float stepBase = max(0.004f, u.params.y);
  int maxSteps = clamp(int(u.params.z), 16, 128);
  float lastd = 10000.0f;
  bool hit = false;
  float3 pos = ro + rd * t;
  for (int i = 0; i < 128; ++i) \{
    if (i >= maxSteps || t > tMax) break;
    pos = ro + rd * t;
    float d = product_len(pos, u.blade);
    float stepLen = clamp(stepBase * (1.0f + 42.0f * d), stepBase * 0.5f, 0.14f);
    if (d < thresh) \{
      float a = clamp((lastd - thresh) / max(1e-5f, lastd - d), 0.0f, 1.0f);
      t -= (1.0f - a) * stepLen;
      pos = ro + rd * t;
      hit = true;
      break;
    }
    lastd = d;
    t += stepLen;
  }
  if (!hit) \{ outTex.write(half4(0.0h), gid); return; }
  const float eps = 0.0015f;
  float3 grad = float3(
    product_len(pos + float3(eps,0.0f,0.0f), u.blade) - product_len(pos - float3(eps,0.0f,0.0f), u.blade),
    product_len(pos + float3(0.0f,eps,0.0f), u.blade) - product_len(pos - float3(0.0f,eps,0.0f), u.blade),
    product_len(pos + float3(0.0f,0.0f,eps), u.blade) - product_len(pos - float3(0.0f,0.0f,eps), u.blade)
  );
  float3 N = length(grad) > 1e-6f ? normalize(grad) : float3(0.0f, 1.0f, 0.0f);
  if (dot(N, -rd) < 0.0f) N = -N;
  float3 V = -rd;
  float3 Lk = normalize(float3(0.55f, 0.78f, 0.38f));
  float3 Lr = normalize(float3(-0.62f, 0.36f, -0.68f));
  float diffKey = max(0.0f, dot(N, Lk));
  float diffRim = max(0.0f, dot(N, Lr));
  float spec = pow(max(0.0f, dot(N, normalize(Lk + V))), 48.0f);
  float fres = pow(1.0f - max(0.0f, dot(N, V)), 3.0f);
  float3 lit = u.color.rgb * (0.24f + 0.74f * diffKey)
             + float3(0.52f, 0.85f, 1.0f) * (0.30f * diffRim + 0.42f * fres)
             + float3(1.0f, 0.97f, 0.92f) * (0.55f * spec);
  float outA = clamp(u.color.a * (0.76f + 0.24f * fres), 0.20f, 0.98f);
  outTex.write(half4(half3(clamp(lit, 0.0f, 1.0f)), half(outA)), gid);
}
"

/-- Compile a complete `Init`-only `OpnsShaderSource` triplet (`wgsl`, `glsl`, `msl`) for
any `AlgSpec` (`CGA3`, `CGA2`, `PGA3`, `STA`, `R3`, etc.) and grade. -/
def compileGaOpnsBundle (tag : String) (alg : AlgSpec) (grade : Nat) (isIPNS : Bool := false) :
    Except String OpnsShaderSource := do
  let wgsl ← emitGaOpnsWgsl alg grade isIPNS
  let glsl ← emitGaOpnsGlsl alg grade isIPNS
  let msl  ← emitGaOpnsMsl  alg grade isIPNS
  return { hash := hashShaderTag tag glsl, wgsl, glsl, msl }

/-! ## 4. Live User-Typed `ImplicitExpr` → GPU Raymarching Shader Compiler! -/

/-- Exact odd-integer predicate for any finite IEEE-754 float64 integer `kRound`:
for `|k| < 2^53` `toUInt64` is exact (zero saturation); for `|k| >= 2^53` every
representable float64 has ULP >= 2 and is strictly even. -/
private def isOddIntFloat (kRound : Float) : Bool :=
  let ak := Float.abs kRound
  if ak < 9007199254740992.0 then ak.toUInt64.toNat % 2 == 1
  else false

/-- Emit a signed-safe GPU power expression `a ^ b` across GLSL3, WGSL, and Metal MSL:
- Small integer exponents `0..8` use exact unrolled multiplication helpers (`gs_sq`..`gs_p8`) preserving exact sign for `a ≤ 0`!
- Arbitrary odd integer exponents use `gs_spow_odd` (preserving negative signs, zero NaN at `a = 0`)!
- Arbitrary even integer exponents use `gs_spow_even`!
- Non-integer exponents fall back safely to `pow(max(1e-6, abs(a)), b)`. -/
private def emitPowGpu (sa : String) (b : Expr) (sb : String) : String :=
  match b with
  | .lit k =>
    if !k.isFinite || k.isNaN then s!"pow(max(1e-6, abs({sa})), {sb})"
    else
      let kRound := Float.round k
      if Float.abs (k - kRound) < 1e-9 then
        let ak := Float.abs kRound
        if kRound ≥ 0.0 && ak <= 8.5 then
          match ak.toUInt64.toNat with
          | 0 => "1.0"
          | 1 => sa
          | 2 => s!"gs_sq({sa})"
          | 3 => s!"gs_cb({sa})"
          | 4 => s!"gs_p4({sa})"
          | 5 => s!"gs_p5({sa})"
          | 6 => s!"gs_p6({sa})"
          | 7 => s!"gs_p7({sa})"
          | 8 => s!"gs_p8({sa})"
          | _ => s!"gs_spow_even({sa}, {fmtFloat kRound})"
        else
          if isOddIntFloat kRound then s!"gs_spow_odd({sa}, {fmtFloat kRound})"
          else s!"gs_spow_even({sa}, {fmtFloat kRound})"
      else
        s!"pow(max(1e-6, abs({sa})), {sb})"
  | _ => s!"pow(max(1e-6, abs({sa})), {sb})"

/-- Structural equality on `ImplicitExpr.Expr` (pure `Init`, zero extra `List` symbols). -/
private def exprEq : Expr → Expr → Bool
  | .lit a, .lit b => a == b && !a.isNaN && !b.isNaN
  | .varX, .varX | .varY, .varY | .varZ, .varZ
  | .varU, .varU | .varV, .varV | .varT, .varT | .varR, .varR => true
  | .un op1 a1, .un op2 a2 => op1 == op2 && exprEq a1 a2
  | .bin op1 a1 b1, .bin op2 a2 b2 => op1 == op2 && exprEq a1 a2 && exprEq b1 b2
  | _, _ => false

/-- Evaluate a unary op on a Float64 constant, returning `some r` only when finite. -/
private def foldUnaryConst (op : UnaryOp) (v : Float) : Option Float :=
  let r :=
    match op with
    | .neg   => -v
    | .sq    => v * v
    | .cube  => v * v * v
    | .p4    => let v2 := v * v; v2 * v2
    | .sin   => Float.sin v
    | .cos   => Float.cos v
    | .tan   => Float.tan v
    | .asin  => Float.asin (max (-1.0) (min 1.0 v))
    | .acos  => Float.acos (max (-1.0) (min 1.0 v))
    | .atan  => Float.atan v
    | .sinh  => Float.sinh v
    | .cosh  => Float.cosh v
    | .tanh  => Float.tanh v
    | .exp   => Float.exp (max (-30.0) (min 30.0 v))
    | .log   => Float.log (max 1e-6 (Float.abs v))
    | .sqrt  => Float.sqrt (max 0.0 v)
    | .abs   => Float.abs v
    | .floor => Float.floor v
    | .ceil  => Float.ceil v
    | .sign  => if v > 0.0 then 1.0 else if v < 0.0 then -1.0 else 0.0
  if r.isFinite then some r else none

/-- Count additive leaf terms inside an expression (capped at `limit + 1`) so
scalar distribution never explodes deeply nested polynomial products. -/
private def countSumTerms (e : Expr) (limit : Nat := 16) : Nat :=
  match e with
  | .bin .add a b | .bin .sub a b =>
    let na := countSumTerms a limit
    if na > limit then limit + 1 else na + countSumTerms b limit
  | .un .neg a => countSumTerms a limit
  | _ => 1

private def pushLinearTerm (scale : Float) (term : Expr)
    (constAcc : Float) (terms : Array (Float × Expr)) : Option (Float × Array (Float × Expr)) := Id.run do
  if !scale.isFinite then return none
  for i in [:terms.size] do
    let (oldC, base) := terms[i]!
    if exprEq base term then
      let sum := oldC + scale
      if !sum.isFinite then return none
      return some (constAcc, terms.set! i (sum, base))
  return some (constAcc, terms.push (scale, term))

/-- Flatten linear combinations `(coeff * base)` in Float64, combining like terms
`a * e ± b * e -> (a ± b) * e` and folding constant offsets before float32 GPU
codegen eliminates catastrophic float32 cancellation (e.g.
`1000000*(0.5000004*x - 0.5000001*x) - 0.15` -> `0.3*x - 0.15`).
Returns `none` on ANY Float64 overflow (`!isFinite`) so no term is ever dropped! -/
private partial def collectLinearTerms (scale : Float) (e : Expr)
    (constAcc : Float) (terms : Array (Float × Expr)) : Option (Float × Array (Float × Expr)) :=
  if !scale.isFinite || !constAcc.isFinite then none
  else if scale == 0.0 then some (constAcc, terms)
  else
    match e with
    | .lit v =>
      let prod := scale * v
      let sum := constAcc + prod
      if prod.isFinite && sum.isFinite then some (sum, terms) else none
    | .un .neg a => collectLinearTerms (-scale) a constAcc terms
    | .bin .add a b => do
      let (c1, t1) ← collectLinearTerms scale a constAcc terms
      collectLinearTerms scale b c1 t1
    | .bin .sub a b => do
      let (c1, t1) ← collectLinearTerms scale a constAcc terms
      collectLinearTerms (-scale) b c1 t1
    | .bin .mul (.lit c) a =>
      if countSumTerms a 12 <= 12 then
        let sc := scale * c
        if sc.isFinite then collectLinearTerms sc a constAcc terms else none
      else
        pushLinearTerm scale (.bin .mul (.lit c) a) constAcc terms
    | .bin .mul a (.lit c) =>
      if countSumTerms a 12 <= 12 then
        let sc := scale * c
        if sc.isFinite then collectLinearTerms sc a constAcc terms else none
      else
        pushLinearTerm scale (.bin .mul a (.lit c)) constAcc terms
    | other => pushLinearTerm scale other constAcc terms

private def rebuildLinearSum (constAcc : Float) (terms : Array (Float × Expr)) : Expr := Id.run do
  let mut parts : Array (Bool × Expr) := #[]
  for (c, base) in terms do
    if c != 0.0 && c.isFinite then
      if c == 1.0 then
        parts := parts.push (true, base)
      else if c == -1.0 then
        parts := parts.push (false, base)
      else if c > 0.0 then
        parts := parts.push (true, .bin .mul (.lit c) base)
      else
        parts := parts.push (false, .bin .mul (.lit (-c)) base)
  if constAcc != 0.0 && constAcc.isFinite then
    if constAcc > 0.0 then
      parts := parts.push (true, .lit constAcc)
    else
      parts := parts.push (false, .lit (-constAcc))
  if parts.isEmpty then
    return .lit 0.0
  let (pos0, e0) := parts[0]!
  let mut acc : Expr :=
    if pos0 then e0
    else
      match e0 with
      | .lit v => .lit (-v)
      | .bin .mul (.lit c) inner => .bin .mul (.lit (-c)) inner
      | other => .un .neg other
  for i in [1:parts.size] do
    let (pos, ei) := parts[i]!
    acc := if pos then .bin .add acc ei else .bin .sub acc ei
  return acc

private def scaleExpr (c : Float) : Expr → Expr
  | .lit v =>
    let p := c * v
    if p.isFinite then .lit p else .bin .mul (.lit c) (.lit v)
  | .un .neg inner => scaleExpr (-c) inner
  | .bin .mul (.lit c2) inner =>
    let p := c * c2
    if p.isFinite then scaleExpr p inner else .bin .mul (.lit c) (.bin .mul (.lit c2) inner)
  | other =>
    if c == 0.0 then .lit 0.0
    else if c == 1.0 then other
    else if c == -1.0 then .un .neg other
    else .bin .mul (.lit c) other

private def simplifyMul (a b : Expr) : Expr :=
  match a, b with
  | .lit ca, x => scaleExpr ca x
  | x, .lit cb => scaleExpr cb x
  | .bin .mul (.lit c1) x, .bin .mul (.lit c2) y =>
    let p := c1 * c2
    if p.isFinite then scaleExpr p (.bin .mul x y) else .bin .mul a b
  | .bin .mul (.lit c1) x, y => scaleExpr c1 (.bin .mul x y)
  | x, .bin .mul (.lit c2) y => scaleExpr c2 (.bin .mul x y)
  | x, y => .bin .mul x y

/-- Bottom-up Float64 algebraic constant-folding & like-term combining pass
applied before float32 GPU shader emission (GLSL3, WGSL, and Metal MSL). -/
partial def simplifyExpr : Expr → Expr
  | .lit v => .lit v
  | .varX => .varX | .varY => .varY | .varZ => .varZ
  | .varU => .varU | .varV => .varV | .varT => .varT | .varR => .varR
  | .un op a =>
    let a' := simplifyExpr a
    match a' with
    | .lit v =>
      match foldUnaryConst op v with
      | some r => .lit r
      | none => .un op a'
    | _ =>
      match op, a' with
      | .neg, .un .neg inner => inner
      | .neg, .bin .mul (.lit c) inner => simplifyMul (.lit (-c)) inner
      | .neg, .bin .add _ _ | .neg, .bin .sub _ _ =>
        match collectLinearTerms (-1.0) a' 0.0 #[] with
        | some (cAcc, terms) => rebuildLinearSum cAcc terms
        | none => .un .neg a'
      | _, _ => .un op a'
  | .bin op a b =>
    let a' := simplifyExpr a
    let b' := simplifyExpr b
    match op with
    | .add =>
      match (do
        let (c1, t1) ← collectLinearTerms 1.0 a' 0.0 #[]
        collectLinearTerms 1.0 b' c1 t1) with
      | some (c2, t2) => rebuildLinearSum c2 t2
      | none => .bin .add a' b'
    | .sub =>
      match (do
        let (c1, t1) ← collectLinearTerms 1.0 a' 0.0 #[]
        collectLinearTerms (-1.0) b' c1 t1) with
      | some (c2, t2) => rebuildLinearSum c2 t2
      | none => .bin .sub a' b'
    | .mul => simplifyMul a' b'
    | .div =>
      match a', b' with
      | .lit ca, .lit cb =>
        if Float.abs cb >= 1e-30 && (ca / cb).isFinite then .lit (ca / cb)
        else .bin .div a' b'
      | .bin .mul (.lit ca) inner, .lit cb =>
        if Float.abs cb >= 1e-30 && (ca / cb).isFinite then scaleExpr (ca / cb) inner
        else .bin .div a' b'
      | .lit 0.0, _ => .lit 0.0
      | x, .lit 1.0 => x
      | x, .lit (-1.0) => simplifyMul (.lit (-1.0)) x
      | _, _ => .bin .div a' b'
    | .pow =>
      match a', b' with
      | .lit ca, .lit cb =>
        let kRound := Float.round cb
        if cb.isFinite && Float.abs (cb - kRound) < 1e-9 then
          let r :=
            if ca < 0.0 then
              let mag := Float.pow (Float.abs ca) kRound
              if isOddIntFloat kRound then -mag else mag
            else Float.pow ca kRound
          if r.isFinite then .lit r else .bin .pow a' b'
        else if ca >= 0.0 && (Float.pow ca cb).isFinite then
          .lit (Float.pow ca cb)
        else .bin .pow a' b'
      | _, .lit 0.0 => .lit 1.0
      | x, .lit 1.0 => x
      | x, .lit 2.0 => .un .sq x
      | x, .lit 3.0 => .un .cube x
      | x, .lit 4.0 => .un .p4 x
      | _, _ => .bin .pow a' b'
    | .min =>
      match a', b' with
      | .lit ca, .lit cb => .lit (min ca cb)
      | _, _ => .bin .min a' b'
    | .max =>
      match a', b' with
      | .lit ca, .lit cb => .lit (max ca cb)
      | _, _ => .bin .max a' b'
    | .atan2 =>
      match a', b' with
      | .lit ca, .lit cb =>
        let r := Float.atan2 ca cb
        if r.isFinite then .lit r else .bin .atan2 a' b'
      | _, _ => .bin .atan2 a' b'
    | .hypot =>
      match a', b' with
      | .lit ca, .lit cb =>
        let r := Float.sqrt (ca * ca + cb * cb)
        if r.isFinite then .lit r else .bin .hypot a' b'
      | _, _ => .bin .hypot a' b'

/-- Emit a compiled `Grassmann.Eval.ImplicitExpr.Expr` as a safe, parenthesized GPU
scalar expression in GLSL 300 es, WGSL, or Metal MSL. -/
def emitExprGpu (target : GpuTarget) (e : Expr) (tVar : String) : String :=
  match e with
  | .lit v => fmtFloat v
  | .varX  => "p.x"
  | .varY  => "p.y"
  | .varZ  => "p.z"
  | .varU  => "p.x"
  | .varV  => "p.y"
  | .varT  => tVar
  | .varR  => "length(p)"
  | .un op a =>
    let sa := emitExprGpu target a tVar
    match op with
    | .neg   => s!"(-({sa}))"
    | .sq    => s!"gs_sq({sa})"
    | .cube  => s!"gs_cb({sa})"
    | .p4    => s!"gs_p4({sa})"
    | .sin   => s!"sin({sa})"
    | .cos   => s!"cos({sa})"
    | .tan   => s!"tan({sa})"
    | .asin  => s!"asin(clamp({sa}, -1.0, 1.0))"
    | .acos  => s!"acos(clamp({sa}, -1.0, 1.0))"
    | .atan  => s!"atan({sa})"
    | .sinh  => s!"sinh({sa})"
    | .cosh  => s!"cosh({sa})"
    | .tanh  => s!"tanh({sa})"
    | .exp   => s!"exp(clamp({sa}, -30.0, 30.0))"
    | .log   => s!"log(max(1e-6, abs({sa})))"
    | .sqrt  => s!"sqrt(max(0.0, {sa}))"
    | .abs   => s!"abs({sa})"
    | .floor => s!"floor({sa})"
    | .ceil  => s!"ceil({sa})"
    | .sign  => s!"sign({sa})"
  | .bin op a b =>
    let sa := emitExprGpu target a tVar
    let sb := emitExprGpu target b tVar
    match op with
    | .add   => s!"({sa} + {sb})"
    | .sub   => s!"({sa} - {sb})"
    | .mul   => s!"({sa} * {sb})"
    | .div   => s!"({sa} / (abs({sb}) < 1e-6 ? 1e-6 : {sb}))"
    | .pow   => emitPowGpu sa b sb
    | .atan2 =>
      match target with
      | .glsl => s!"atan({sa}, {sb})"
      | _     => s!"atan2({sa}, {sb})"
    | .min   => s!"min({sa}, {sb})"
    | .max   => s!"max({sa}, {sb})"
    | .hypot =>
      match target with
      | .wgsl => s!"length(vec2<f32>({sa}, {sb}))"
      | .glsl => s!"length(vec2({sa}, {sb}))"
      | .msl  => s!"length(float2({sa}, {sb}))"

/-- WGSL ternary-free division & signed-power expression helper. -/
private def emitExprWgsl (e : Expr) (tVar : String) : String :=
  match e with
  | .bin .div a b =>
    let sa := emitExprWgsl a tVar
    let sb := emitExprWgsl b tVar
    s!"({sa} / select({sb}, 1e-6, abs({sb}) < 1e-6))"
  | .bin op a b =>
    let sa := emitExprWgsl a tVar
    let sb := emitExprWgsl b tVar
    match op with
    | .add   => s!"({sa} + {sb})"
    | .sub   => s!"({sa} - {sb})"
    | .mul   => s!"({sa} * {sb})"
    | .pow   => emitPowGpu sa b sb
    | .atan2 => s!"atan2({sa}, {sb})"
    | .min   => s!"min({sa}, {sb})"
    | .max   => s!"max({sa}, {sb})"
    | .hypot => s!"length(vec2<f32>({sa}, {sb}))"
    | .div   => s!"({sa} / select({sb}, 1e-6, abs({sb}) < 1e-6))"
  | .un op a =>
    let sa := emitExprWgsl a tVar
    match op with
    | .neg   => s!"(-({sa}))"
    | .sq    => s!"gs_sq({sa})"
    | .cube  => s!"gs_cb({sa})"
    | .p4    => s!"gs_p4({sa})"
    | .sin   => s!"sin({sa})"
    | .cos   => s!"cos({sa})"
    | .tan   => s!"tan({sa})"
    | .asin  => s!"asin(clamp({sa}, -1.0, 1.0))"
    | .acos  => s!"acos(clamp({sa}, -1.0, 1.0))"
    | .atan  => s!"atan({sa})"
    | .sinh  => s!"sinh({sa})"
    | .cosh  => s!"cosh({sa})"
    | .tanh  => s!"tanh({sa})"
    | .exp   => s!"exp(clamp({sa}, -30.0, 30.0))"
    | .log   => s!"log(max(1e-6, abs({sa})))"
    | .sqrt  => s!"sqrt(max(0.0, {sa}))"
    | .abs   => s!"abs({sa})"
    | .floor => s!"floor({sa})"
    | .ceil  => s!"ceil({sa})"
    | .sign  => s!"sign({sa})"
  | other => emitExprGpu .wgsl other tVar

/-- Canonical half-extent clamp `[0.5, 20.0]` shared identically between CPU Marching Tetrahedra
and GLSL3/WGSL/MSL axis-aligned box `[-bound, bound]³` raymarching. -/
private def clampImplicitBound (bound : Float) : Float :=
  if bound.isNaN || !bound.isFinite then 1.6
  else max 0.5 (min 20.0 bound)

/-- Emit a complete **GLSL 300 es (`THREE.GLSL3`)** implicit-surface raymarching fragment
shader (exact ray–AABB `[-bound, bound]³` clipping + sign-change bisection + exact `gl_FragDepth`)
for any user-typed `f(x,y,z,t)=0`. -/
def emitImplicitExprGlsl (exprStr : String) (e : Expr) (bound : Float := 1.6) : String :=
  let body := emitExprGpu .glsl (simplifyExpr e) "uSimTime"
  let b := clampImplicitBound bound
  let gradH := max 0.0015 (b * 0.001)
  s!"#version 300 es
// Auto-generated by Grassmann.Codegen.GPUInit (Implicit 3D: {exprStr} = 0, bound={fmtFloat b})
precision highp float;
in vec3 vWorldPos;
in vec3 vLocalPos;
out vec4 fragColor;

uniform vec4 uColor;
uniform float uCoeffs[64];
uniform int uGrade;
uniform float uThresh;
uniform int uMaxSteps;
uniform float uStepSize;
uniform int uIsIPNS;
uniform float uSimTime;
uniform vec2 uResolution;
uniform mat4 uInvViewProj;
uniform mat4 projectionMatrix;

float gs_sq(float v) \{ return v * v; }
float gs_cb(float v) \{ return v * v * v; }
float gs_p4(float v) \{ float s = v * v; return s * s; }
float gs_p5(float v) \{ float s = v * v; return s * s * v; }
float gs_p6(float v) \{ float c = v * v * v; return c * c; }
float gs_p7(float v) \{ float s = v * v; float c = s * v; return c * c * v; }
float gs_p8(float v) \{ float s = v * v; float q = s * s; return q * q; }
float gs_spow_odd(float v, float e) \{
  float a = abs(v);
  float r = e < 0.0 ? pow(max(1e-6, a), e) : (a < 1e-30 ? 0.0 : pow(a, e));
  return v < 0.0 ? -r : r;
}
float gs_spow_even(float v, float e) \{
  float a = abs(v);
  return e < 0.0 ? pow(max(1e-6, a), e) : (a < 1e-30 ? 0.0 : pow(a, e));
}

float eval_implicit(vec3 p) \{
  return {body};
}

vec2 intersectBox(vec3 ro, vec3 rd, float b) \{
  float tNear = -1e30;
  float tFar = 1e30;
  if (abs(rd.x) < 1e-12) \{
    if (ro.x < -b || ro.x > b) return vec2(1.0, -1.0);
  } else \{
    float invX = 1.0 / rd.x;
    float t0x = (-b - ro.x) * invX;
    float t1x = ( b - ro.x) * invX;
    tNear = max(tNear, min(t0x, t1x));
    tFar  = min(tFar,  max(t0x, t1x));
  }
  if (abs(rd.y) < 1e-12) \{
    if (ro.y < -b || ro.y > b) return vec2(1.0, -1.0);
  } else \{
    float invY = 1.0 / rd.y;
    float t0y = (-b - ro.y) * invY;
    float t1y = ( b - ro.y) * invY;
    tNear = max(tNear, min(t0y, t1y));
    tFar  = min(tFar,  max(t0y, t1y));
  }
  if (abs(rd.z) < 1e-12) \{
    if (ro.z < -b || ro.z > b) return vec2(1.0, -1.0);
  } else \{
    float invZ = 1.0 / rd.z;
    float t0z = (-b - ro.z) * invZ;
    float t1z = ( b - ro.z) * invZ;
    tNear = max(tNear, min(t0z, t1z));
    tFar  = min(tFar,  max(t0z, t1z));
  }
  if (tFar < tNear || tFar < 0.0) return vec2(1.0, -1.0);
  return vec2(max(0.0, tNear), tFar);
}

vec2 gs_refine_min(vec3 ro, vec3 rd, float ta, float tb, float tMidInit, float gMidInit, float s, float g0, float g2) \{
  float ga = ta, gb = tb;
  const float invPhi = 0.61803398875;
  float gc = gb - (gb - ga) * invPhi;
  float gd = ga + (gb - ga) * invPhi;
  float fc = s * eval_implicit(ro + rd * gc);
  float fd = s * eval_implicit(ro + rd * gd);
  bool flipped = false;
  float tFlip = ta;
  if (fc <= 0.0) \{ flipped = true; tFlip = gc; }
  else if (fd <= 0.0) \{ flipped = true; tFlip = gd; }
  else \{
    for (int k = 0; k < 32; k++) \{
      if (fc < fd) \{
        gb = gd; gd = gc; fd = fc;
        gc = gb - (gb - ga) * invPhi;
        fc = s * eval_implicit(ro + rd * gc);
        if (fc <= 0.0) \{ flipped = true; tFlip = gc; break; }
      } else \{
        ga = gc; gc = gd; fc = fd;
        gd = ga + (gb - ga) * invPhi;
        fd = s * eval_implicit(ro + rd * gd);
        if (fd <= 0.0) \{ flipped = true; tFlip = gd; break; }
      }
    }
  }
  if (flipped) \{
    float lo = (tMidInit > ta && tFlip > tMidInit) ? tMidInit : ta;
    float hi = tFlip;
    for (int k = 0; k < 6; k++) \{
      float mid = 0.5 * (lo + hi);
      if (s * eval_implicit(ro + rd * mid) > 0.0) \{ lo = mid; } else \{ hi = mid; }
    }
    return vec2(1.0, 0.5 * (lo + hi));
  }
  float tMin = (fc < fd) ? gc : gd;
  float gMin = min(fc, fd);
  if (tMidInit > ta && gMidInit < gMin) \{ gMin = gMidInit; tMin = tMidInit; }
  float gMaxEnd = max(g0, g2);
  if (gMaxEnd > 0.0 && gMin < g0 && gMin < g2 && gMin <= 1e-8 * gMaxEnd) \{
    float delta = 0.01 * (tb - ta);
    float gL = s * eval_implicit(ro + rd * max(ta, tMin - delta));
    float gR = s * eval_implicit(ro + rd * min(tb, tMin + delta));
    float gLoc = max(gL, gR);
    if (gL <= 0.0 || gR <= 0.0 || (gLoc > 0.0 && gMin <= 1e-5 * gLoc)) \{
      return vec2(1.0, tMin);
    }
  }
  return vec2(0.0, 0.0);
}

void main() \{
  vec3 ro = cameraPosition;
  vec3 rd = normalize(vWorldPos - cameraPosition);
  vec2 hitRange = intersectBox(ro, rd, {fmtFloat b});
  if (hitRange.y < hitRange.x || hitRange.y < 0.0) discard;

  int steps = clamp(uMaxSteps, 32, 160);
  float dt = (hitRange.y - hitRange.x) / float(steps);
  float tPrev2 = hitRange.x;
  float fPrev2 = 0.0;
  float tPrev = hitRange.x;
  float fPrev = eval_implicit(ro + rd * tPrev);
  bool hit = (fPrev == 0.0);
  float tHit = tPrev;

  if (!hit) \{
    for (int i = 1; i <= 160; i++) \{
      if (i > steps) break;
      float tCur = (i == steps) ? hitRange.y : (hitRange.x + dt * float(i));
      float fCur = eval_implicit(ro + rd * tCur);
      // Strictly scale-invariant zero-set crossing (invariant under f -> c*f for all c > 0)
      if (fCur == 0.0) \{
        tHit = tCur;
        hit = true;
        break;
      }
      if ((fPrev < 0.0 && fCur > 0.0) || (fPrev > 0.0 && fCur < 0.0)) \{
        // 6-step bisection refinement for razor-sharp algebraic silhouettes
        float lo = tPrev, hi = tCur, fLo = fPrev;
        for (int k = 0; k < 6; k++) \{
          float mid = 0.5 * (lo + hi);
          float fMid = eval_implicit(ro + rd * mid);
          if ((fLo < 0.0 && fMid < 0.0) || (fLo > 0.0 && fMid > 0.0)) \{
            lo = mid; fLo = fMid;
          } else \{
            hi = mid;
          }
        }
        tHit = 0.5 * (lo + hi);
        hit = true;
        break;
      }
      float s = fPrev > 0.0 ? 1.0 : -1.0;
      float gPrev = s * fPrev;
      float gCur  = s * fCur;
      if (i == 1 && gPrev < gCur) \{
        vec2 rHit = gs_refine_min(ro, rd, tPrev, tCur, tPrev, gPrev, s, gPrev, gCur);
        if (rHit.x > 0.5) \{ tHit = rHit.y; hit = true; break; }
      }
      if (i >= 2) \{
        float gPrev2 = s * fPrev2;
        if (gPrev <= gPrev2 && gPrev <= gCur && (gPrev < gPrev2 || gPrev < gCur)) \{
          vec2 rHit = gs_refine_min(ro, rd, tPrev2, tCur, tPrev, gPrev, s, gPrev2, gCur);
          if (rHit.x > 0.5) \{ tHit = rHit.y; hit = true; break; }
        }
      }
      if (i == steps && gCur < gPrev) \{
        vec2 rHit = gs_refine_min(ro, rd, tPrev, tCur, tPrev, gPrev, s, gPrev, gCur);
        if (rHit.x > 0.5) \{ tHit = rHit.y; hit = true; break; }
      }
      tPrev2 = tPrev;
      fPrev2 = fPrev;
      tPrev = tCur;
      fPrev = fCur;
    }
  }
  if (!hit) discard;

  vec3 pos = ro + rd * tHit;
  float h = {fmtFloat gradH};
  float f0 = eval_implicit(pos);
  float fpx = eval_implicit(pos + vec3(h,0.0,0.0)), fmx = eval_implicit(pos - vec3(h,0.0,0.0));
  float fpy = eval_implicit(pos + vec3(0.0,h,0.0)), fmy = eval_implicit(pos - vec3(0.0,h,0.0));
  float fpz = eval_implicit(pos + vec3(0.0,0.0,h)), fmz = eval_implicit(pos - vec3(0.0,0.0,h));
  vec3 g = vec3(fpx - fmx, fpy - fmy, fpz - fmz);
  float gMax = max(abs(g.x), max(abs(g.y), abs(g.z)));
  vec3 N = -rd;
  if (gMax > 1e-20) \{
    N = normalize(g / gMax);
  } else \{
    vec3 h2 = vec3(fpx + fmx - 2.0 * f0, fpy + fmy - 2.0 * f0, fpz + fmz - 2.0 * f0);
    float h2Max = max(abs(h2.x), max(abs(h2.y), abs(h2.z)));
    if (h2Max > 1e-20) N = normalize(h2 / h2Max);
  }
  if (dot(N, -rd) < 0.0) N = -N;
  vec3 V = -rd;
  vec3 Lk = normalize(vec3(0.55, 0.78, 0.38));
  vec3 Lr = normalize(vec3(-0.62, 0.36, -0.68));
  float diffKey = max(0.0, dot(N, Lk));
  float diffRim = max(0.0, dot(N, Lr));
  float spec = pow(max(0.0, dot(N, normalize(Lk + V))), 52.0);
  float fres = pow(1.0 - max(0.0, dot(N, V)), 3.0);
  // Curvature-inspired iridescent base tint mixed with uColor
  float phase = 2.0 * (0.5 + 0.3 * pos.y) + 0.6 * (N.x + N.z);
  vec3 irid = vec3(0.50 + 0.40 * cos(phase), 0.54 + 0.36 * cos(phase + 2.094), 0.64 + 0.34 * cos(phase + 4.188));
  vec3 baseCol = mix(uColor.rgb, irid, 0.55);
  vec3 lit = baseCol * (0.24 + 0.74 * diffKey)
           + vec3(0.52, 0.85, 1.0) * (0.30 * diffRim + 0.44 * fres)
           + vec3(1.0, 0.97, 0.92) * (0.58 * spec);

  vec4 clipPos = projectionMatrix * viewMatrix * vec4(pos, 1.0);
  gl_FragDepth = clamp((clipPos.z / clipPos.w) * 0.5 + 0.5, 0.0, 1.0);
  fragColor = vec4(clamp(lit, 0.0, 1.0), clamp(uColor.a, 0.35, 1.0));
}
"

/-- Emit a complete **WebGPU `WGSL`** implicit-surface raymarching fragment shader with exact
ray–AABB `[-bound, bound]³` clipping and `tFar < tNear || tFar < 0.0` guard. -/
def emitImplicitExprWgsl (exprStr : String) (e : Expr) (bound : Float := 1.6) : String :=
  let body := emitExprWgsl (simplifyExpr e) "u.params.w"
  let b := clampImplicitBound bound
  let gradH := max 0.0015 (b * 0.001)
  s!"// Auto-generated by Grassmann.Codegen.GPUInit (Implicit 3D: {exprStr} = 0, bound={fmtFloat b})
struct OpnsUniforms \{
  camPos   : vec4<f32>,
  camRight : vec4<f32>,
  camUp    : vec4<f32>,
  camFwd   : vec4<f32>,
  color    : vec4<f32>,
  params   : vec4<f32>, // x=thresh, y=stepSize, z=maxSteps, w=simTime
  blade    : array<vec4<f32>, 16>,
};
@group(0) @binding(0) var<uniform> u : OpnsUniforms;

fn gs_sq(v: f32) -> f32 \{ return v * v; }
fn gs_cb(v: f32) -> f32 \{ return v * v * v; }
fn gs_p4(v: f32) -> f32 \{ let s = v * v; return s * s; }
fn gs_p5(v: f32) -> f32 \{ let s = v * v; return s * s * v; }
fn gs_p6(v: f32) -> f32 \{ let c = v * v * v; return c * c; }
fn gs_p7(v: f32) -> f32 \{ let s = v * v; let c = s * v; return c * c * v; }
fn gs_p8(v: f32) -> f32 \{ let s = v * v; let q = s * s; return q * q; }
fn gs_spow_odd(v: f32, e: f32) -> f32 \{
  let a = abs(v);
  let rPos = select(pow(max(1e-30, a), e), 0.0, a < 1e-30);
  let rNeg = pow(max(1e-6, a), e);
  let r = select(rPos, rNeg, e < 0.0);
  return select(r, -r, v < 0.0);
}
fn gs_spow_even(v: f32, e: f32) -> f32 \{
  let a = abs(v);
  let rPos = select(pow(max(1e-30, a), e), 0.0, a < 1e-30);
  let rNeg = pow(max(1e-6, a), e);
  return select(rPos, rNeg, e < 0.0);
}

fn eval_implicit(p: vec3<f32>) -> f32 \{
  return {body};
}

fn intersectBox(ro: vec3<f32>, rd: vec3<f32>, b: f32) -> vec2<f32> \{
  var tNear: f32 = -1e30;
  var tFar: f32 = 1e30;
  if (abs(rd.x) < 1e-12) \{
    if (ro.x < -b || ro.x > b) \{ return vec2<f32>(1.0, -1.0); }
  } else \{
    let invX = 1.0 / rd.x;
    let t0x = (-b - ro.x) * invX;
    let t1x = ( b - ro.x) * invX;
    tNear = max(tNear, min(t0x, t1x));
    tFar  = min(tFar,  max(t0x, t1x));
  }
  if (abs(rd.y) < 1e-12) \{
    if (ro.y < -b || ro.y > b) \{ return vec2<f32>(1.0, -1.0); }
  } else \{
    let invY = 1.0 / rd.y;
    let t0y = (-b - ro.y) * invY;
    let t1y = ( b - ro.y) * invY;
    tNear = max(tNear, min(t0y, t1y));
    tFar  = min(tFar,  max(t0y, t1y));
  }
  if (abs(rd.z) < 1e-12) \{
    if (ro.z < -b || ro.z > b) \{ return vec2<f32>(1.0, -1.0); }
  } else \{
    let invZ = 1.0 / rd.z;
    let t0z = (-b - ro.z) * invZ;
    let t1z = ( b - ro.z) * invZ;
    tNear = max(tNear, min(t0z, t1z));
    tFar  = min(tFar,  max(t0z, t1z));
  }
  if (tFar < tNear || tFar < 0.0) \{ return vec2<f32>(1.0, -1.0); }
  return vec2<f32>(max(0.0, tNear), tFar);
}

fn gs_refine_min(ro: vec3<f32>, rd: vec3<f32>, ta: f32, tb: f32, tMidInit: f32, gMidInit: f32, s: f32, g0: f32, g2: f32) -> vec2<f32> \{
  var ga = ta;
  var gb = tb;
  let invPhi: f32 = 0.61803398875;
  var gc = gb - (gb - ga) * invPhi;
  var gd = ga + (gb - ga) * invPhi;
  var fc = s * eval_implicit(ro + rd * gc);
  var fd = s * eval_implicit(ro + rd * gd);
  var flipped: bool = false;
  var tFlip: f32 = ta;
  if (fc <= 0.0) \{ flipped = true; tFlip = gc; }
  else if (fd <= 0.0) \{ flipped = true; tFlip = gd; }
  else \{
    for (var k: i32 = 0; k < 32; k = k + 1) \{
      if (fc < fd) \{
        gb = gd; gd = gc; fd = fc;
        gc = gb - (gb - ga) * invPhi;
        fc = s * eval_implicit(ro + rd * gc);
        if (fc <= 0.0) \{ flipped = true; tFlip = gc; break; }
      } else \{
        ga = gc; gc = gd; fc = fd;
        gd = ga + (gb - ga) * invPhi;
        fd = s * eval_implicit(ro + rd * gd);
        if (fd <= 0.0) \{ flipped = true; tFlip = gd; break; }
      }
    }
  }
  if (flipped) \{
    var lo = select(ta, tMidInit, tMidInit > ta && tFlip > tMidInit);
    var hi = tFlip;
    for (var k: i32 = 0; k < 6; k = k + 1) \{
      let mid = 0.5 * (lo + hi);
      if (s * eval_implicit(ro + rd * mid) > 0.0) \{ lo = mid; } else \{ hi = mid; }
    }
    return vec2<f32>(1.0, 0.5 * (lo + hi));
  }
  var tMin = select(gd, gc, fc < fd);
  var gMin = min(fc, fd);
  if (tMidInit > ta && gMidInit < gMin) \{ gMin = gMidInit; tMin = tMidInit; }
  let gMaxEnd = max(g0, g2);
  if (gMaxEnd > 0.0 && gMin < g0 && gMin < g2 && gMin <= 1e-8 * gMaxEnd) \{
    let delta = 0.01 * (tb - ta);
    let gL = s * eval_implicit(ro + rd * max(ta, tMin - delta));
    let gR = s * eval_implicit(ro + rd * min(tb, tMin + delta));
    let gLoc = max(gL, gR);
    if (gL <= 0.0 || gR <= 0.0 || (gLoc > 0.0 && gMin <= 1e-5 * gLoc)) \{
      return vec2<f32>(1.0, tMin);
    }
  }
  return vec2<f32>(0.0, 0.0);
}

@fragment
fn fs_main(@location(0) uv: vec2<f32>) -> @location(0) vec4<f32> \{
  let ndc = uv * 2.0 - vec2<f32>(1.0, 1.0);
  let ro = u.camPos.xyz;
  let rd = normalize(u.camFwd.xyz + ndc.x * u.camRight.xyz + ndc.y * u.camUp.xyz);
  let hitRange = intersectBox(ro, rd, {fmtFloat b});
  if (hitRange.y < hitRange.x || hitRange.y < 0.0) \{ discard; }
  let tNear = hitRange.x;
  let tFar = hitRange.y;
  let steps = clamp(i32(u.params.z), 32, 160);
  let dt = (tFar - tNear) / f32(steps);
  var tPrev2 = tNear;
  var fPrev2: f32 = 0.0;
  var tPrev = tNear;
  var fPrev = eval_implicit(ro + rd * tPrev);
  var hit: bool = (fPrev == 0.0);
  var tHit = tPrev;
  if (!hit) \{
    for (var i: i32 = 1; i <= 160; i = i + 1) \{
      if (i > steps) \{ break; }
      let tCur = select(tNear + dt * f32(i), tFar, i == steps);
      let fCur = eval_implicit(ro + rd * tCur);
      // Strictly scale-invariant zero-set crossing (invariant under f -> c*f for all c > 0)
      if (fCur == 0.0) \{
        tHit = tCur;
        hit = true;
        break;
      }
      if ((fPrev < 0.0 && fCur > 0.0) || (fPrev > 0.0 && fCur < 0.0)) \{
        var lo = tPrev; var hi = tCur; var fLo = fPrev;
        for (var k: i32 = 0; k < 6; k = k + 1) \{
          let mid = 0.5 * (lo + hi);
          let fMid = eval_implicit(ro + rd * mid);
          if ((fLo < 0.0 && fMid < 0.0) || (fLo > 0.0 && fMid > 0.0)) \{
            lo = mid; fLo = fMid;
          } else \{
            hi = mid;
          }
        }
        tHit = 0.5 * (lo + hi);
        hit = true;
        break;
      }
      let s = select(-1.0, 1.0, fPrev > 0.0);
      let gPrev = s * fPrev;
      let gCur  = s * fCur;
      if (i == 1 && gPrev < gCur) \{
        let rHit = gs_refine_min(ro, rd, tPrev, tCur, tPrev, gPrev, s, gPrev, gCur);
        if (rHit.x > 0.5) \{ tHit = rHit.y; hit = true; break; }
      }
      if (i >= 2) \{
        let gPrev2 = s * fPrev2;
        if (gPrev <= gPrev2 && gPrev <= gCur && (gPrev < gPrev2 || gPrev < gCur)) \{
          let rHit = gs_refine_min(ro, rd, tPrev2, tCur, tPrev, gPrev, s, gPrev2, gCur);
          if (rHit.x > 0.5) \{ tHit = rHit.y; hit = true; break; }
        }
      }
      if (i == steps && gCur < gPrev) \{
        let rHit = gs_refine_min(ro, rd, tPrev, tCur, tPrev, gPrev, s, gPrev, gCur);
        if (rHit.x > 0.5) \{ tHit = rHit.y; hit = true; break; }
      }
      tPrev2 = tPrev;
      fPrev2 = fPrev;
      tPrev = tCur;
      fPrev = fCur;
    }
  }
  if (!hit) \{ discard; }
  let pos = ro + rd * tHit;
  let h: f32 = {fmtFloat gradH};
  let f0 = eval_implicit(pos);
  let fpx = eval_implicit(pos + vec3<f32>(h,0.0,0.0));
  let fmx = eval_implicit(pos - vec3<f32>(h,0.0,0.0));
  let fpy = eval_implicit(pos + vec3<f32>(0.0,h,0.0));
  let fmy = eval_implicit(pos - vec3<f32>(0.0,h,0.0));
  let fpz = eval_implicit(pos + vec3<f32>(0.0,0.0,h));
  let fmz = eval_implicit(pos - vec3<f32>(0.0,0.0,h));
  let g = vec3<f32>(fpx - fmx, fpy - fmy, fpz - fmz);
  let gMax = max(abs(g.x), max(abs(g.y), abs(g.z)));
  var N = -rd;
  if (gMax > 1e-20) \{
    N = normalize(g / gMax);
  } else \{
    let h2 = vec3<f32>(fpx + fmx - 2.0 * f0, fpy + fmy - 2.0 * f0, fpz + fmz - 2.0 * f0);
    let h2Max = max(abs(h2.x), max(abs(h2.y), abs(h2.z)));
    if (h2Max > 1e-20) \{ N = normalize(h2 / h2Max); }
  }
  if (dot(N, -rd) < 0.0) \{ N = -N; }
  let V = -rd;
  let Lk = normalize(vec3<f32>(0.55, 0.78, 0.38));
  let Lr = normalize(vec3<f32>(-0.62, 0.36, -0.68));
  let diffKey = max(0.0, dot(N, Lk));
  let diffRim = max(0.0, dot(N, Lr));
  let spec = pow(max(0.0, dot(N, normalize(Lk + V))), 52.0);
  let fres = pow(1.0 - max(0.0, dot(N, V)), 3.0);
  let lit = u.color.rgb * (0.24 + 0.74 * diffKey)
          + vec3<f32>(0.52, 0.85, 1.0) * (0.30 * diffRim + 0.44 * fres)
          + vec3<f32>(1.0, 0.97, 0.92) * (0.58 * spec);
  return vec4<f32>(clamp(lit, vec3<f32>(0.0), vec3<f32>(1.0)), clamp(u.color.a, 0.35, 1.0));
}
"

/-- Emit a complete **Apple Metal `MSL`** compute shader for any user-typed implicit equation
`f(x, y, z, t) = 0` with exact ray–AABB `[-bound, bound]³` clipping and `tFar < tNear || tFar < 0.0f`
guard, matching `OPNSMetalRenderer.swift`'s exact `OpnsUniforms` + `product_len` +
`gsir_lean_opns_compute` contract! -/
def emitImplicitExprMsl (exprStr : String) (e : Expr) (bound : Float := 1.6) : String :=
  let body := emitExprGpu .msl (simplifyExpr e) "simTime"
  let b := clampImplicitBound bound
  let gradH := max 0.0015 (b * 0.001)
  s!"// Auto-generated by Grassmann.Codegen.GPUInit (Implicit 3D: {exprStr} = 0, bound={fmtFloat b})
#include <metal_stdlib>
using namespace metal;

struct OpnsUniforms \{
  float4 camPos;
  float4 camRight;
  float4 camUp;
  float4 camFwd;
  float4 color;
  float4 params; // x=thresh, y=stepSize, z=maxSteps, w=simTime
  float  blade[64];
};

inline float gs_sq(float v) \{ return v * v; }
inline float gs_cb(float v) \{ return v * v * v; }
inline float gs_p4(float v) \{ float s = v * v; return s * s; }
inline float gs_p5(float v) \{ float s = v * v; return s * s * v; }
inline float gs_p6(float v) \{ float c = v * v * v; return c * c; }
inline float gs_p7(float v) \{ float s = v * v; float c = s * v; return c * c * v; }
inline float gs_p8(float v) \{ float s = v * v; float q = s * s; return q * q; }
inline float gs_spow_odd(float v, float e) \{
  float a = abs(v);
  float r = e < 0.0f ? pow(max(1e-6f, a), e) : (a < 1e-30f ? 0.0f : pow(a, e));
  return v < 0.0f ? -r : r;
}
inline float gs_spow_even(float v, float e) \{
  float a = abs(v);
  return e < 0.0f ? pow(max(1e-6f, a), e) : (a < 1e-30f ? 0.0f : pow(a, e));
}

inline float eval_implicit(float3 p, float simTime) \{
  return {body};
}

inline float product_len(float3 p, constant float* b) \{
  return abs(eval_implicit(p, b[0]));
}

inline float2 intersectBox(float3 ro, float3 rd, float b) \{
  float tNear = -1e30f;
  float tFar = 1e30f;
  if (abs(rd.x) < 1e-12f) \{
    if (ro.x < -b || ro.x > b) return float2(1.0f, -1.0f);
  } else \{
    float invX = 1.0f / rd.x;
    float t0x = (-b - ro.x) * invX;
    float t1x = ( b - ro.x) * invX;
    tNear = max(tNear, min(t0x, t1x));
    tFar  = min(tFar,  max(t0x, t1x));
  }
  if (abs(rd.y) < 1e-12f) \{
    if (ro.y < -b || ro.y > b) return float2(1.0f, -1.0f);
  } else \{
    float invY = 1.0f / rd.y;
    float t0y = (-b - ro.y) * invY;
    float t1y = ( b - ro.y) * invY;
    tNear = max(tNear, min(t0y, t1y));
    tFar  = min(tFar,  max(t0y, t1y));
  }
  if (abs(rd.z) < 1e-12f) \{
    if (ro.z < -b || ro.z > b) return float2(1.0f, -1.0f);
  } else \{
    float invZ = 1.0f / rd.z;
    float t0z = (-b - ro.z) * invZ;
    float t1z = ( b - ro.z) * invZ;
    tNear = max(tNear, min(t0z, t1z));
    tFar  = min(tFar,  max(t0z, t1z));
  }
  if (tFar < tNear || tFar < 0.0f) return float2(1.0f, -1.0f);
  return float2(max(0.0f, tNear), tFar);
}

inline float2 gs_refine_min(float3 ro, float3 rd, float simTime, float ta, float tb, float tMidInit, float gMidInit, float s, float g0, float g2) \{
  float ga = ta, gb = tb;
  const float invPhi = 0.61803398875f;
  float gc = gb - (gb - ga) * invPhi;
  float gd = ga + (gb - ga) * invPhi;
  float fc = s * eval_implicit(ro + rd * gc, simTime);
  float fd = s * eval_implicit(ro + rd * gd, simTime);
  bool flipped = false;
  float tFlip = ta;
  if (fc <= 0.0f) \{ flipped = true; tFlip = gc; }
  else if (fd <= 0.0f) \{ flipped = true; tFlip = gd; }
  else \{
    for (int k = 0; k < 32; ++k) \{
      if (fc < fd) \{
        gb = gd; gd = gc; fd = fc;
        gc = gb - (gb - ga) * invPhi;
        fc = s * eval_implicit(ro + rd * gc, simTime);
        if (fc <= 0.0f) \{ flipped = true; tFlip = gc; break; }
      } else \{
        ga = gc; gc = gd; fc = fd;
        gd = ga + (gb - ga) * invPhi;
        fd = s * eval_implicit(ro + rd * gd, simTime);
        if (fd <= 0.0f) \{ flipped = true; tFlip = gd; break; }
      }
    }
  }
  if (flipped) \{
    float lo = (tMidInit > ta && tFlip > tMidInit) ? tMidInit : ta;
    float hi = tFlip;
    for (int k = 0; k < 6; ++k) \{
      float mid = 0.5f * (lo + hi);
      if (s * eval_implicit(ro + rd * mid, simTime) > 0.0f) \{ lo = mid; } else \{ hi = mid; }
    }
    return float2(1.0f, 0.5f * (lo + hi));
  }
  float tMin = (fc < fd) ? gc : gd;
  float gMin = min(fc, fd);
  if (tMidInit > ta && gMidInit < gMin) \{ gMin = gMidInit; tMin = tMidInit; }
  float gMaxEnd = max(g0, g2);
  if (gMaxEnd > 0.0f && gMin < g0 && gMin < g2 && gMin <= 1e-8f * gMaxEnd) \{
    float delta = 0.01f * (tb - ta);
    float gL = s * eval_implicit(ro + rd * max(ta, tMin - delta), simTime);
    float gR = s * eval_implicit(ro + rd * min(tb, tMin + delta), simTime);
    float gLoc = max(gL, gR);
    if (gL <= 0.0f || gR <= 0.0f || (gLoc > 0.0f && gMin <= 1e-5f * gLoc)) \{
      return float2(1.0f, tMin);
    }
  }
  return float2(0.0f, 0.0f);
}

kernel void gsir_lean_opns_compute(
    texture2d<half, access::write> outTex [[texture(0)]],
    constant OpnsUniforms& u [[buffer(0)]],
    uint2 gid [[thread_position_in_grid]]
) \{
  uint w = outTex.get_width(), h = outTex.get_height();
  if (gid.x >= w || gid.y >= h) return;
  float2 uv = (float2(gid) + 0.5f) / float2(float(w), float(h));
  float2 ndc = uv * 2.0f - 1.0f;
  ndc.y = -ndc.y;
  float3 ro = u.camPos.xyz;
  float3 rd = normalize(u.camFwd.xyz + ndc.x * u.camRight.xyz + ndc.y * u.camUp.xyz);
  float2 hitRange = intersectBox(ro, rd, {fmtFloat b}f);
  if (hitRange.y < hitRange.x || hitRange.y < 0.0f) \{ outTex.write(half4(0.0h), gid); return; }
  float tNear = hitRange.x;
  float tFar = hitRange.y;
  int steps = clamp(int(u.params.z), 32, 160);
  float dt = (tFar - tNear) / float(steps);
  float simTime = u.params.w;
  float tPrev2 = tNear;
  float fPrev2 = 0.0f;
  float tPrev = tNear;
  float fPrev = eval_implicit(ro + rd * tPrev, simTime);
  bool hit = (fPrev == 0.0f);
  float tHit = tPrev;
  if (!hit) \{
    for (int i = 1; i <= 160; ++i) \{
      if (i > steps) break;
      float tCur = (i == steps) ? tFar : (tNear + dt * float(i));
      float fCur = eval_implicit(ro + rd * tCur, simTime);
      // Strictly scale-invariant zero-set crossing (invariant under f -> c*f for all c > 0)
      if (fCur == 0.0f) \{
        tHit = tCur;
        hit = true;
        break;
      }
      if ((fPrev < 0.0f && fCur > 0.0f) || (fPrev > 0.0f && fCur < 0.0f)) \{
        float lo = tPrev, hi = tCur, fLo = fPrev;
        for (int k = 0; k < 6; ++k) \{
          float mid = 0.5f * (lo + hi);
          float fMid = eval_implicit(ro + rd * mid, simTime);
          if ((fLo < 0.0f && fMid < 0.0f) || (fLo > 0.0f && fMid > 0.0f)) \{
            lo = mid; fLo = fMid;
          } else \{
            hi = mid;
          }
        }
        tHit = 0.5f * (lo + hi);
        hit = true;
        break;
      }
      float s = fPrev > 0.0f ? 1.0f : -1.0f;
      float gPrev = s * fPrev;
      float gCur  = s * fCur;
      if (i == 1 && gPrev < gCur) \{
        float2 rHit = gs_refine_min(ro, rd, simTime, tPrev, tCur, tPrev, gPrev, s, gPrev, gCur);
        if (rHit.x > 0.5f) \{ tHit = rHit.y; hit = true; break; }
      }
      if (i >= 2) \{
        float gPrev2 = s * fPrev2;
        if (gPrev <= gPrev2 && gPrev <= gCur && (gPrev < gPrev2 || gPrev < gCur)) \{
          float2 rHit = gs_refine_min(ro, rd, simTime, tPrev2, tCur, tPrev, gPrev, s, gPrev2, gCur);
          if (rHit.x > 0.5f) \{ tHit = rHit.y; hit = true; break; }
        }
      }
      if (i == steps && gCur < gPrev) \{
        float2 rHit = gs_refine_min(ro, rd, simTime, tPrev, tCur, tPrev, gPrev, s, gPrev, gCur);
        if (rHit.x > 0.5f) \{ tHit = rHit.y; hit = true; break; }
      }
      tPrev2 = tPrev;
      fPrev2 = fPrev;
      tPrev = tCur;
      fPrev = fCur;
    }
  }
  if (!hit) \{ outTex.write(half4(0.0h), gid); return; }
  float3 pos = ro + rd * tHit;
  const float eps = {fmtFloat gradH}f;
  float f0 = eval_implicit(pos, simTime);
  float fpx = eval_implicit(pos + float3(eps,0.0f,0.0f), simTime), fmx = eval_implicit(pos - float3(eps,0.0f,0.0f), simTime);
  float fpy = eval_implicit(pos + float3(0.0f,eps,0.0f), simTime), fmy = eval_implicit(pos - float3(0.0f,eps,0.0f), simTime);
  float fpz = eval_implicit(pos + float3(0.0f,0.0f,eps), simTime), fmz = eval_implicit(pos - float3(0.0f,0.0f,eps), simTime);
  float3 grad = float3(fpx - fmx, fpy - fmy, fpz - fmz);
  float gMax = max(abs(grad.x), max(abs(grad.y), abs(grad.z)));
  float3 N = -rd;
  if (gMax > 1e-20f) \{
    N = normalize(grad / gMax);
  } else \{
    float3 h2 = float3(fpx + fmx - 2.0f * f0, fpy + fmy - 2.0f * f0, fpz + fmz - 2.0f * f0);
    float h2Max = max(abs(h2.x), max(abs(h2.y), abs(h2.z)));
    if (h2Max > 1e-20f) N = normalize(h2 / h2Max);
  }
  if (dot(N, -rd) < 0.0f) N = -N;
  float3 V = -rd;
  float3 Lk = normalize(float3(0.55f, 0.78f, 0.38f));
  float3 Lr = normalize(float3(-0.62f, 0.36f, -0.68f));
  float diffKey = max(0.0f, dot(N, Lk));
  float diffRim = max(0.0f, dot(N, Lr));
  float spec = pow(max(0.0f, dot(N, normalize(Lk + V))), 52.0f);
  float fres = pow(1.0f - max(0.0f, dot(N, V)), 3.0f);
  float3 lit = u.color.rgb * (0.24f + 0.74f * diffKey)
             + float3(0.52f, 0.85f, 1.0f) * (0.30f * diffRim + 0.44f * fres)
             + float3(1.0f, 0.97f, 0.92f) * (0.58f * spec);
  float outA = clamp(u.color.a * (0.76f + 0.24f * fres), 0.25f, 1.0f);
  outTex.write(half4(half3(clamp(lit, 0.0f, 1.0f)), half(outA)), gid);
}
"

/-- Parse ANY user-typed 3D implicit equation `f(x, y, z, t) = 0` and compile it directly
into a complete drop-in `OpnsShaderSource` triplet (`wgsl`, `glsl`, `msl`) clipped strictly
to the axis-aligned box `[-bound, bound]³` (`bound ∈ [0.5, 20.0]`)! -/
def compileImplicitExprToGpu (exprStr : String) (tag : String := "implicit_gpu")
    (bound : Float := 1.6) : Except String OpnsShaderSource := do
  let parsed ← parseExpr exprStr
  let b := clampImplicitBound bound
  let glsl := emitImplicitExprGlsl exprStr parsed b
  let wgsl := emitImplicitExprWgsl exprStr parsed b
  let msl  := emitImplicitExprMsl  exprStr parsed b
  return { hash := hashShaderTag tag s!"box:{fmtFloat b}:{glsl}", wgsl, glsl, msl }

end Grassmann.Codegen.GPUInit
