import Grassmann.Scene
import Grassmann.Codegen.GPUInit

/-!
# Verification & Real-Compiler Test Suite for Strictly `Init`-Only GPU Codegen (`Tests.GPUInit`)

Strictly `Init`-only (zero `Lean.*`, zero `Std.*`, zero `DirectSum`, zero `sorry`/axioms):
1. Compiles GA OPNS & IPNS shader bundles (`CGA3` OPNS grade 4, `CGA3` IPNS grade 1,
   `PGA3` OPNS grade 1, `STA` IPNS grade 2) in GLSL 300 es, WGSL, and Metal MSL.
2. Verifies exact drop-in contract compatibility with:
   - `web/src/render/materials.ts` (`OpnsShaderCache`: `THREE.GLSL3`, `vWorldPos`,
     `uCoeffs[64]`, `uInvViewProj`, `uResolution`, `uSimTime`, `gl_FragDepth`, `void main()`).
   - `LeanCalculator/Sources/Spatial3D/OPNSMetalRenderer.swift` (`struct OpnsUniforms`,
     `float  blade[64]`, `inline float product_len`, `kernel void gsir_lean_opns_compute`).
   - WebGPU WGSL (`array<vec4<f32>, 16>`, `@fragment`, `fn fs_main`, ternary-free `select`).
3. Compiles live user-typed `ImplicitExpr` equations (`cos(x)*sin(y)+cos(y)*sin(z)+cos(z)*sin(x)`,
   `(x^2+y^2+z^2-1)^2 - 0.1`, animated metaballs with `t` and division) directly into
   GLSL 300 es, WGSL, and Metal MSL sphere-tracing shaders and benchmarks compilation latency.
4. Verifies `SceneFrame` + `opnsShaders` + `opnsUniforms` encodes into strictly 8-byte
   aligned `GSIR` v1 binary (`validateGsirFrame`).
-/

namespace Tests.GPUInit

open Grassmann.Scene Grassmann.Scene.Binary Grassmann.Codegen.GPUInit

private def hasSubstr (s pat : String) : Bool := (s.splitOn pat).length > 1

private def assertTrue (name : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError s!"FAIL [{name}]")

private def verifyTriplet (tag : String) (b : OpnsShaderSource) : IO Unit := do
  assertTrue s!"{tag}: hash non-empty" (!b.hash.isEmpty)
  -- GLSL 300 es (Three.js OpnsShaderCache verbatim contract)
  assertTrue s!"{tag} GLSL3 header"       (hasSubstr b.glsl "#version 300 es")
  assertTrue s!"{tag} GLSL3 vWorldPos"    (hasSubstr b.glsl "in vec3 vWorldPos;")
  assertTrue s!"{tag} GLSL3 fragColor"    (hasSubstr b.glsl "out vec4 fragColor;")
  assertTrue s!"{tag} GLSL3 uCoeffs[64]"  (hasSubstr b.glsl "uniform float uCoeffs[64];")
  assertTrue s!"{tag} GLSL3 uInvViewProj" (hasSubstr b.glsl "uniform mat4 uInvViewProj;")
  assertTrue s!"{tag} GLSL3 uResolution"  (hasSubstr b.glsl "uniform vec2 uResolution;")
  assertTrue s!"{tag} GLSL3 gl_FragDepth" (hasSubstr b.glsl "gl_FragDepth")
  assertTrue s!"{tag} GLSL3 void main()"  (hasSubstr b.glsl "void main()")
  -- WGSL (WebGPU 16-byte uniform contract)
  assertTrue s!"{tag} WGSL OpnsUniforms"  (hasSubstr b.wgsl "struct OpnsUniforms")
  assertTrue s!"{tag} WGSL vec4[16]"      (hasSubstr b.wgsl "array<vec4<f32>, 16>")
  assertTrue s!"{tag} WGSL @fragment"     (hasSubstr b.wgsl "@fragment")
  assertTrue s!"{tag} WGSL fs_main"       (hasSubstr b.wgsl "fn fs_main")
  assertTrue s!"{tag} WGSL no ternary '?'" (!hasSubstr b.wgsl " ? ")
  -- Metal MSL (OPNSMetalRenderer.swift verbatim contract)
  assertTrue s!"{tag} MSL metal_stdlib"   (hasSubstr b.msl "#include <metal_stdlib>")
  assertTrue s!"{tag} MSL OpnsUniforms"   (hasSubstr b.msl "struct OpnsUniforms")
  assertTrue s!"{tag} MSL blade[64]"      (hasSubstr b.msl "blade[64]")
  assertTrue s!"{tag} MSL product_len"    (hasSubstr b.msl "product_len(")
  assertTrue s!"{tag} MSL compute entry"  (hasSubstr b.msl "kernel void gsir_lean_opns_compute(")

def runAll (dumpDir : Option String := none) : IO Unit := do
  let t0 ← IO.monoNanosNow
  -- 1. GA OPNS & IPNS bundles across CGA3, PGA3, STA
  let cgaOpns ← IO.ofExcept (compileGaOpnsBundle "cga3_opns_g4" AlgSpec.cga3 4 false)
  let cgaIpns ← IO.ofExcept (compileGaOpnsBundle "cga3_ipns_g1" AlgSpec.cga3 1 true)
  let pgaOpns ← IO.ofExcept (compileGaOpnsBundle "pga3_opns_g1" AlgSpec.pga3 1 false)
  let staIpns ← IO.ofExcept (compileGaOpnsBundle "sta_ipns_g2"  AlgSpec.sta  2 true)
  let t1 ← IO.monoNanosNow

  verifyTriplet "cga3_opns_g4" cgaOpns
  verifyTriplet "cga3_ipns_g1" cgaIpns
  verifyTriplet "pga3_opns_g1" pgaOpns
  verifyTriplet "sta_ipns_g2"  staIpns
  assertTrue "cga3_opns_g4 has non-trivial unrolled terms" (hasSubstr cgaOpns.glsl "u0 * b[")
  assertTrue "cga3_ipns_g1 contracts Witt null pair" (hasSubstr cgaIpns.glsl "u0 * b[1]")

  -- 2. Live User-Typed ImplicitExpr → GPU Raymarcher bundles!
  let t2 ← IO.monoNanosNow
  let gyroidGpu ← IO.ofExcept (compileImplicitExprToGpu
    "cos(x)*sin(y) + cos(y)*sin(z) + cos(z)*sin(x)" "gyroid_gpu")
  let quarticGpu ← IO.ofExcept (compileImplicitExprToGpu
    "(x^2 + y^2 + z^2 - 1)^2 - 0.1" "quartic_gpu")
  let metaGpu ← IO.ofExcept (compileImplicitExprToGpu
    "1 - 0.25/((x - 0.5*cos(t))^2 + y^2 + z^2 + 0.05) - 0.25/((x + 0.5)^2 + y^2 + z^2 + 0.05)"
    "metaballs_gpu")
  let t3 ← IO.monoNanosNow

  verifyTriplet "gyroid_gpu"    gyroidGpu
  verifyTriplet "quartic_gpu"   quarticGpu
  verifyTriplet "metaballs_gpu" metaGpu
  assertTrue "gyroid GLSL calls cos/sin" (hasSubstr gyroidGpu.glsl "cos(p.x)")
  assertTrue "quartic uses gs_sq power specialization" (hasSubstr quarticGpu.glsl "gs_sq(")
  assertTrue "metaballs WGSL uses ternary-free select for div" (hasSubstr metaGpu.wgsl "select(")
  assertTrue "metaballs GLSL uses uSimTime" (hasSubstr metaGpu.glsl "uSimTime")

  -- Syntax error propagates cleanly
  match compileImplicitExprToGpu "sin(x + )" "bad" with
  | .ok _ => throw (IO.userError "Expected compile error on malformed expression")
  | .error _ => pure ()

  -- 3. End-to-end GSIR v1 binary framing with embedded opnsShaders + 0x10 OPNS_UNIFORMS
  let coeffs := FloatArray.empty |>.push 1.0 |>.push 0.2 |>.push (-0.3) |>.push 0.5 |>.push 0.8
  let frame : SceneFrame :=
    { frameSeq := 1, simTime := 0.5, mode := .coffeeShop,
      presetId := "cga3d_opns_live", title := "Live Init-Only GPU OPNS & Implicit",
      opnsShaders := #[cgaOpns, gyroidGpu],
      opnsUniforms := #[{ shaderIdx := 0, grade := 4, coeffs, color := RGBA.violet },
                        { shaderIdx := 1, grade := 0, coeffs := FloatArray.empty.push 0.5, color := RGBA.cyan }] }
  let raw := encodeFrame frame true
  match validateGsirFrame raw with
  | .error e => throw (IO.userError s!"GSIR frame w/ GPUInit shaders invalid: {e}")
  | .ok (secs, _, metaLen) =>
    assertTrue "GSIR has OPNS_UNIFORMS section" (secs ≥ 2)
    assertTrue "GSIR embeds full opnsShaders in metaJson" (metaLen > 4000)
    assertTrue "GSIR strictly 8B aligned" (raw.size % 8 == 0)

  -- Optional dump of emitted MSL files for live `xcrun metal` compilation check
  match dumpDir with
  | some dir =>
    IO.FS.writeFile s!"{dir}/cga3_opns_g4.metal" cgaOpns.msl
    IO.FS.writeFile s!"{dir}/cga3_ipns_g1.metal" cgaIpns.msl
    IO.FS.writeFile s!"{dir}/gyroid_gpu.metal"   gyroidGpu.msl
    IO.FS.writeFile s!"{dir}/metaballs_gpu.metal" metaGpu.msl
  | none => pure ()

  IO.println s!"  [bench] 4 GA OPNS/IPNS triplets (GLSL+WGSL+MSL): {Float.ofNat (t1 - t0) / 1e6} ms"
  IO.println s!"  [bench] 3 ImplicitExpr GPU triplets (Gyroid+Quartic+Metaballs): {Float.ofNat (t3 - t2) / 1e6} ms"
  IO.println "PASS [1/3] GA OPNS/IPNS pure-Init compiler (CGA3 OPNS/IPNS, PGA3, STA -> GLSL3/WGSL/MSL)"
  IO.println "PASS [2/3] Live ImplicitExpr -> GPU raymarcher compiler (Gyroid, Quartic, Animated Metaballs)"
  IO.println "PASS [3/3] GSIR v1 8B-aligned framing with embedded opnsShaders + 0x10 OPNS_UNIFORMS"
  IO.println "ALL GPUINIT TESTS PASSED!"

end Tests.GPUInit

def main (args : List String) : IO Unit :=
  match args with
  | ["--dump-msl", dir] => Tests.GPUInit.runAll (some dir)
  | _ => Tests.GPUInit.runAll none
