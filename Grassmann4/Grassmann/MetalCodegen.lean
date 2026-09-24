/-
  Grassmann/MetalCodegen.lean - Generate Metal compute shaders from Lean specs

  Strategy:
  1. Precompute sign tables at Lean compile time (no runtime cost)
  2. Generate specialized Metal kernels for each signature
  3. Batch parallelism: one thread per multivector product

  Design principles:
  - Fixed dimension per kernel (GPU prefers static sizes)
  - Sign table as constant array (no runtime computation)
  - AoS layout for simplicity, SoA version possible later
-/
import Grassmann.Parity

namespace Grassmann.Metal

variable {n : ℕ}

/-! ## Sign Table Generation

The sign table for signature `sig` is a 2^n × 2^n matrix where
`signTable[i][j]` = sign of `blade[i] * blade[j]` in the geometric product.

This is precomputed at Lean compile time and embedded in Metal as `constant`.
-/

/-- Compute full sign table for a signature -/
def computeSignTable (sig : Signature n) : Array (Array Int) :=
  let size := 2^n
  Array.ofFn fun i : Fin size =>
    Array.ofFn fun j : Fin size =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      geometricSign sig bi bj

/-- Compute wedge sign table (0 when blades share basis vectors) -/
def computeWedgeSignTable (sig : Signature n) : Array (Array Int) :=
  let size := 2^n
  Array.ofFn fun i : Fin size =>
    Array.ofFn fun j : Fin size =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      wedgeSign sig bi bj

/-- Output index table: outputIdx[i][j] = i XOR j -/
def computeOutputIdxTable (n : ℕ) : Array (Array Nat) :=
  let size := 2^n
  Array.ofFn fun i : Fin size =>
    Array.ofFn fun j : Fin size =>
      (BitVec.ofNat n i.val ^^^ BitVec.ofNat n j.val).toNat

/-! ## Metal Code Generation -/

/-- Format sign table as Metal constant array -/
def signTableToMetal (table : Array (Array Int)) (name : String) : String :=
  let size := table.size
  let rows := table.toList.map fun row =>
    "    {" ++ String.intercalate ", " (row.toList.map fun x =>
      if x < 0 then toString x else " " ++ toString x) ++ "}"
  s!"constant int {name}[{size}][{size}] = \{\n" ++
    String.intercalate ",\n" rows ++ "\n};\n"

/-- Format output index table as Metal constant array -/
def outputIdxTableToMetal (table : Array (Array Nat)) : String :=
  let size := table.size
  let rows := table.toList.map fun row =>
    "    {" ++ String.intercalate ", " (row.toList.map toString) ++ "}"
  s!"constant uint outputIdx[{size}][{size}] = \{\n" ++
    String.intercalate ",\n" rows ++ "\n};\n"

/-- Generate Metal struct for multivector -/
def multivectorStructMetal (sigName : String) (n : ℕ) : String :=
  let size := 2^n
  s!"// Multivector for {sigName} ({n}D, {size} blades)
struct Multivector_{sigName} \{
    float coeffs[{size}];
};
"

/-- Generate batch geometric product kernel -/
def geometricProductKernelMetal (sigName : String) (n : ℕ) : String :=
  let size := 2^n
  s!"// Batch geometric product: result[gid] = a[gid] * b[gid]
kernel void geometricProduct_{sigName}(
    device const Multivector_{sigName}* a [[buffer(0)]],
    device const Multivector_{sigName}* b [[buffer(1)]],
    device Multivector_{sigName}* result [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) \{
    // Zero output
    Multivector_{sigName} out;
    for (uint k = 0; k < {size}; k++) out.coeffs[k] = 0.0f;

    // Accumulate contributions from all pairs
    for (uint i = 0; i < {size}; i++) \{
        float ai = a[gid].coeffs[i];
        if (ai == 0.0f) continue;  // Skip zeros

        for (uint j = 0; j < {size}; j++) \{
            float bj = b[gid].coeffs[j];
            if (bj == 0.0f) continue;  // Skip zeros

            int sign = signs_{sigName}[i][j];
            if (sign != 0) \{
                uint k = outputIdx[i][j];
                out.coeffs[k] += float(sign) * ai * bj;
            }
        }
    }

    result[gid] = out;
}
"

/-- Generate sandwich product kernel: result = a * x * reverse(a) -/
def sandwichProductKernelMetal (sigName : String) (n : ℕ) : String :=
  let size := 2^n
  -- Precompute reverse signs: (-1)^(k(k-1)/2) for each grade
  s!"// Sandwich product: result[gid] = a[gid] * x[gid] * reverse(a[gid])
// Used for rotations and reflections
kernel void sandwichProduct_{sigName}(
    device const Multivector_{sigName}* a [[buffer(0)]],
    device const Multivector_{sigName}* x [[buffer(1)]],
    device Multivector_{sigName}* result [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) \{
    // First compute temp = a * x
    Multivector_{sigName} temp;
    for (uint k = 0; k < {size}; k++) temp.coeffs[k] = 0.0f;

    for (uint i = 0; i < {size}; i++) \{
        float ai = a[gid].coeffs[i];
        if (ai == 0.0f) continue;
        for (uint j = 0; j < {size}; j++) \{
            float xj = x[gid].coeffs[j];
            if (xj == 0.0f) continue;
            int sign = signs_{sigName}[i][j];
            if (sign != 0) \{
                uint k = outputIdx[i][j];
                temp.coeffs[k] += float(sign) * ai * xj;
            }
        }
    }

    // Now compute result = temp * reverse(a)
    Multivector_{sigName} out;
    for (uint k = 0; k < {size}; k++) out.coeffs[k] = 0.0f;

    for (uint i = 0; i < {size}; i++) \{
        float ti = temp.coeffs[i];
        if (ti == 0.0f) continue;
        for (uint j = 0; j < {size}; j++) \{
            // Apply reverse sign to a[j]
            float aj = a[gid].coeffs[j] * reverseSign_{sigName}[j];
            if (aj == 0.0f) continue;
            int sign = signs_{sigName}[i][j];
            if (sign != 0) \{
                uint k = outputIdx[i][j];
                out.coeffs[k] += float(sign) * ti * aj;
            }
        }
    }

    result[gid] = out;
}
"

/-- Compute reverse signs for each blade index -/
def computeReverseSignTable (n : ℕ) : Array Int :=
  Array.ofFn fun i : Fin (2^n) =>
    let g := grade (BitVec.ofNat n i.val)
    if (g * (g - 1) / 2) % 2 == 0 then 1 else -1

/-- Format reverse sign table as Metal constant -/
def reverseSignTableToMetal (table : Array Int) (sigName : String) : String :=
  let size := table.size
  let entries := String.intercalate ", " (table.toList.map fun x =>
    if x < 0 then toString x else " " ++ toString x)
  s!"constant int reverseSign_{sigName}[{size}] = \{{entries}};\n"

/-- Generate complete Metal shader file for a signature -/
def generateMetalShader (sig : Signature n) (sigName : String) : String :=
  let signTable := computeSignTable sig
  let outputTable := computeOutputIdxTable n
  let reverseTable := computeReverseSignTable n
  "// Auto-generated Metal shader for Grassmann algebra\n" ++
  "// Signature: " ++ sigName ++ " (" ++ toString n ++ "D)\n" ++
  "// Generated from Lean specifications\n\n" ++
  "#include <metal_stdlib>\n" ++
  "using namespace metal;\n\n" ++
  "// Precomputed sign table for geometric product\n" ++
  signTableToMetal signTable s!"signs_{sigName}" ++ "\n" ++
  "// Output index table: i XOR j\n" ++
  outputIdxTableToMetal outputTable ++ "\n" ++
  "// Reverse signs for dagger operation\n" ++
  reverseSignTableToMetal reverseTable sigName ++ "\n" ++
  multivectorStructMetal sigName n ++ "\n" ++
  geometricProductKernelMetal sigName n ++ "\n" ++
  sandwichProductKernelMetal sigName n

/-! ## File Output -/

/-- Write Metal shader to file -/
def writeMetalShader (sig : Signature n) (sigName : String) (path : System.FilePath) : IO Unit := do
  let content := generateMetalShader sig sigName
  IO.FS.writeFile path content
  IO.println s!"Wrote Metal shader to {path}"

/-! ## Swift Runner Template -/

/-- Generate Swift runner code -/
def generateSwiftRunner (sigName : String) (n : ℕ) : String :=
  let size := 2^n
  s!"#!/usr/bin/env swift
// Swift runner for {sigName} Grassmann algebra GPU operations
// Generated from Lean specifications

import Metal
import Foundation

// Must match Metal struct layout
struct Multivector_{sigName} \{
    var coeffs: ({String.intercalate ", " (List.replicate size "Float")})

    static var zero: Multivector_{sigName} \{
        Multivector_{sigName}(coeffs: ({String.intercalate ", " (List.replicate size "0.0")}))
    }

    // Create basis vector e_i (i is 0-indexed)
    static func basis(_ i: Int) -> Multivector_{sigName} \{
        var m = zero
        withUnsafeMutablePointer(to: &m.coeffs) \{ ptr in
            let arr = UnsafeMutableRawPointer(ptr).assumingMemoryBound(to: Float.self)
            arr[1 << i] = 1.0
        }
        return m
    }

    subscript(i: Int) -> Float \{
        get \{
            withUnsafePointer(to: coeffs) \{ ptr in
                UnsafeRawPointer(ptr).assumingMemoryBound(to: Float.self)[i]
            }
        }
        set \{
            withUnsafeMutablePointer(to: &coeffs) \{ ptr in
                UnsafeMutableRawPointer(ptr).assumingMemoryBound(to: Float.self)[i] = newValue
            }
        }
    }
}

class GrassmannGPU_{sigName} \{
    let device: MTLDevice
    let commandQueue: MTLCommandQueue
    let geometricProductPipeline: MTLComputePipelineState
    let sandwichProductPipeline: MTLComputePipelineState

    init(shaderPath: String) throws \{
        guard let device = MTLCreateSystemDefaultDevice() else \{
            throw NSError(domain: \"Metal\", code: 1, userInfo: [NSLocalizedDescriptionKey: \"Metal not supported\"])
        }
        self.device = device

        guard let commandQueue = device.makeCommandQueue() else \{
            throw NSError(domain: \"Metal\", code: 2, userInfo: [NSLocalizedDescriptionKey: \"Failed to create command queue\"])
        }
        self.commandQueue = commandQueue

        let shaderSource = try String(contentsOfFile: shaderPath, encoding: .utf8)
        let library = try device.makeLibrary(source: shaderSource, options: nil)

        guard let geoFunc = library.makeFunction(name: \"geometricProduct_{sigName}\"),
              let sandFunc = library.makeFunction(name: \"sandwichProduct_{sigName}\") else \{
            throw NSError(domain: \"Metal\", code: 3, userInfo: [NSLocalizedDescriptionKey: \"Failed to find kernel functions\"])
        }

        self.geometricProductPipeline = try device.makeComputePipelineState(function: geoFunc)
        self.sandwichProductPipeline = try device.makeComputePipelineState(function: sandFunc)
    }

    /// Batch geometric product: result[i] = a[i] * b[i]
    func geometricProduct(_ a: [Multivector_{sigName}], _ b: [Multivector_{sigName}]) -> [Multivector_{sigName}] \{
        precondition(a.count == b.count)
        let count = a.count
        let size = MemoryLayout<Multivector_{sigName}>.size

        let aBuffer = device.makeBuffer(bytes: a, length: count * size, options: .storageModeShared)!
        let bBuffer = device.makeBuffer(bytes: b, length: count * size, options: .storageModeShared)!
        let resultBuffer = device.makeBuffer(length: count * size, options: .storageModeShared)!

        let commandBuffer = commandQueue.makeCommandBuffer()!
        let encoder = commandBuffer.makeComputeCommandEncoder()!
        encoder.setComputePipelineState(geometricProductPipeline)
        encoder.setBuffer(aBuffer, offset: 0, index: 0)
        encoder.setBuffer(bBuffer, offset: 0, index: 1)
        encoder.setBuffer(resultBuffer, offset: 0, index: 2)

        let gridSize = MTLSize(width: count, height: 1, depth: 1)
        let threadGroupSize = MTLSize(width: min(64, count), height: 1, depth: 1)
        encoder.dispatchThreads(gridSize, threadsPerThreadgroup: threadGroupSize)
        encoder.endEncoding()

        commandBuffer.commit()
        commandBuffer.waitUntilCompleted()

        let resultPtr = resultBuffer.contents().bindMemory(to: Multivector_{sigName}.self, capacity: count)
        return Array(UnsafeBufferPointer(start: resultPtr, count: count))
    }

    /// Batch sandwich product: result[i] = a[i] * x[i] * reverse(a[i])
    func sandwichProduct(_ a: [Multivector_{sigName}], _ x: [Multivector_{sigName}]) -> [Multivector_{sigName}] \{
        precondition(a.count == x.count)
        let count = a.count
        let size = MemoryLayout<Multivector_{sigName}>.size

        let aBuffer = device.makeBuffer(bytes: a, length: count * size, options: .storageModeShared)!
        let xBuffer = device.makeBuffer(bytes: x, length: count * size, options: .storageModeShared)!
        let resultBuffer = device.makeBuffer(length: count * size, options: .storageModeShared)!

        let commandBuffer = commandQueue.makeCommandBuffer()!
        let encoder = commandBuffer.makeComputeCommandEncoder()!
        encoder.setComputePipelineState(sandwichProductPipeline)
        encoder.setBuffer(aBuffer, offset: 0, index: 0)
        encoder.setBuffer(xBuffer, offset: 0, index: 1)
        encoder.setBuffer(resultBuffer, offset: 0, index: 2)

        let gridSize = MTLSize(width: count, height: 1, depth: 1)
        let threadGroupSize = MTLSize(width: min(64, count), height: 1, depth: 1)
        encoder.dispatchThreads(gridSize, threadsPerThreadgroup: threadGroupSize)
        encoder.endEncoding()

        commandBuffer.commit()
        commandBuffer.waitUntilCompleted()

        let resultPtr = resultBuffer.contents().bindMemory(to: Multivector_{sigName}.self, capacity: count)
        return Array(UnsafeBufferPointer(start: resultPtr, count: count))
    }
}

// Example usage
func main() throws \{
    let gpu = try GrassmannGPU_{sigName}(shaderPath: \"./{sigName.toLower}_grassmann.metal\")

    // Create some test vectors
    let e1 = Multivector_{sigName}.basis(0)
    let e2 = Multivector_{sigName}.basis(1)

    // Batch test: e1 * e1 should give scalar 1
    let results = gpu.geometricProduct([e1, e2], [e1, e2])
    print(\"e1*e1 scalar part: \\(results[0][0])\")  // Should be 1.0
    print(\"e2*e2 scalar part: \\(results[1][0])\")  // Should be 1.0

    // Benchmark with many operations
    let count = 100_000
    let rotors = (0..<count).map \{ _ in e1 }  // Simplified
    let vectors = (0..<count).map \{ _ in e2 }

    let start = Date()
    let _ = gpu.sandwichProduct(rotors, vectors)
    let elapsed = Date().timeIntervalSince(start)
    print(\"\\(count) sandwich products in \\(elapsed * 1000)ms (\\(Double(count)/elapsed/1_000_000) M/s)\")
}

try main()
"

/-! ## Generate for standard signatures -/

-- R3: Euclidean 3D (e1²=e2²=e3²=1)
#eval IO.println (generateMetalShader R3 "R3")

-- Generate Swift runner
#eval! IO.println (generateSwiftRunner "R3" 3)

-- Generate sign table for inspection
#eval computeSignTable R3

-- Generate PGA signature (Projective Geometric Algebra)
-- R3,0,1: 3 positive, 0 negative, 1 zero (e4² = 0)
def PGA3D : Signature 4 := Signature.clr 3 0 1  -- e₁,e₂,e₃ positive, e₄ degenerate

/-! ## Physics Kernels

Batch physics kernels for rigid body simulation.
Uses PGA motors for transforms and motor velocity for dynamics.
-/

/-- Generate batch motor integration kernel.
    Integrates motor velocity to update motor pose: M' = exp(dt * V) * M -/
def motorIntegrationKernelMetal : String :=
  "// Batch motor integration: motors[gid] = exp(dt * velocities[gid]) * motors[gid]
// Uses first-order approximation: exp(B) ≈ 1 + B for small timesteps

struct MotorVelocity {
    float omega12;  // angular velocity components
    float omega13;
    float omega23;
    float v01;      // linear velocity components
    float v02;
    float v03;
};

kernel void integrateMotors(
    device Multivector_PGA3* motors [[buffer(0)]],
    device const MotorVelocity* velocities [[buffer(1)]],
    constant float& dt [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    MotorVelocity v = velocities[gid];
    Multivector_PGA3 M = motors[gid];

    // Build velocity bivector: dt * (angular + linear)
    Multivector_PGA3 B;
    for (uint i = 0; i < 16; i++) B.coeffs[i] = 0.0f;

    // Bivector indices in PGA3: e01=3, e02=5, e03=9, e12=6, e13=10, e23=12
    B.coeffs[3] = dt * v.v01;
    B.coeffs[5] = dt * v.v02;
    B.coeffs[9] = dt * v.v03;
    B.coeffs[6] = dt * v.omega12;
    B.coeffs[10] = dt * v.omega13;
    B.coeffs[12] = dt * v.omega23;

    // First-order exponential: exp(B) ≈ 1 + B
    Multivector_PGA3 expB;
    for (uint i = 0; i < 16; i++) expB.coeffs[i] = B.coeffs[i];
    expB.coeffs[0] = 1.0f;  // scalar part = 1

    // M' = expB * M (geometric product)
    Multivector_PGA3 out;
    for (uint k = 0; k < 16; k++) out.coeffs[k] = 0.0f;

    for (uint i = 0; i < 16; i++) {
        float ai = expB.coeffs[i];
        if (ai == 0.0f) continue;
        for (uint j = 0; j < 16; j++) {
            float bj = M.coeffs[j];
            if (bj == 0.0f) continue;
            int sign = signs_PGA3[i][j];
            if (sign != 0) {
                uint k = outputIdx[i][j];
                out.coeffs[k] += float(sign) * ai * bj;
            }
        }
    }

    motors[gid] = out;
}
"

/-- Generate batch sphere-sphere collision detection kernel.
    Outputs collision pairs with penetration depth and normal. -/
def sphereCollisionKernelMetal : String :=
  "// Batch sphere-sphere collision detection
// Input: sphere positions (xyz) and radii
// Output: collision info for each pair

struct Sphere {
    float x, y, z, radius;
};

struct CollisionInfo {
    uint i, j;           // indices of colliding spheres
    float penetration;   // penetration depth
    float nx, ny, nz;    // contact normal (from i to j)
    float cx, cy, cz;    // contact point
};

// Kernel to detect collision between two specific spheres
kernel void detectSphereCollision(
    device const Sphere* spheres [[buffer(0)]],
    device CollisionInfo* collisions [[buffer(1)]],
    device atomic_uint* collisionCount [[buffer(2)]],
    constant uint& numSpheres [[buffer(3)]],
    uint2 gid [[thread_position_in_grid]]
) {
    uint i = gid.x;
    uint j = gid.y;

    // Only check upper triangle (i < j)
    if (i >= j || j >= numSpheres) return;

    Sphere si = spheres[i];
    Sphere sj = spheres[j];

    float dx = sj.x - si.x;
    float dy = sj.y - si.y;
    float dz = sj.z - si.z;
    float distSq = dx*dx + dy*dy + dz*dz;
    float minDist = si.radius + sj.radius;

    if (distSq < minDist * minDist && distSq > 1e-10f) {
        float dist = sqrt(distSq);
        float invDist = 1.0f / dist;

        // Allocate collision slot
        uint slot = atomic_fetch_add_explicit(collisionCount, 1, memory_order_relaxed);

        CollisionInfo info;
        info.i = i;
        info.j = j;
        info.penetration = minDist - dist;
        info.nx = dx * invDist;
        info.ny = dy * invDist;
        info.nz = dz * invDist;

        // Contact point at surface of sphere i toward sphere j
        info.cx = si.x + si.radius * info.nx;
        info.cy = si.y + si.radius * info.ny;
        info.cz = si.z + si.radius * info.nz;

        collisions[slot] = info;
    }
}
"

/-- Generate floor collision kernel.
    Detects sphere-floor collisions and computes bounce impulse. -/
def floorCollisionKernelMetal : String :=
  "// Batch floor collision detection and response
// Input: sphere positions, velocities, floor y-coordinate
// Output: updated velocities after bounce

kernel void handleFloorCollision(
    device float3* positions [[buffer(0)]],
    device float3* velocities [[buffer(1)]],
    constant float& floorY [[buffer(2)]],
    constant float& radius [[buffer(3)]],
    constant float& restitution [[buffer(4)]],
    uint gid [[thread_position_in_grid]]
) {
    float3 pos = positions[gid];
    float3 vel = velocities[gid];

    float penetration = floorY + radius - pos.y;

    if (penetration > 0.0f) {
        // Collision detected
        if (vel.y < 0.0f) {
            // Bounce: reflect y velocity
            vel.y = -vel.y * restitution;
        }

        // Push out of floor
        pos.y = floorY + radius;

        positions[gid] = pos;
        velocities[gid] = vel;
    }
}
"

/-- Generate batch gravity application kernel -/
def gravityKernelMetal : String :=
  "// Apply gravity to all bodies
kernel void applyGravity(
    device float3* velocities [[buffer(0)]],
    constant float& gravity [[buffer(1)]],
    constant float& dt [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    velocities[gid].y -= gravity * dt;
}
"

/-- Generate batch position integration kernel -/
def positionIntegrationKernelMetal : String :=
  "// Integrate positions using velocities
kernel void integratePositions(
    device float3* positions [[buffer(0)]],
    device const float3* velocities [[buffer(1)]],
    constant float& dt [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    positions[gid] += velocities[gid] * dt;
}
"

/-! ## Constraint Solver Kernels

GPU-accelerated constraint solving using motor gradient descent.
-/

/-- Ball joint data structure for GPU -/
def ballJointStructMetal : String :=
  "// Ball joint constraint
struct BallJoint {
    uint body1Idx;    // First body index
    uint body2Idx;    // Second body index
    float3 anchor1;   // Anchor in body1 local frame
    float3 anchor2;   // Anchor in body2 local frame
};
"

/-- Kernel to compute ball joint residuals in batch -/
def ballJointResidualKernelMetal : String :=
  "// Compute ball joint residual (distance between world-space anchors)
kernel void computeBallJointResidual(
    device const Multivector_PGA3* motors [[buffer(0)]],
    device const BallJoint* joints [[buffer(1)]],
    device float* residuals [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    BallJoint joint = joints[gid];
    Multivector_PGA3 m1 = motors[joint.body1Idx];
    Multivector_PGA3 m2 = motors[joint.body2Idx];

    // Transform anchor1 by motor1 (simplified - assumes motor encodes position)
    float3 p1 = float3(
        2.0f * m1.coeffs[3] + joint.anchor1.x,   // e01 component + local
        2.0f * m1.coeffs[5] + joint.anchor1.y,   // e02 component
        2.0f * m1.coeffs[9] + joint.anchor1.z    // e03 component
    );

    // Transform anchor2 by motor2
    float3 p2 = float3(
        2.0f * m2.coeffs[3] + joint.anchor2.x,
        2.0f * m2.coeffs[5] + joint.anchor2.y,
        2.0f * m2.coeffs[9] + joint.anchor2.z
    );

    float3 d = p2 - p1;
    residuals[gid] = sqrt(d.x*d.x + d.y*d.y + d.z*d.z);
}
"

/-- Kernel to compute motor gradients for constraint solving -/
def motorGradientKernelMetal : String :=
  "// Compute gradient of total residual w.r.t. motor coefficients
// Uses finite differences (ε = 1e-6)
kernel void computeMotorGradient(
    device const Multivector_PGA3* motors [[buffer(0)]],
    device const BallJoint* joints [[buffer(1)]],
    constant uint& numJoints [[buffer(2)]],
    device float* gradients [[buffer(3)]],  // 16 floats per body
    constant float& epsilon [[buffer(4)]],
    uint gid [[thread_position_in_grid]]
) {
    uint bodyIdx = gid / 16;
    uint coeffIdx = gid % 16;

    // Compute base residual
    float baseResidual = 0.0f;
    for (uint j = 0; j < numJoints; j++) {
        if (joints[j].body1Idx == bodyIdx || joints[j].body2Idx == bodyIdx) {
            // Compute this joint's contribution
            Multivector_PGA3 m1 = motors[joints[j].body1Idx];
            Multivector_PGA3 m2 = motors[joints[j].body2Idx];

            float3 p1 = float3(
                2.0f * m1.coeffs[3] + joints[j].anchor1.x,
                2.0f * m1.coeffs[5] + joints[j].anchor1.y,
                2.0f * m1.coeffs[9] + joints[j].anchor1.z
            );
            float3 p2 = float3(
                2.0f * m2.coeffs[3] + joints[j].anchor2.x,
                2.0f * m2.coeffs[5] + joints[j].anchor2.y,
                2.0f * m2.coeffs[9] + joints[j].anchor2.z
            );
            float3 d = p2 - p1;
            baseResidual += sqrt(d.x*d.x + d.y*d.y + d.z*d.z);
        }
    }

    // Perturb coefficient and recompute
    float perturbedResidual = 0.0f;
    for (uint j = 0; j < numJoints; j++) {
        if (joints[j].body1Idx == bodyIdx || joints[j].body2Idx == bodyIdx) {
            Multivector_PGA3 m1 = motors[joints[j].body1Idx];
            Multivector_PGA3 m2 = motors[joints[j].body2Idx];

            // Apply perturbation
            if (joints[j].body1Idx == bodyIdx) {
                m1.coeffs[coeffIdx] += epsilon;
            }
            if (joints[j].body2Idx == bodyIdx) {
                m2.coeffs[coeffIdx] += epsilon;
            }

            float3 p1 = float3(
                2.0f * m1.coeffs[3] + joints[j].anchor1.x,
                2.0f * m1.coeffs[5] + joints[j].anchor1.y,
                2.0f * m1.coeffs[9] + joints[j].anchor1.z
            );
            float3 p2 = float3(
                2.0f * m2.coeffs[3] + joints[j].anchor2.x,
                2.0f * m2.coeffs[5] + joints[j].anchor2.y,
                2.0f * m2.coeffs[9] + joints[j].anchor2.z
            );
            float3 d = p2 - p1;
            perturbedResidual += sqrt(d.x*d.x + d.y*d.y + d.z*d.z);
        }
    }

    gradients[gid] = (perturbedResidual - baseResidual) / epsilon;
}
"

/-- Kernel to update motors using gradient descent -/
def motorUpdateKernelMetal : String :=
  "// Update motors using gradient descent step
kernel void updateMotors(
    device Multivector_PGA3* motors [[buffer(0)]],
    device const float* gradients [[buffer(1)]],  // 16 floats per body
    constant float& stepSize [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    uint bodyIdx = gid / 16;
    uint coeffIdx = gid % 16;

    motors[bodyIdx].coeffs[coeffIdx] -= stepSize * gradients[gid];

    // Normalize motor (ensure M·M† ≈ 1)
    // For simplicity, just normalize scalar + pseudoscalar part
    if (coeffIdx == 0) {
        Multivector_PGA3 m = motors[bodyIdx];
        float normSq = m.coeffs[0] * m.coeffs[0];
        for (uint i = 1; i < 16; i++) {
            normSq += m.coeffs[i] * m.coeffs[i];
        }
        if (normSq > 1e-10f) {
            float scale = 1.0f / sqrt(normSq);
            for (uint i = 0; i < 16; i++) {
                motors[bodyIdx].coeffs[i] *= scale;
            }
        }
    }
}
"

/-- Complete constraint solver iteration kernel -/
def constraintSolverKernelMetal : String :=
  "// Single iteration of constraint solver
// Combines gradient computation and motor update
kernel void constraintSolverStep(
    device Multivector_PGA3* motors [[buffer(0)]],
    device const BallJoint* joints [[buffer(1)]],
    constant uint& numJoints [[buffer(2)]],
    constant uint& numBodies [[buffer(3)]],
    constant float& stepSize [[buffer(4)]],
    device float* tempGradients [[buffer(5)]],  // Workspace
    uint gid [[thread_position_in_grid]]
) {
    uint bodyIdx = gid;
    if (bodyIdx >= numBodies) return;

    const float epsilon = 1e-6f;

    // Compute gradient for this body (all 16 coefficients)
    for (uint coeffIdx = 0; coeffIdx < 16; coeffIdx++) {
        float baseResidual = 0.0f;
        float perturbedResidual = 0.0f;

        for (uint j = 0; j < numJoints; j++) {
            BallJoint joint = joints[j];
            if (joint.body1Idx != bodyIdx && joint.body2Idx != bodyIdx) continue;

            Multivector_PGA3 m1 = motors[joint.body1Idx];
            Multivector_PGA3 m2 = motors[joint.body2Idx];

            // Base residual
            float3 p1 = float3(2.0f*m1.coeffs[3], 2.0f*m1.coeffs[5], 2.0f*m1.coeffs[9])
                      + joint.anchor1;
            float3 p2 = float3(2.0f*m2.coeffs[3], 2.0f*m2.coeffs[5], 2.0f*m2.coeffs[9])
                      + joint.anchor2;
            float3 d = p2 - p1;
            baseResidual += length(d);

            // Perturbed residual
            if (joint.body1Idx == bodyIdx) m1.coeffs[coeffIdx] += epsilon;
            if (joint.body2Idx == bodyIdx) m2.coeffs[coeffIdx] += epsilon;

            p1 = float3(2.0f*m1.coeffs[3], 2.0f*m1.coeffs[5], 2.0f*m1.coeffs[9])
               + joint.anchor1;
            p2 = float3(2.0f*m2.coeffs[3], 2.0f*m2.coeffs[5], 2.0f*m2.coeffs[9])
               + joint.anchor2;
            d = p2 - p1;
            perturbedResidual += length(d);
        }

        float grad = (perturbedResidual - baseResidual) / epsilon;
        motors[bodyIdx].coeffs[coeffIdx] -= stepSize * grad;
    }

    // Normalize motor
    float normSq = 0.0f;
    for (uint i = 0; i < 16; i++) {
        normSq += motors[bodyIdx].coeffs[i] * motors[bodyIdx].coeffs[i];
    }
    if (normSq > 1e-10f) {
        float scale = 1.0f / sqrt(normSq);
        for (uint i = 0; i < 16; i++) {
            motors[bodyIdx].coeffs[i] *= scale;
        }
    }
}
"

/-- Generate complete physics shader file -/
def generatePhysicsShader : String :=
  "// Auto-generated Metal physics shaders for Grassmann algebra
// Generated from Lean specifications

#include <metal_stdlib>
using namespace metal;

" ++ motorIntegrationKernelMetal ++ "\n" ++
    sphereCollisionKernelMetal ++ "\n" ++
    floorCollisionKernelMetal ++ "\n" ++
    gravityKernelMetal ++ "\n" ++
    positionIntegrationKernelMetal

/-- Generate constraint solver shader file -/
def generateConstraintShader : String :=
  "// Auto-generated Metal constraint solver shaders
// Generated from Lean specifications

#include <metal_stdlib>
using namespace metal;

// PGA3 Multivector struct
struct Multivector_PGA3 {
    float coeffs[16];
};

" ++ ballJointStructMetal ++ "\n" ++
    ballJointResidualKernelMetal ++ "\n" ++
    motorGradientKernelMetal ++ "\n" ++
    motorUpdateKernelMetal ++ "\n" ++
    constraintSolverKernelMetal

-- Output physics shader
#eval IO.println generatePhysicsShader

-- Output constraint solver shader
#eval IO.println generateConstraintShader

end Grassmann.Metal
