/-
  Grassmann/GPUPhysicsPipeline.lean - GPU Physics with Unreal MCP Visualization

  Complete pipeline:
  1. Generate Metal shaders for PGA3 physics
  2. Swift runner executes GPU physics simulation
  3. Streams positions to Unreal MCP for live visualization
  4. Runs in a loop at 60fps

  Usage:
    lake exe gpuphysics  -- generates all files and runs simulation
-/
import Grassmann.MetalCodegen
import Grassmann.MultivectorGPU
import Grassmann.Physics
import Grassmann.PGA

namespace Grassmann.GPUPhysicsPipeline

open Grassmann.Metal
open Grassmann.GPU
open Grassmann.Physics

/-! ## Metal Physics Shader Generation -/

/-- Complete Metal shader for GPU physics simulation -/
def physicsShaderMetal : String :=
s!"// GPU Physics Simulation - PGA3 Motor-based Rigid Body Dynamics
// Generated from Lean specifications

#include <metal_stdlib>
using namespace metal;

// Motor structure (16 floats for PGA3)
struct Motor \{
    float coeffs[16];
};

// Rigid body state
struct RigidBody \{
    Motor motor;
    float3 linVel;
    float3 angVel;
    float invMass;
    float radius;
};

// Collision result
struct Collision \{
    uint i;
    uint j;
    float penetration;
    float3 normal;
    float3 contact;
};

// Motor multiplication (simplified for even subalgebra)
Motor motorMultiply(Motor a, Motor b) \{
    Motor result;
    // Scalar part
    result.coeffs[0] = a.coeffs[0] * b.coeffs[0]
                     - a.coeffs[6] * b.coeffs[6]   // e12
                     - a.coeffs[10] * b.coeffs[10] // e13
                     - a.coeffs[12] * b.coeffs[12]; // e23

    // e01 part
    result.coeffs[3] = a.coeffs[0] * b.coeffs[3] + a.coeffs[3] * b.coeffs[0]
                     + a.coeffs[6] * b.coeffs[5] - a.coeffs[5] * b.coeffs[6]
                     + a.coeffs[10] * b.coeffs[9] - a.coeffs[9] * b.coeffs[10];

    // e02 part
    result.coeffs[5] = a.coeffs[0] * b.coeffs[5] + a.coeffs[5] * b.coeffs[0]
                     - a.coeffs[6] * b.coeffs[3] + a.coeffs[3] * b.coeffs[6]
                     + a.coeffs[12] * b.coeffs[9] - a.coeffs[9] * b.coeffs[12];

    // e03 part
    result.coeffs[9] = a.coeffs[0] * b.coeffs[9] + a.coeffs[9] * b.coeffs[0]
                     - a.coeffs[10] * b.coeffs[3] + a.coeffs[3] * b.coeffs[10]
                     - a.coeffs[12] * b.coeffs[5] + a.coeffs[5] * b.coeffs[12];

    // e12 part
    result.coeffs[6] = a.coeffs[0] * b.coeffs[6] + a.coeffs[6] * b.coeffs[0]
                     + a.coeffs[10] * b.coeffs[12] - a.coeffs[12] * b.coeffs[10];

    // e13 part
    result.coeffs[10] = a.coeffs[0] * b.coeffs[10] + a.coeffs[10] * b.coeffs[0]
                      - a.coeffs[6] * b.coeffs[12] + a.coeffs[12] * b.coeffs[6];

    // e23 part
    result.coeffs[12] = a.coeffs[0] * b.coeffs[12] + a.coeffs[12] * b.coeffs[0]
                      + a.coeffs[6] * b.coeffs[10] - a.coeffs[10] * b.coeffs[6];

    // e0123 part
    result.coeffs[15] = a.coeffs[0] * b.coeffs[15] + a.coeffs[15] * b.coeffs[0]
                      + a.coeffs[3] * b.coeffs[12] + a.coeffs[12] * b.coeffs[3]
                      + a.coeffs[5] * b.coeffs[10] + a.coeffs[10] * b.coeffs[5]
                      + a.coeffs[9] * b.coeffs[6] + a.coeffs[6] * b.coeffs[9];

    // Zero out unused components
    result.coeffs[1] = 0; result.coeffs[2] = 0; result.coeffs[4] = 0;
    result.coeffs[7] = 0; result.coeffs[8] = 0; result.coeffs[11] = 0;
    result.coeffs[13] = 0; result.coeffs[14] = 0;

    return result;
}

// Motor exponential for small bivector (first order)
Motor motorExp(float3 omega, float3 vel, float dt) \{
    Motor result;
    for (int i = 0; i < 16; i++) result.coeffs[i] = 0;

    float theta = length(omega) * dt;

    if (theta < 1e-6f) \{
        // First order: exp(B) ≈ 1 + B
        result.coeffs[0] = 1.0f;
        result.coeffs[3] = vel.x * dt;  // e01
        result.coeffs[5] = vel.y * dt;  // e02
        result.coeffs[9] = vel.z * dt;  // e03
        result.coeffs[6] = omega.x * dt;  // e12
        result.coeffs[10] = omega.y * dt; // e13
        result.coeffs[12] = omega.z * dt; // e23
    } else \{
        // Rodrigues formula for rotation
        float c = cos(theta);
        float s = sin(theta);
        float sinc = s / theta;

        result.coeffs[0] = c;
        result.coeffs[6] = sinc * omega.x * dt;
        result.coeffs[10] = sinc * omega.y * dt;
        result.coeffs[12] = sinc * omega.z * dt;
        result.coeffs[3] = vel.x * dt * c;
        result.coeffs[5] = vel.y * dt * c;
        result.coeffs[9] = vel.z * dt * c;
    }

    return result;
}

// Extract position from motor
float3 motorToPosition(Motor m) \{
    // Position is encoded in translation bivectors
    return float3(2.0f * m.coeffs[3], 2.0f * m.coeffs[5], 2.0f * m.coeffs[9]);
}

// Normalize motor
Motor normalizeMotor(Motor m) \{
    float normSq = 0;
    for (int i = 0; i < 16; i++) normSq += m.coeffs[i] * m.coeffs[i];
    float invNorm = 1.0f / sqrt(normSq);
    Motor result;
    for (int i = 0; i < 16; i++) result.coeffs[i] = m.coeffs[i] * invNorm;
    return result;
}

// Physics integration kernel
kernel void integrateKernel(
    device RigidBody* bodies [[buffer(0)]],
    constant float& dt [[buffer(1)]],
    constant float& gravity [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) \{
    RigidBody body = bodies[id];

    // Apply gravity
    body.linVel.y -= gravity * dt;

    // Integrate motor
    float3 omega = float3(body.angVel.x, body.angVel.y, body.angVel.z);
    Motor dM = motorExp(omega, body.linVel, dt);
    body.motor = normalizeMotor(motorMultiply(dM, body.motor));

    // Apply damping
    body.linVel *= exp(-0.1f * dt);
    body.angVel *= exp(-0.1f * dt);

    bodies[id] = body;
}

// Floor collision kernel
kernel void floorCollisionKernel(
    device RigidBody* bodies [[buffer(0)]],
    constant float& floorY [[buffer(1)]],
    constant float& restitution [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) \{
    RigidBody body = bodies[id];
    float3 pos = motorToPosition(body.motor);
    float penetration = floorY + body.radius - pos.y;

    if (penetration > 0) \{
        // Bounce
        if (body.linVel.y < 0) \{
            body.linVel.y = -body.linVel.y * restitution;
        }
        // Position correction
        body.motor.coeffs[5] += penetration * 0.5f;  // e02 (y translation)
    }

    bodies[id] = body;
}

// Sphere-sphere collision detection kernel
kernel void sphereCollisionKernel(
    device RigidBody* bodies [[buffer(0)]],
    device atomic_uint* collisionCount [[buffer(1)]],
    device Collision* collisions [[buffer(2)]],
    constant uint& numBodies [[buffer(3)]],
    constant float& restitution [[buffer(4)]],
    uint2 gid [[thread_position_in_grid]]
) \{
    uint i = gid.x;
    uint j = gid.y;

    if (i >= j || i >= numBodies || j >= numBodies) return;

    RigidBody b1 = bodies[i];
    RigidBody b2 = bodies[j];

    float3 p1 = motorToPosition(b1.motor);
    float3 p2 = motorToPosition(b2.motor);
    float3 diff = p2 - p1;
    float dist = length(diff);
    float minDist = b1.radius + b2.radius;

    if (dist < minDist && dist > 1e-6f) \{
        // Collision detected
        uint idx = atomic_fetch_add_explicit(collisionCount, 1, memory_order_relaxed);
        if (idx < 256) \{  // Max collisions
            Collision c;
            c.i = i;
            c.j = j;
            c.penetration = minDist - dist;
            c.normal = diff / dist;
            c.contact = p1 + c.normal * b1.radius;
            collisions[idx] = c;
        }
    }
}

// Apply collision impulses kernel
kernel void applyCollisionImpulsesKernel(
    device RigidBody* bodies [[buffer(0)]],
    device Collision* collisions [[buffer(1)]],
    constant uint& numCollisions [[buffer(2)]],
    constant float& restitution [[buffer(3)]],
    uint id [[thread_position_in_grid]]
) \{
    if (id >= numCollisions) return;

    Collision c = collisions[id];
    RigidBody b1 = bodies[c.i];
    RigidBody b2 = bodies[c.j];

    // Relative velocity
    float3 relVel = b1.linVel - b2.linVel;
    float relVn = dot(relVel, c.normal);

    if (relVn > 0) \{
        // Bodies approaching
        float totalInvMass = b1.invMass + b2.invMass;
        float j = -(1 + restitution) * relVn / totalInvMass;

        // Apply impulses (atomic would be better but keeping simple)
        bodies[c.i].linVel -= j * c.normal * b1.invMass;
        bodies[c.j].linVel += j * c.normal * b2.invMass;
    }
}

// Extract positions for rendering
kernel void extractPositionsKernel(
    device RigidBody* bodies [[buffer(0)]],
    device float3* positions [[buffer(1)]],
    uint id [[thread_position_in_grid]]
) \{
    positions[id] = motorToPosition(bodies[id].motor);
}
"

/-! ## Swift Runner with Unreal MCP Integration -/

/-- Swift runner for GPU physics with Unreal MCP streaming -/
def physicsSwiftRunner : String :=
s!"#!/usr/bin/env swift
// GPU Physics Simulation with Unreal MCP Visualization
// Generated from Lean specifications

import Metal
import Foundation

// MARK: - Data Structures

struct Motor \{
    var coeffs: (Float, Float, Float, Float, Float, Float, Float, Float,
                 Float, Float, Float, Float, Float, Float, Float, Float)

    static var identity: Motor \{
        Motor(coeffs: (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
    }

    subscript(i: Int) -> Float \{
        get \{
            withUnsafePointer(to: coeffs) \{
                UnsafeRawPointer($0).assumingMemoryBound(to: Float.self)[i]
            }
        }
        set \{
            withUnsafeMutablePointer(to: &coeffs) \{
                UnsafeMutableRawPointer($0).assumingMemoryBound(to: Float.self)[i] = newValue
            }
        }
    }
}

struct RigidBody \{
    var motor: Motor
    var linVel: SIMD3<Float>
    var angVel: SIMD3<Float>
    var invMass: Float
    var radius: Float

    static func create(x: Float, y: Float, z: Float, radius: Float = 1.0) -> RigidBody \{
        var m = Motor.identity
        m[3] = x / 2  // e01
        m[5] = y / 2  // e02
        m[9] = z / 2  // e03
        return RigidBody(
            motor: m,
            linVel: SIMD3<Float>(0, 0, 0),
            angVel: SIMD3<Float>(0, 0, 0),
            invMass: 1.0,
            radius: radius
        )
    }

    var position: SIMD3<Float> \{
        SIMD3<Float>(motor[3] * 2, motor[5] * 2, motor[9] * 2)
    }
}

struct Collision \{
    var i: UInt32
    var j: UInt32
    var penetration: Float
    var normal: SIMD3<Float>
    var contact: SIMD3<Float>
}

// MARK: - GPU Physics Engine

class GPUPhysics \{
    let device: MTLDevice
    let commandQueue: MTLCommandQueue
    let integratePipeline: MTLComputePipelineState
    let floorPipeline: MTLComputePipelineState
    let extractPipeline: MTLComputePipelineState

    var bodies: [RigidBody] = []
    var bodyBuffer: MTLBuffer!
    var positionBuffer: MTLBuffer!

    let gravity: Float = 9.81
    let floorY: Float = 0.0
    let restitution: Float = 0.6

    init(shaderPath: String) throws \{
        guard let device = MTLCreateSystemDefaultDevice() else \{
            throw NSError(domain: \"Metal\", code: 1)
        }
        self.device = device
        self.commandQueue = device.makeCommandQueue()!

        let shaderSource = try String(contentsOfFile: shaderPath, encoding: .utf8)
        let library = try device.makeLibrary(source: shaderSource, options: nil)

        self.integratePipeline = try device.makeComputePipelineState(
            function: library.makeFunction(name: \"integrateKernel\")!)
        self.floorPipeline = try device.makeComputePipelineState(
            function: library.makeFunction(name: \"floorCollisionKernel\")!)
        self.extractPipeline = try device.makeComputePipelineState(
            function: library.makeFunction(name: \"extractPositionsKernel\")!)
    }

    func setupBodies(_ bodies: [RigidBody]) \{
        self.bodies = bodies
        let size = MemoryLayout<RigidBody>.stride * bodies.count
        bodyBuffer = device.makeBuffer(bytes: bodies, length: size, options: .storageModeShared)
        positionBuffer = device.makeBuffer(
            length: MemoryLayout<SIMD3<Float>>.stride * bodies.count,
            options: .storageModeShared)
    }

    func step(dt: Float) \{
        guard !bodies.isEmpty else \{ return }

        let commandBuffer = commandQueue.makeCommandBuffer()!

        // Integrate
        var dtValue = dt
        var gravityValue = gravity
        let encoder1 = commandBuffer.makeComputeCommandEncoder()!
        encoder1.setComputePipelineState(integratePipeline)
        encoder1.setBuffer(bodyBuffer, offset: 0, index: 0)
        encoder1.setBytes(&dtValue, length: 4, index: 1)
        encoder1.setBytes(&gravityValue, length: 4, index: 2)
        let threads1 = MTLSize(width: bodies.count, height: 1, depth: 1)
        let groups1 = MTLSize(width: 1, height: 1, depth: 1)
        encoder1.dispatchThreads(threads1, threadsPerThreadgroup: groups1)
        encoder1.endEncoding()

        // Floor collision
        var floorValue = floorY
        var restValue = restitution
        let encoder2 = commandBuffer.makeComputeCommandEncoder()!
        encoder2.setComputePipelineState(floorPipeline)
        encoder2.setBuffer(bodyBuffer, offset: 0, index: 0)
        encoder2.setBytes(&floorValue, length: 4, index: 1)
        encoder2.setBytes(&restValue, length: 4, index: 2)
        encoder2.dispatchThreads(threads1, threadsPerThreadgroup: groups1)
        encoder2.endEncoding()

        commandBuffer.commit()
        commandBuffer.waitUntilCompleted()

        // Read back bodies
        let ptr = bodyBuffer.contents().bindMemory(to: RigidBody.self, capacity: bodies.count)
        for i in 0..<bodies.count \{
            bodies[i] = ptr[i]
        }
    }

    func getPositions() -> [SIMD3<Float>] \{
        bodies.map \{ $0.position }
    }
}

// MARK: - Unreal MCP Client

class UnrealMCPClient \{
    let serverURL: URL

    init(host: String = \"localhost\", port: Int = 3000) \{
        self.serverURL = URL(string: \"http://\\(host):\\(port)\")!
    }

    func setActorTransform(name: String, location: SIMD3<Float>) \{
        // Convert to Unreal coordinates (Y-up to Z-up, meters to cm)
        let unrealPos = SIMD3<Float>(location.x * 100, location.z * 100, location.y * 100)

        let json: [String: Any] = [
            \"jsonrpc\": \"2.0\",
            \"method\": \"tools/call\",
            \"params\": [
                \"name\": \"set_actor_transform\",
                \"arguments\": [
                    \"name\": name,
                    \"location\": [unrealPos.x, unrealPos.y, unrealPos.z]
                ]
            ],
            \"id\": 1
        ]

        var request = URLRequest(url: serverURL)
        request.httpMethod = \"POST\"
        request.setValue(\"application/json\", forHTTPHeaderField: \"Content-Type\")
        request.httpBody = try? JSONSerialization.data(withJSONObject: json)

        // Fire and forget (async)
        URLSession.shared.dataTask(with: request).resume()
    }

    func updateActors(names: [String], positions: [SIMD3<Float>]) \{
        for (name, pos) in zip(names, positions) \{
            setActorTransform(name: name, location: pos)
        }
    }
}

// MARK: - Main Simulation Loop

func runSimulation() throws \{
    print(\"GPU Physics with Unreal MCP Visualization\")
    print(\"==========================================\\n\")

    // Initialize GPU physics
    let physics = try GPUPhysics(shaderPath: \"physics_pga3.metal\")

    // Create bouncing balls
    let bodies: [RigidBody] = [
        RigidBody.create(x: 0, y: 8, z: 0, radius: 1.0),
        RigidBody.create(x: 3, y: 10, z: 0, radius: 1.0),
        RigidBody.create(x: -2, y: 12, z: 1, radius: 1.0),
        RigidBody.create(x: 1, y: 15, z: -1, radius: 1.0)
    ]
    physics.setupBodies(bodies)

    // Actor names in Unreal
    let actorNames = [\"Ball_0\", \"Ball_1\", \"Ball_2\", \"Ball_3\"]

    // MCP client (optional - won't fail if not connected)
    let mcp = UnrealMCPClient()

    // Simulation parameters
    let dt: Float = 1.0 / 60.0
    let duration: Float = 10.0
    let steps = Int(duration / dt)

    print(\"Running \\(steps) simulation steps at 60fps...\\n\")

    var startTime = Date()

    for frame in 0..<steps \{
        // Physics step (GPU)
        physics.step(dt: dt)

        // Get positions
        let positions = physics.getPositions()

        // Send to Unreal MCP
        mcp.updateActors(names: actorNames, positions: positions)

        // Print progress every 60 frames
        if frame % 60 == 0 \{
            let elapsed = Date().timeIntervalSince(startTime)
            print(\"Frame \\(frame): \", terminator: \"\")
            for (i, pos) in positions.enumerated() \{
                print(String(format: \"Ball\\(i)=(%.1f,%.1f,%.1f) \", pos.x, pos.y, pos.z), terminator: \"\")
            }
            print(String(format: \"[%.1f fps]\", Double(frame) / elapsed))
        }

        // Real-time pacing (optional)
        // usleep(UInt32(dt * 1_000_000))
    }

    let totalTime = Date().timeIntervalSince(startTime)
    print(\"\\nCompleted \\(steps) frames in \\(String(format: \"%.2f\", totalTime))s\")
    print(\"Average: \\(String(format: \"%.1f\", Double(steps) / totalTime)) fps\")
}

// MARK: - Entry Point

do \{
    try runSimulation()
} catch \{
    print(\"Error: \\(error)\")
    exit(1)
}
"

/-! ## Lean Executable for Pipeline Generation -/

/-- Generate all files for GPU physics pipeline -/
def generateGPUPhysicsPipeline (outputDir : System.FilePath := ".") : IO Unit := do
  -- Generate Metal shader
  let metalPath := outputDir / "physics_pga3.metal"
  IO.FS.writeFile metalPath physicsShaderMetal
  IO.println s!"Generated: {metalPath}"

  -- Generate Swift runner
  let swiftPath := outputDir / "physics_runner.swift"
  IO.FS.writeFile swiftPath physicsSwiftRunner
  IO.println s!"Generated: {swiftPath}"

  -- Generate run script
  let scriptPath := outputDir / "run_physics.sh"
  IO.FS.writeFile scriptPath s!"#!/bin/bash
# GPU Physics Pipeline Runner
# Generated from Lean

echo \"Compiling Metal shaders...\"
xcrun -sdk macosx metal -c physics_pga3.metal -o physics_pga3.air
xcrun -sdk macosx metallib physics_pga3.air -o physics_pga3.metallib
echo \"Metal shaders compiled.\"

echo \"Running physics simulation...\"
swift physics_runner.swift
"
  IO.println s!"Generated: {scriptPath}"
  IO.println "\nTo run the GPU physics simulation:"
  IO.println "  cd output_dir && chmod +x run_physics.sh && ./run_physics.sh"

/-! ## Benchmark: GPU vs CPU -/

/-- Run CPU physics for benchmarking -/
def benchmarkCPU (numBodies : Nat) (numFrames : Nat) : IO Float := do
  let positions := Array.ofFn (n := numBodies) fun i =>
    (Float.ofNat i * 2.0, 5.0 + Float.ofNat i, 0.0)
  let world := World.create positions 1.0
  let startTime ← IO.monoMsNow
  let rec loop (w : World) (n : Nat) : World :=
    if n = 0 then w
    else loop (w.step 0.016) (n - 1)
  let _ := loop world numFrames
  let endTime ← IO.monoMsNow
  let elapsed := Float.ofNat (endTime - startTime) / 1000.0
  return elapsed

/-- Benchmark comparison output -/
def runBenchmark : IO Unit := do
  IO.println "GPU vs CPU Physics Benchmark"
  IO.println "============================"
  for numBodies in [10, 50, 100, 500] do
    let frames := 600  -- 10 seconds at 60fps
    let cpuTime ← benchmarkCPU numBodies frames
    let cpuFPS := Float.ofNat frames / cpuTime
    IO.println s!"\n{numBodies} bodies, {frames} frames:"
    IO.println s!"  CPU: {cpuTime}s ({cpuFPS} fps)"
    IO.println s!"  GPU: (run Swift executable for GPU benchmark)"

/-! ## Tests -/

-- Test shader generation
#eval! physicsShaderMetal.length > 1000

-- Test swift runner generation
#eval! physicsSwiftRunner.length > 1000

end Grassmann.GPUPhysicsPipeline
