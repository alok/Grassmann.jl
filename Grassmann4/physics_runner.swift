#!/usr/bin/env swift
// GPU Physics Simulation with Unreal MCP Visualization
// Generated from Lean specifications

import Metal
import Foundation

// MARK: - Data Structures

struct Motor {
    var coeffs: (Float, Float, Float, Float, Float, Float, Float, Float,
                 Float, Float, Float, Float, Float, Float, Float, Float)

    static var identity: Motor {
        Motor(coeffs: (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
    }

    subscript(i: Int) -> Float {
        get {
            withUnsafePointer(to: coeffs) {
                UnsafeRawPointer($0).assumingMemoryBound(to: Float.self)[i]
            }
        }
        set {
            withUnsafeMutablePointer(to: &coeffs) {
                UnsafeMutableRawPointer($0).assumingMemoryBound(to: Float.self)[i] = newValue
            }
        }
    }
}

struct RigidBody {
    var motor: Motor
    var linVel: SIMD3<Float>
    var angVel: SIMD3<Float>
    var invMass: Float
    var radius: Float

    static func create(x: Float, y: Float, z: Float, radius: Float = 1.0) -> RigidBody {
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

    var position: SIMD3<Float> {
        SIMD3<Float>(motor[3] * 2, motor[5] * 2, motor[9] * 2)
    }
}

struct Collision {
    var i: UInt32
    var j: UInt32
    var penetration: Float
    var normal: SIMD3<Float>
    var contact: SIMD3<Float>
}

// MARK: - GPU Physics Engine

class GPUPhysics {
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

    init(shaderPath: String) throws {
        guard let device = MTLCreateSystemDefaultDevice() else {
            throw NSError(domain: "Metal", code: 1)
        }
        self.device = device
        self.commandQueue = device.makeCommandQueue()!

        let shaderSource = try String(contentsOfFile: shaderPath, encoding: .utf8)
        let library = try device.makeLibrary(source: shaderSource, options: nil)

        self.integratePipeline = try device.makeComputePipelineState(
            function: library.makeFunction(name: "integrateKernel")!)
        self.floorPipeline = try device.makeComputePipelineState(
            function: library.makeFunction(name: "floorCollisionKernel")!)
        self.extractPipeline = try device.makeComputePipelineState(
            function: library.makeFunction(name: "extractPositionsKernel")!)
    }

    func setupBodies(_ bodies: [RigidBody]) {
        self.bodies = bodies
        let size = MemoryLayout<RigidBody>.stride * bodies.count
        bodyBuffer = device.makeBuffer(bytes: bodies, length: size, options: .storageModeShared)
        positionBuffer = device.makeBuffer(
            length: MemoryLayout<SIMD3<Float>>.stride * bodies.count,
            options: .storageModeShared)
    }

    func step(dt: Float) {
        guard !bodies.isEmpty else { return }

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
        for i in 0..<bodies.count {
            bodies[i] = ptr[i]
        }
    }

    func getPositions() -> [SIMD3<Float>] {
        bodies.map { $0.position }
    }
}

// MARK: - Unreal MCP Client

class UnrealMCPClient {
    let serverURL: URL

    init(host: String = "localhost", port: Int = 3000) {
        self.serverURL = URL(string: "http://\(host):\(port)")!
    }

    func setActorTransform(name: String, location: SIMD3<Float>) {
        // Convert to Unreal coordinates (Y-up to Z-up, meters to cm)
        let unrealPos = SIMD3<Float>(location.x * 100, location.z * 100, location.y * 100)

        let json: [String: Any] = [
            "jsonrpc": "2.0",
            "method": "tools/call",
            "params": [
                "name": "set_actor_transform",
                "arguments": [
                    "name": name,
                    "location": [unrealPos.x, unrealPos.y, unrealPos.z]
                ]
            ],
            "id": 1
        ]

        var request = URLRequest(url: serverURL)
        request.httpMethod = "POST"
        request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        request.httpBody = try? JSONSerialization.data(withJSONObject: json)

        // Fire and forget (async)
        URLSession.shared.dataTask(with: request).resume()
    }

    func updateActors(names: [String], positions: [SIMD3<Float>]) {
        for (name, pos) in zip(names, positions) {
            setActorTransform(name: name, location: pos)
        }
    }
}

// MARK: - Main Simulation Loop

func runSimulation() throws {
    print("GPU Physics with Unreal MCP Visualization")
    print("==========================================\n")

    // Initialize GPU physics
    let physics = try GPUPhysics(shaderPath: "physics_pga3.metal")

    // Create bouncing balls
    let bodies: [RigidBody] = [
        RigidBody.create(x: 0, y: 8, z: 0, radius: 1.0),
        RigidBody.create(x: 3, y: 10, z: 0, radius: 1.0),
        RigidBody.create(x: -2, y: 12, z: 1, radius: 1.0),
        RigidBody.create(x: 1, y: 15, z: -1, radius: 1.0)
    ]
    physics.setupBodies(bodies)

    // Actor names in Unreal
    let actorNames = ["Ball_0", "Ball_1", "Ball_2", "Ball_3"]

    // MCP client (optional - won't fail if not connected)
    let mcp = UnrealMCPClient()

    // Simulation parameters
    let dt: Float = 1.0 / 60.0
    let duration: Float = 10.0
    let steps = Int(duration / dt)

    print("Running \(steps) simulation steps at 60fps...\n")

    var startTime = Date()

    for frame in 0..<steps {
        // Physics step (GPU)
        physics.step(dt: dt)

        // Get positions
        let positions = physics.getPositions()

        // Send to Unreal MCP
        mcp.updateActors(names: actorNames, positions: positions)

        // Print progress every 60 frames
        if frame % 60 == 0 {
            let elapsed = Date().timeIntervalSince(startTime)
            print("Frame \(frame): ", terminator: "")
            for (i, pos) in positions.enumerated() {
                print(String(format: "Ball\(i)=(%.1f,%.1f,%.1f) ", pos.x, pos.y, pos.z), terminator: "")
            }
            print(String(format: "[%.1f fps]", Double(frame) / elapsed))
        }

        // Real-time pacing (optional)
        // usleep(UInt32(dt * 1_000_000))
    }

    let totalTime = Date().timeIntervalSince(startTime)
    print("\nCompleted \(steps) frames in \(String(format: "%.2f", totalTime))s")
    print("Average: \(String(format: "%.1f", Double(steps) / totalTime)) fps")
}

// MARK: - Entry Point

do {
    try runSimulation()
} catch {
    print("Error: \(error)")
    exit(1)
}
