#!/usr/bin/env swift
// Swift runner for R3 Grassmann algebra GPU operations
// Generated from Lean specifications

import Metal
import Foundation

// Must match Metal struct layout
struct Multivector_R3 {
    var coeffs: (Float, Float, Float, Float, Float, Float, Float, Float)

    static var zero: Multivector_R3 {
        Multivector_R3(coeffs: (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0))
    }

    // Create basis vector e_i (i is 0-indexed)
    static func basis(_ i: Int) -> Multivector_R3 {
        var m = zero
        withUnsafeMutablePointer(to: &m.coeffs) { ptr in
            let arr = UnsafeMutableRawPointer(ptr).assumingMemoryBound(to: Float.self)
            arr[1 << i] = 1.0
        }
        return m
    }

    subscript(i: Int) -> Float {
        get {
            withUnsafePointer(to: coeffs) { ptr in
                UnsafeRawPointer(ptr).assumingMemoryBound(to: Float.self)[i]
            }
        }
        set {
            withUnsafeMutablePointer(to: &coeffs) { ptr in
                UnsafeMutableRawPointer(ptr).assumingMemoryBound(to: Float.self)[i] = newValue
            }
        }
    }
}

class GrassmannGPU_R3 {
    let device: MTLDevice
    let commandQueue: MTLCommandQueue
    let geometricProductPipeline: MTLComputePipelineState
    let sandwichProductPipeline: MTLComputePipelineState

    init(shaderPath: String) throws {
        guard let device = MTLCreateSystemDefaultDevice() else {
            throw NSError(domain: "Metal", code: 1, userInfo: [NSLocalizedDescriptionKey: "Metal not supported"])
        }
        self.device = device

        guard let commandQueue = device.makeCommandQueue() else {
            throw NSError(domain: "Metal", code: 2, userInfo: [NSLocalizedDescriptionKey: "Failed to create command queue"])
        }
        self.commandQueue = commandQueue

        let shaderSource = try String(contentsOfFile: shaderPath, encoding: .utf8)
        let library = try device.makeLibrary(source: shaderSource, options: nil)

        guard let geoFunc = library.makeFunction(name: "geometricProduct_R3"),
              let sandFunc = library.makeFunction(name: "sandwichProduct_R3") else {
            throw NSError(domain: "Metal", code: 3, userInfo: [NSLocalizedDescriptionKey: "Failed to find kernel functions"])
        }

        self.geometricProductPipeline = try device.makeComputePipelineState(function: geoFunc)
        self.sandwichProductPipeline = try device.makeComputePipelineState(function: sandFunc)
    }

    /// Batch geometric product: result[i] = a[i] * b[i]
    func geometricProduct(_ a: [Multivector_R3], _ b: [Multivector_R3]) -> [Multivector_R3] {
        precondition(a.count == b.count)
        let count = a.count
        let size = MemoryLayout<Multivector_R3>.size

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

        let resultPtr = resultBuffer.contents().bindMemory(to: Multivector_R3.self, capacity: count)
        return Array(UnsafeBufferPointer(start: resultPtr, count: count))
    }

    /// Batch sandwich product: result[i] = a[i] * x[i] * reverse(a[i])
    func sandwichProduct(_ a: [Multivector_R3], _ x: [Multivector_R3]) -> [Multivector_R3] {
        precondition(a.count == x.count)
        let count = a.count
        let size = MemoryLayout<Multivector_R3>.size

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

        let resultPtr = resultBuffer.contents().bindMemory(to: Multivector_R3.self, capacity: count)
        return Array(UnsafeBufferPointer(start: resultPtr, count: count))
    }
}

// Example usage
func main() throws {
    let gpu = try GrassmannGPU_R3(shaderPath: "./r3_grassmann.metal")

    // Create some test vectors
    let e1 = Multivector_R3.basis(0)
    let e2 = Multivector_R3.basis(1)

    // Batch test: e1 * e1 should give scalar 1
    let results = gpu.geometricProduct([e1, e2], [e1, e2])
    print("e1*e1 scalar part: \(results[0][0])")  // Should be 1.0
    print("e2*e2 scalar part: \(results[1][0])")  // Should be 1.0

    // Benchmark with many operations
    let count = 100_000
    let rotors = (0..<count).map { _ in e1 }  // Simplified
    let vectors = (0..<count).map { _ in e2 }

    let start = Date()
    let _ = gpu.sandwichProduct(rotors, vectors)
    let elapsed = Date().timeIntervalSince(start)
    print("\(count) sandwich products in \(elapsed * 1000)ms (\(Double(count)/elapsed/1_000_000) M/s)")
}

try main()
