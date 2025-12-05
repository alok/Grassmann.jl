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

end Grassmann.Metal
