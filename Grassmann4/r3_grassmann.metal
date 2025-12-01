// Auto-generated Metal shader for Grassmann algebra
// Signature: R3 (3D)
// Generated from Lean specifications

#include <metal_stdlib>
using namespace metal;

// Precomputed sign table for geometric product
constant int signs_R3[8][8] = {
    { 1,  1,  1,  1,  1,  1,  1,  1},
    { 1,  1,  1,  1,  1,  1,  1,  1},
    { 1, -1,  1, -1,  1, -1,  1, -1},
    { 1, -1,  1, -1,  1, -1,  1, -1},
    { 1, -1, -1,  1,  1, -1, -1,  1},
    { 1, -1, -1,  1,  1, -1, -1,  1},
    { 1,  1, -1, -1,  1,  1, -1, -1},
    { 1,  1, -1, -1,  1,  1, -1, -1}
};

// Output index table: i XOR j
constant uint outputIdx[8][8] = {
    {0, 1, 2, 3, 4, 5, 6, 7},
    {1, 0, 3, 2, 5, 4, 7, 6},
    {2, 3, 0, 1, 6, 7, 4, 5},
    {3, 2, 1, 0, 7, 6, 5, 4},
    {4, 5, 6, 7, 0, 1, 2, 3},
    {5, 4, 7, 6, 1, 0, 3, 2},
    {6, 7, 4, 5, 2, 3, 0, 1},
    {7, 6, 5, 4, 3, 2, 1, 0}
};

// Reverse signs for dagger operation
constant int reverseSign_R3[8] = { 1,  1,  1, -1,  1, -1, -1, -1};

// Multivector for R3 (3D, 8 blades)
struct Multivector_R3 {
    float coeffs[8];
};

// Batch geometric product: result[gid] = a[gid] * b[gid]
kernel void geometricProduct_R3(
    device const Multivector_R3* a [[buffer(0)]],
    device const Multivector_R3* b [[buffer(1)]],
    device Multivector_R3* result [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    // Zero output
    Multivector_R3 out;
    for (uint k = 0; k < 8; k++) out.coeffs[k] = 0.0f;

    // Accumulate contributions from all pairs
    for (uint i = 0; i < 8; i++) {
        float ai = a[gid].coeffs[i];
        if (ai == 0.0f) continue;  // Skip zeros

        for (uint j = 0; j < 8; j++) {
            float bj = b[gid].coeffs[j];
            if (bj == 0.0f) continue;  // Skip zeros

            int sign = signs_R3[i][j];
            if (sign != 0) {
                uint k = outputIdx[i][j];
                out.coeffs[k] += float(sign) * ai * bj;
            }
        }
    }

    result[gid] = out;
}

// Sandwich product: result[gid] = a[gid] * x[gid] * reverse(a[gid])
// Used for rotations and reflections
kernel void sandwichProduct_R3(
    device const Multivector_R3* a [[buffer(0)]],
    device const Multivector_R3* x [[buffer(1)]],
    device Multivector_R3* result [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    // First compute temp = a * x
    Multivector_R3 temp;
    for (uint k = 0; k < 8; k++) temp.coeffs[k] = 0.0f;

    for (uint i = 0; i < 8; i++) {
        float ai = a[gid].coeffs[i];
        if (ai == 0.0f) continue;
        for (uint j = 0; j < 8; j++) {
            float xj = x[gid].coeffs[j];
            if (xj == 0.0f) continue;
            int sign = signs_R3[i][j];
            if (sign != 0) {
                uint k = outputIdx[i][j];
                temp.coeffs[k] += float(sign) * ai * xj;
            }
        }
    }

    // Now compute result = temp * reverse(a)
    Multivector_R3 out;
    for (uint k = 0; k < 8; k++) out.coeffs[k] = 0.0f;

    for (uint i = 0; i < 8; i++) {
        float ti = temp.coeffs[i];
        if (ti == 0.0f) continue;
        for (uint j = 0; j < 8; j++) {
            // Apply reverse sign to a[j]
            float aj = a[gid].coeffs[j] * reverseSign_R3[j];
            if (aj == 0.0f) continue;
            int sign = signs_R3[i][j];
            if (sign != 0) {
                uint k = outputIdx[i][j];
                out.coeffs[k] += float(sign) * ti * aj;
            }
        }
    }

    result[gid] = out;
}
