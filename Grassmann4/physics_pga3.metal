// GPU Physics Simulation - PGA3 Motor-based Rigid Body Dynamics
// Generated from Lean specifications

#include <metal_stdlib>
using namespace metal;

// Motor structure (16 floats for PGA3)
struct Motor {
    float coeffs[16];
};

// Rigid body state
struct RigidBody {
    Motor motor;
    float3 linVel;
    float3 angVel;
    float invMass;
    float radius;
};

// Collision result
struct Collision {
    uint i;
    uint j;
    float penetration;
    float3 normal;
    float3 contact;
};

// Motor multiplication (simplified for even subalgebra)
Motor motorMultiply(Motor a, Motor b) {
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
Motor motorExp(float3 omega, float3 vel, float dt) {
    Motor result;
    for (int i = 0; i < 16; i++) result.coeffs[i] = 0;

    float theta = length(omega) * dt;

    if (theta < 1e-6f) {
        // First order: exp(B) ≈ 1 + B
        result.coeffs[0] = 1.0f;
        result.coeffs[3] = vel.x * dt;  // e01
        result.coeffs[5] = vel.y * dt;  // e02
        result.coeffs[9] = vel.z * dt;  // e03
        result.coeffs[6] = omega.x * dt;  // e12
        result.coeffs[10] = omega.y * dt; // e13
        result.coeffs[12] = omega.z * dt; // e23
    } else {
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
float3 motorToPosition(Motor m) {
    // Position is encoded in translation bivectors
    return float3(2.0f * m.coeffs[3], 2.0f * m.coeffs[5], 2.0f * m.coeffs[9]);
}

// Normalize motor
Motor normalizeMotor(Motor m) {
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
) {
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
) {
    RigidBody body = bodies[id];
    float3 pos = motorToPosition(body.motor);
    float penetration = floorY + body.radius - pos.y;

    if (penetration > 0) {
        // Bounce
        if (body.linVel.y < 0) {
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
) {
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

    if (dist < minDist && dist > 1e-6f) {
        // Collision detected
        uint idx = atomic_fetch_add_explicit(collisionCount, 1, memory_order_relaxed);
        if (idx < 256) {  // Max collisions
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
) {
    if (id >= numCollisions) return;

    Collision c = collisions[id];
    RigidBody b1 = bodies[c.i];
    RigidBody b2 = bodies[c.j];

    // Relative velocity
    float3 relVel = b1.linVel - b2.linVel;
    float relVn = dot(relVel, c.normal);

    if (relVn > 0) {
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
) {
    positions[id] = motorToPosition(bodies[id].motor);
}
