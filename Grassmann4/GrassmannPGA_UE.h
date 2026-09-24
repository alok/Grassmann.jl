/**
 * GrassmannPGA_UE.h - Pure C/C++ PGA3 operations for Unreal Engine
 *
 * Self-contained implementation (no Lean runtime dependency).
 * Generated from Lean 4 Grassmann library formulas.
 *
 * PGA3 Coefficient Layout (16 floats):
 *   [0]  scalar   [1]  e0      [2]  e1      [3]  e12
 *   [4]  e2       [5]  e31     [6]  e23     [7]  e123
 *   [8]  e3       [9]  e01     [10] e02     [11] e012
 *   [12] e03      [13] e031    [14] e023    [15] e0123
 */

#ifndef GRASSMANN_PGA_UE_H
#define GRASSMANN_PGA_UE_H

#include <math.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Indices for PGA3 basis elements */
#define PGA_SCALAR  0
#define PGA_E0      1
#define PGA_E1      2
#define PGA_E12     3
#define PGA_E2      4
#define PGA_E31     5
#define PGA_E23     6
#define PGA_E123    7
#define PGA_E3      8
#define PGA_E01     9
#define PGA_E02     10
#define PGA_E012    11
#define PGA_E03     12
#define PGA_E031    13
#define PGA_E023    14
#define PGA_E0123   15

#define PGA_DIM     16

/* ============================================================================
 * Point Operations
 * ============================================================================ */

/**
 * Create a PGA3 point from x,y,z coordinates.
 * Point = e123 + x*e023 + y*e031 + z*e012
 */
static inline void pga_point(float x, float y, float z, float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);
    out[PGA_E123] = 1.0f;  /* w = 1 (homogeneous) */
    out[PGA_E023] = x;
    out[PGA_E031] = y;
    out[PGA_E012] = z;
}

/**
 * Extract x,y,z from a PGA point.
 */
static inline void pga_extract_point(const float p[PGA_DIM], float* x, float* y, float* z) {
    float w = p[PGA_E123];
    if (fabsf(w) < 1e-10f) {
        *x = *y = *z = 0.0f;
        return;
    }
    *x = p[PGA_E023] / w;
    *y = p[PGA_E031] / w;
    *z = p[PGA_E012] / w;
}

/* ============================================================================
 * Motor Operations (Rotors + Translators)
 * ============================================================================ */

/**
 * Create a rotation motor (rotor) from axis and angle.
 * Rotor = cos(θ/2) + sin(θ/2)(dx*e23 + dy*e31 + dz*e12)
 */
static inline void pga_rotor(float dx, float dy, float dz, float theta, float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);
    float half = theta * 0.5f;
    float c = cosf(half);
    float s = sinf(half);
    out[PGA_SCALAR] = c;
    out[PGA_E23] = s * dx;
    out[PGA_E31] = s * dy;
    out[PGA_E12] = s * dz;
}

/**
 * Create a translation motor.
 * Translator = 1 + (tx/2)*e01 + (ty/2)*e02 + (tz/2)*e03
 */
static inline void pga_translator(float tx, float ty, float tz, float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);
    out[PGA_SCALAR] = 1.0f;
    out[PGA_E01] = tx * 0.5f;
    out[PGA_E02] = ty * 0.5f;
    out[PGA_E03] = tz * 0.5f;
}

/**
 * Compose two motors: M1 * M2.
 */
static inline void pga_motor_compose(const float m1[PGA_DIM], const float m2[PGA_DIM], float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);

    /* Extract rotor components */
    float s1 = m1[PGA_SCALAR], b12_1 = m1[PGA_E12], b31_1 = m1[PGA_E31], b23_1 = m1[PGA_E23];
    float s2 = m2[PGA_SCALAR], b12_2 = m2[PGA_E12], b31_2 = m2[PGA_E31], b23_2 = m2[PGA_E23];

    /* Rotor composition */
    out[PGA_SCALAR] = s1*s2 - (b12_1*b12_2 + b31_1*b31_2 + b23_1*b23_2);
    out[PGA_E12] = s1*b12_2 + s2*b12_1 + (b31_1*b23_2 - b23_1*b31_2);
    out[PGA_E31] = s1*b31_2 + s2*b31_1 + (b23_1*b12_2 - b12_1*b23_2);
    out[PGA_E23] = s1*b23_2 + s2*b23_1 + (b12_1*b31_2 - b31_1*b12_2);

    /* Translation part (simplified) */
    out[PGA_E01] = m1[PGA_E01] + m2[PGA_E01];
    out[PGA_E02] = m1[PGA_E02] + m2[PGA_E02];
    out[PGA_E03] = m1[PGA_E03] + m2[PGA_E03];
}

/**
 * Reverse (conjugate) of a motor: M†
 */
static inline void pga_motor_reverse(const float m[PGA_DIM], float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);
    out[PGA_SCALAR] = m[PGA_SCALAR];
    out[PGA_E12] = -m[PGA_E12];
    out[PGA_E31] = -m[PGA_E31];
    out[PGA_E23] = -m[PGA_E23];
    out[PGA_E01] = -m[PGA_E01];
    out[PGA_E02] = -m[PGA_E02];
    out[PGA_E03] = -m[PGA_E03];
    out[PGA_E0123] = m[PGA_E0123];
}

/**
 * Apply motor to point: M * P * M†
 * Uses Rodrigues rotation formula + translation.
 */
static inline void pga_motor_apply_point(const float motor[PGA_DIM], const float point[PGA_DIM], float out[PGA_DIM]) {
    /* Extract point coordinates */
    float x, y, z;
    pga_extract_point(point, &x, &y, &z);

    /* Extract rotor as quaternion: q = (qx, qy, qz, qw) */
    float qx = motor[PGA_E23];
    float qy = motor[PGA_E31];
    float qz = motor[PGA_E12];
    float qw = motor[PGA_SCALAR];

    /* Rodrigues rotation: v' = v + 2w(q × v) + 2(q × (q × v)) */
    /* Cross product q × v */
    float cx = qy*z - qz*y;
    float cy = qz*x - qx*z;
    float cz = qx*y - qy*x;

    /* Cross product q × (q × v) */
    float ccx = qy*cz - qz*cy;
    float ccy = qz*cx - qx*cz;
    float ccz = qx*cy - qy*cx;

    /* Final rotated position */
    float rx = x + 2.0f*qw*cx + 2.0f*ccx;
    float ry = y + 2.0f*qw*cy + 2.0f*ccy;
    float rz = z + 2.0f*qw*cz + 2.0f*ccz;

    /* Add translation */
    float tx = motor[PGA_E01] * 2.0f;
    float ty = motor[PGA_E02] * 2.0f;
    float tz = motor[PGA_E03] * 2.0f;

    pga_point(rx + tx, ry + ty, rz + tz, out);
}

/* ============================================================================
 * Unreal Engine Conversions
 * ============================================================================ */

/**
 * Convert PGA motor to quaternion (x,y,z,w) for FQuat.
 */
static inline void pga_motor_to_quat(const float motor[PGA_DIM], float* qx, float* qy, float* qz, float* qw) {
    float w = motor[PGA_SCALAR];
    float xy = motor[PGA_E12];
    float xz = motor[PGA_E31];
    float yz = motor[PGA_E23];

    float norm = sqrtf(w*w + xy*xy + xz*xz + yz*yz);
    if (norm < 1e-10f) {
        *qx = 0.0f; *qy = 0.0f; *qz = 0.0f; *qw = 1.0f;
        return;
    }

    *qx = yz / norm;
    *qy = xz / norm;
    *qz = xy / norm;
    *qw = w / norm;
}

/**
 * Extract translation (x,y,z) from PGA motor for FVector.
 */
static inline void pga_motor_to_translation(const float motor[PGA_DIM], float* tx, float* ty, float* tz) {
    *tx = motor[PGA_E01] * 2.0f;
    *ty = motor[PGA_E02] * 2.0f;
    *tz = motor[PGA_E03] * 2.0f;
}

/**
 * Create PGA motor from UE FQuat (x,y,z,w) and FVector (tx,ty,tz).
 */
static inline void pga_motor_from_ue(float qx, float qy, float qz, float qw,
                                      float tx, float ty, float tz,
                                      float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);
    out[PGA_SCALAR] = qw;
    out[PGA_E12] = qz;
    out[PGA_E31] = qy;
    out[PGA_E23] = qx;
    out[PGA_E01] = tx * 0.5f;
    out[PGA_E02] = ty * 0.5f;
    out[PGA_E03] = tz * 0.5f;
}

/* ============================================================================
 * Utility Operations
 * ============================================================================ */

/**
 * Euclidean distance squared between two points.
 */
static inline float pga_distance_sq(float x1, float y1, float z1, float x2, float y2, float z2) {
    float dx = x2 - x1;
    float dy = y2 - y1;
    float dz = z2 - z1;
    return dx*dx + dy*dy + dz*dz;
}

/**
 * Quaternion spherical linear interpolation (SLERP).
 */
static inline void quat_slerp(float q1x, float q1y, float q1z, float q1w,
                               float q2x, float q2y, float q2z, float q2w,
                               float t,
                               float* ox, float* oy, float* oz, float* ow) {
    float dot = q1x*q2x + q1y*q2y + q1z*q2z + q1w*q2w;

    /* Ensure shortest path */
    if (dot < 0.0f) {
        q2x = -q2x; q2y = -q2y; q2z = -q2z; q2w = -q2w;
        dot = -dot;
    }

    /* Clamp dot to valid range */
    if (dot > 1.0f) dot = 1.0f;
    if (dot < -1.0f) dot = -1.0f;

    float theta = acosf(dot);
    float sinTheta = sinf(theta);

    float s1, s2;
    if (fabsf(sinTheta) < 0.001f) {
        /* Linear interpolation for small angles */
        s1 = 1.0f - t;
        s2 = t;
    } else {
        s1 = sinf((1.0f - t) * theta) / sinTheta;
        s2 = sinf(t * theta) / sinTheta;
    }

    *ox = s1 * q1x + s2 * q2x;
    *oy = s1 * q1y + s2 * q2y;
    *oz = s1 * q1z + s2 * q2z;
    *ow = s1 * q1w + s2 * q2w;
}

/**
 * Motor interpolation (useful for smooth transform blending).
 * Uses SLERP on rotor part and LERP on translator part.
 */
static inline void pga_motor_lerp(const float m1[PGA_DIM], const float m2[PGA_DIM], float t, float out[PGA_DIM]) {
    memset(out, 0, sizeof(float) * PGA_DIM);

    /* SLERP on rotor part */
    float q1x, q1y, q1z, q1w, q2x, q2y, q2z, q2w;
    pga_motor_to_quat(m1, &q1x, &q1y, &q1z, &q1w);
    pga_motor_to_quat(m2, &q2x, &q2y, &q2z, &q2w);

    float ox, oy, oz, ow;
    quat_slerp(q1x, q1y, q1z, q1w, q2x, q2y, q2z, q2w, t, &ox, &oy, &oz, &ow);

    out[PGA_SCALAR] = ow;
    out[PGA_E23] = ox;
    out[PGA_E31] = oy;
    out[PGA_E12] = oz;

    /* LERP on translator part */
    out[PGA_E01] = m1[PGA_E01] * (1.0f - t) + m2[PGA_E01] * t;
    out[PGA_E02] = m1[PGA_E02] * (1.0f - t) + m2[PGA_E02] * t;
    out[PGA_E03] = m1[PGA_E03] * (1.0f - t) + m2[PGA_E03] * t;
}

#ifdef __cplusplus
}

/* ============================================================================
 * C++ Unreal Engine Integration Helpers
 * ============================================================================ */

#ifdef UE_BUILD
#include "Math/Vector.h"
#include "Math/Quat.h"
#include "Math/Transform.h"

namespace Grassmann {

/** Convert FVector to PGA point */
inline void FVectorToPoint(const FVector& V, float out[PGA_DIM]) {
    pga_point(V.X, V.Y, V.Z, out);
}

/** Convert PGA point to FVector */
inline FVector PointToFVector(const float p[PGA_DIM]) {
    float x, y, z;
    pga_extract_point(p, &x, &y, &z);
    return FVector(x, y, z);
}

/** Convert FTransform to PGA motor */
inline void FTransformToMotor(const FTransform& T, float out[PGA_DIM]) {
    FQuat Q = T.GetRotation();
    FVector Loc = T.GetLocation();
    pga_motor_from_ue(Q.X, Q.Y, Q.Z, Q.W, Loc.X, Loc.Y, Loc.Z, out);
}

/** Convert PGA motor to FTransform */
inline FTransform MotorToFTransform(const float motor[PGA_DIM]) {
    float qx, qy, qz, qw;
    float tx, ty, tz;
    pga_motor_to_quat(motor, &qx, &qy, &qz, &qw);
    pga_motor_to_translation(motor, &tx, &ty, &tz);
    return FTransform(FQuat(qx, qy, qz, qw), FVector(tx, ty, tz));
}

/** Apply PGA motor to FVector */
inline FVector ApplyMotorToVector(const float motor[PGA_DIM], const FVector& V) {
    float point[PGA_DIM], result[PGA_DIM];
    FVectorToPoint(V, point);
    pga_motor_apply_point(motor, point, result);
    return PointToFVector(result);
}

/** Compose two transforms using PGA */
inline FTransform ComposeTransformsPGA(const FTransform& T1, const FTransform& T2) {
    float m1[PGA_DIM], m2[PGA_DIM], result[PGA_DIM];
    FTransformToMotor(T1, m1);
    FTransformToMotor(T2, m2);
    pga_motor_compose(m1, m2, result);
    return MotorToFTransform(result);
}

/** Interpolate between two transforms using PGA motor interpolation */
inline FTransform InterpTransformsPGA(const FTransform& T1, const FTransform& T2, float Alpha) {
    float m1[PGA_DIM], m2[PGA_DIM], result[PGA_DIM];
    FTransformToMotor(T1, m1);
    FTransformToMotor(T2, m2);
    pga_motor_lerp(m1, m2, Alpha, result);
    return MotorToFTransform(result);
}

} // namespace Grassmann

#endif /* UE_BUILD */

#endif /* __cplusplus */

#endif /* GRASSMANN_PGA_UE_H */
