#!/usr/bin/env julia
#=
  grassmann_oracle.jl - Julia oracle for verifying Lean Grassmann computations

  This script provides a reference implementation using Grassmann.jl
  that can be called from Lean tests to verify correctness.

  Usage:
    julia grassmann_oracle.jl test
    julia grassmann_oracle.jl geometric_product "R3" "e1" "e2"

  Output: JSON with result and metadata
=#

using Grassmann
using JSON

# Signature definitions
const SIGNATURES = Dict(
    "R2" => S"++",
    "R3" => S"+++",
    "R4" => S"++++",
    "PGA2" => S"++0",
    "PGA3" => S"+++0",
    "CGA2" => S"+++-",
    "CGA3" => S"++++-",
    "STA" => S"+---",
)

"""
Get the algebra/bundle for a signature name.
"""
function get_algebra(sig_name::String)
    sig = SIGNATURES[sig_name]
    return Λ(sig)  # Returns the full Grassmann algebra bundle
end

"""
Get the i-th basis vector for an algebra.
The algebra is indexed as: alg[1]=scalar, alg[2]=v₁, alg[3]=v₂, ...
"""
function basis_vector(alg, i::Int)
    return alg[i + 1]  # +1 because alg[1] is the scalar
end

"""
Parse a blade string (e.g., "e1", "e12", "e123") into a multivector.
"""
function parse_blade(s::String, alg)
    if s == "1" || s == "scalar"
        return 1.0 * alg[1]  # Scalar identity element
    end
    if startswith(s, "e")
        indices = [parse(Int, string(c)) for c in s[2:end]]
        result = basis_vector(alg, indices[1])
        for i in indices[2:end]
            result *= basis_vector(alg, i)
        end
        return result
    end
    # Scalar coefficient
    return parse(Float64, s) * alg[1]
end

"""
Extract the coefficient of a non-null target blade from a multivector.

For basis blade B, scalar(x * ~B) / scalar(B * ~B) gives the coefficient of B.
This intentionally rejects null blades, where that projection is singular.
"""
function blade_coefficient(x, blade)
    denom = scalar(blade * ~blade)
    if abs(Float64(denom)) < 1e-12
        error("Cannot extract coefficient for null blade")
    end
    return Float64(scalar(x * ~blade) / denom)
end

"""
Compute a binary Grassmann operation by command name.
"""
function binary_operation(op::String, a, b)
    if op == "geometric_product"
        return a * b
    elseif op == "wedge_product"
        return a ∧ b
    elseif op == "left_contraction"
        return a < b
    elseif op == "right_contraction"
        return a > b
    else
        error("Unsupported coefficient operation: $op")
    end
end

"""
Interactive test mode: verify common identities.
"""
function run_tests()
    println("=== Grassmann.jl Oracle Tests ===\n")

    # R3 algebra
    alg3 = get_algebra("R3")
    e1 = basis_vector(alg3, 1)
    e2 = basis_vector(alg3, 2)
    e3 = basis_vector(alg3, 3)

    # Test 1: R3 basis squares
    println("Test 1: R3 basis vectors square to 1")
    println("  e1² = $(scalar(e1*e1))")  # Should be 1
    println("  e2² = $(scalar(e2*e2))")  # Should be 1
    println("  e3² = $(scalar(e3*e3))")  # Should be 1

    # Test 2: Wedge anticommutes
    println("\nTest 2: Wedge product anticommutes")
    println("  e1∧e2 = $(e1 ∧ e2)")
    println("  e2∧e1 = $(e2 ∧ e1)")
    println("  e1∧e2 + e2∧e1 = $(e1∧e2 + e2∧e1)")  # Should be 0

    # Test 3: Geometric product decomposition
    println("\nTest 3: Geometric product e1*e2")
    println("  e1*e2 = $(e1*e2)")  # Should be e12
    println("  e2*e1 = $(e2*e1)")  # Should be -e12

    # Test 4: Pseudoscalar
    println("\nTest 4: Pseudoscalar I = e123")
    I = e1*e2*e3
    println("  I = $I")
    println("  I² = $(I*I)")  # Should be -1 for R3

    # Test 5: Rotor rotation
    println("\nTest 5: 90° rotation of e1 around e12")
    θ = π/2
    B = e1*e2
    R = exp(θ/2 * B)
    rotated = R >>> e1
    println("  Rotor R = exp(π/4·e12)")
    println("  R scalar = $(scalar(R))")  # cos(π/4) ≈ 0.707
    println("  R·e1·R† = $rotated")
    println("  Expected: e2 direction")

    # CGA Tests
    println("\n=== CGA Tests ===")
    alg5 = get_algebra("CGA3")
    w1 = basis_vector(alg5, 1)
    w2 = basis_vector(alg5, 2)
    w3 = basis_vector(alg5, 3)
    w4 = basis_vector(alg5, 4)  # e+ (squares to +1)
    w5 = basis_vector(alg5, 5)  # e- (squares to -1)

    println("\nTest 6: CGA basis signature")
    println("  e1² = $(scalar(w1*w1))")  # +1
    println("  e2² = $(scalar(w2*w2))")  # +1
    println("  e3² = $(scalar(w3*w3))")  # +1
    println("  e4² = $(scalar(w4*w4))")  # +1
    println("  e5² = $(scalar(w5*w5))")  # -1

    # Null basis (standard CGA convention)
    einf = w4 + w5
    e0 = (w5 - w4) / 2
    println("\nTest 7: Null basis properties")
    println("  e∞ = e4 + e5")
    println("  e0 = (e5 - e4)/2")
    println("  e∞² = $(scalar(einf*einf))")  # Should be 0
    println("  e0² = $(scalar(e0*e0))")      # Should be 0
    println("  e∞·e0 = $(scalar(einf*e0 + e0*einf)/2)")  # Should be -1

    # Test 8: Point at (1,0,0)
    println("\nTest 8: CGA point at (1,0,0) is null")
    p = w1  # Euclidean part
    p_sq = 1.0
    P = p + (p_sq/2)*einf + e0
    println("  P = p + (|p|²/2)e∞ + e0")
    println("  P² = $(scalar(P*P))")  # Should be 0

    # Test 9: Distance between points
    println("\nTest 9: Distance between points")
    P1 = e0  # Origin
    P2 = w1 + (1/2)*einf + e0  # Point at (1,0,0)
    # d² = -2(P1·P2) for normalized points
    inner = scalar(P1*P2 + P2*P1)/2
    println("  P1·P2 = $inner")
    println("  d² = $(-2*inner)")  # Should be 1

    println("\n=== Tests Complete ===")
end

"""
Compute geometric product.
"""
function cmd_geometric_product(sig_name::String, blade_a::String, blade_b::String)
    alg = get_algebra(sig_name)

    a = parse_blade(blade_a, alg)
    b = parse_blade(blade_b, alg)
    result = a * b

    return Dict(
        "operation" => "geometric_product",
        "signature" => sig_name,
        "a" => blade_a,
        "b" => blade_b,
        "result" => string(result),
        "scalar_part" => Float64(scalar(result))
    )
end

"""
Compute wedge (outer) product.
"""
function cmd_wedge_product(sig_name::String, blade_a::String, blade_b::String)
    alg = get_algebra(sig_name)

    a = parse_blade(blade_a, alg)
    b = parse_blade(blade_b, alg)
    result = a ∧ b

    return Dict(
        "operation" => "wedge_product",
        "signature" => sig_name,
        "a" => blade_a,
        "b" => blade_b,
        "result" => string(result),
        "scalar_part" => Float64(scalar(result))
    )
end

"""
Compute left contraction.
"""
function cmd_left_contraction(sig_name::String, blade_a::String, blade_b::String)
    alg = get_algebra(sig_name)

    a = parse_blade(blade_a, alg)
    b = parse_blade(blade_b, alg)
    result = a < b

    return Dict(
        "operation" => "left_contraction",
        "signature" => sig_name,
        "a" => blade_a,
        "b" => blade_b,
        "result" => string(result),
        "scalar_part" => Float64(scalar(result))
    )
end

"""
Compute right contraction.
"""
function cmd_right_contraction(sig_name::String, blade_a::String, blade_b::String)
    alg = get_algebra(sig_name)

    a = parse_blade(blade_a, alg)
    b = parse_blade(blade_b, alg)
    result = a > b

    return Dict(
        "operation" => "right_contraction",
        "signature" => sig_name,
        "a" => blade_a,
        "b" => blade_b,
        "result" => string(result),
        "scalar_part" => Float64(scalar(result))
    )
end

"""
Compute one target blade coefficient for a binary operation.
"""
function cmd_blade_coefficient(
    sig_name::String,
    operation::String,
    blade_a::String,
    blade_b::String,
    target_blade::String,
)
    alg = get_algebra(sig_name)

    a = parse_blade(blade_a, alg)
    b = parse_blade(blade_b, alg)
    target = parse_blade(target_blade, alg)
    result = binary_operation(operation, a, b)
    coeff = blade_coefficient(result, target)

    return Dict(
        "operation" => "blade_coefficient",
        "binary_operation" => operation,
        "signature" => sig_name,
        "a" => blade_a,
        "b" => blade_b,
        "target_blade" => target_blade,
        "result" => string(result),
        "coefficient" => coeff,
    )
end

"""
Run CGA point embedding test.
"""
function cmd_point_embedding(x::Float64, y::Float64, z::Float64)
    alg = get_algebra("CGA3")
    w1 = basis_vector(alg, 1)
    w2 = basis_vector(alg, 2)
    w3 = basis_vector(alg, 3)
    w4 = basis_vector(alg, 4)
    w5 = basis_vector(alg, 5)

    einf = w4 + w5
    e0 = (w5 - w4) / 2

    p = x*w1 + y*w2 + z*w3
    p_sq = x^2 + y^2 + z^2
    P = p + (p_sq/2)*einf + e0
    P_sq = Float64(scalar(P*P))

    return Dict(
        "operation" => "point_embedding",
        "x" => x, "y" => y, "z" => z,
        "point_squared" => P_sq,
        "is_null" => abs(P_sq) < 1e-10
    )
end

"""
Compute the squared Euclidean distance and distance between two normalized CGA points.
"""
function cmd_cga_point_distance(
    x1::Float64,
    y1::Float64,
    z1::Float64,
    x2::Float64,
    y2::Float64,
    z2::Float64,
)
    alg = get_algebra("CGA3")
    w1 = basis_vector(alg, 1)
    w2 = basis_vector(alg, 2)
    w3 = basis_vector(alg, 3)
    w4 = basis_vector(alg, 4)
    w5 = basis_vector(alg, 5)

    einf = w4 + w5
    e0 = (w5 - w4) / 2

    p1 = x1*w1 + y1*w2 + z1*w3 + ((x1^2 + y1^2 + z1^2) / 2)*einf + e0
    p2 = x2*w1 + y2*w2 + z2*w3 + ((x2^2 + y2^2 + z2^2) / 2)*einf + e0
    inner = Float64(scalar(p1*p2 + p2*p1) / 2)
    squared_distance = -2.0 * inner
    distance = squared_distance < 0.0 ? 0.0 : sqrt(squared_distance)

    return Dict(
        "operation" => "cga_point_distance",
        "point1" => [x1, y1, z1],
        "point2" => [x2, y2, z2],
        "inner" => inner,
        "squared_distance" => squared_distance,
        "distance" => distance,
    )
end

"""
Translate a CGA point by a Euclidean vector and return down-projected coordinates.
"""
function cmd_cga_translate_point(
    x::Float64,
    y::Float64,
    z::Float64,
    tx::Float64,
    ty::Float64,
    tz::Float64,
)
    alg = get_algebra("CGA3")
    w1 = basis_vector(alg, 1)
    w2 = basis_vector(alg, 2)
    w3 = basis_vector(alg, 3)
    w4 = basis_vector(alg, 4)
    w5 = basis_vector(alg, 5)

    einf = w4 + w5
    e0 = (w5 - w4) / 2

    p = x*w1 + y*w2 + z*w3 + ((x^2 + y^2 + z^2) / 2)*einf + e0
    t = tx*w1 + ty*w2 + tz*w3
    translator = exp(-0.5 * t * einf)
    translated = translator >>> p

    coords = [
        blade_coefficient(translated, w1),
        blade_coefficient(translated, w2),
        blade_coefficient(translated, w3),
    ]

    return Dict(
        "operation" => "cga_translate_point",
        "point" => [x, y, z],
        "translation" => [tx, ty, tz],
        "coords" => coords,
        "point_squared" => Float64(scalar(translated * translated)),
    )
end

"""
Compose two CGA translators, apply them to a point, and return coordinates.
The composition order matches Lean's `CGA.transform (t₂ * t₁) p`, meaning
translation one is applied first and translation two second.
"""
function cmd_cga_translate_point_composed(
    x::Float64,
    y::Float64,
    z::Float64,
    tx1::Float64,
    ty1::Float64,
    tz1::Float64,
    tx2::Float64,
    ty2::Float64,
    tz2::Float64,
)
    alg = get_algebra("CGA3")
    w1 = basis_vector(alg, 1)
    w2 = basis_vector(alg, 2)
    w3 = basis_vector(alg, 3)
    w4 = basis_vector(alg, 4)
    w5 = basis_vector(alg, 5)

    einf = w4 + w5
    e0 = (w5 - w4) / 2

    p = x*w1 + y*w2 + z*w3 + ((x^2 + y^2 + z^2) / 2)*einf + e0
    delta1 = tx1*w1 + ty1*w2 + tz1*w3
    delta2 = tx2*w1 + ty2*w2 + tz2*w3
    translator1 = exp(-0.5 * delta1 * einf)
    translator2 = exp(-0.5 * delta2 * einf)
    translated = (translator2 * translator1) >>> p

    coords = [
        blade_coefficient(translated, w1),
        blade_coefficient(translated, w2),
        blade_coefficient(translated, w3),
    ]

    return Dict(
        "operation" => "cga_translate_point_composed",
        "point" => [x, y, z],
        "translation1" => [tx1, ty1, tz1],
        "translation2" => [tx2, ty2, tz2],
        "coords" => coords,
        "point_squared" => Float64(scalar(translated * translated)),
    )
end

"""
Verify rotor normalization and action.
"""
function cmd_verify_rotor(sig_name::String, angle::Float64)
    alg = get_algebra(sig_name)
    e1 = basis_vector(alg, 1)
    e2 = basis_vector(alg, 2)

    B = e1 * e2
    R = exp(angle/2 * B)
    R_rev = ~R
    norm = scalar(R * R_rev)
    rotated = R >>> e1

    return Dict(
        "operation" => "verify_rotor",
        "signature" => sig_name,
        "angle_rad" => angle,
        "angle_deg" => rad2deg(angle),
        "rotor_scalar" => Float64(scalar(R)),
        "normalization" => Float64(norm),
        "rotated_v1" => string(rotated)
    )
end

"""
Get basis vector squares (signature diagonal).
"""
function cmd_signature_check(sig_name::String)
    alg = get_algebra(sig_name)
    sig = SIGNATURES[sig_name]
    n = length(sig)  # Number of basis vectors
    squares = [Float64(scalar(basis_vector(alg, i) * basis_vector(alg, i))) for i in 1:n]

    return Dict(
        "operation" => "signature_check",
        "signature" => sig_name,
        "dimension" => n,
        "basis_squares" => squares
    )
end

"""
Compute exponential of a bivector.
"""
function cmd_bivector_exp(sig_name::String, i::Int, j::Int, angle::Float64)
    alg = get_algebra(sig_name)
    ei = basis_vector(alg, i)
    ej = basis_vector(alg, j)

    B = ei * ej
    result = exp(angle * B)

    return Dict(
        "operation" => "bivector_exp",
        "signature" => sig_name,
        "bivector" => "e$(i)$(j)",
        "angle" => angle,
        "result" => string(result),
        "scalar_part" => Float64(scalar(result))
    )
end

"""
Compute the R3 cross product coordinates using the Grassmann algebra identity
`a × b = ⋆(a ∧ b)` with the standard right-handed orientation.
"""
function cmd_r3_cross(blade_a::String, blade_b::String)
    alg = get_algebra("R3")
    e1 = basis_vector(alg, 1)
    e2 = basis_vector(alg, 2)
    e3 = basis_vector(alg, 3)

    a = parse_blade(blade_a, alg)
    b = parse_blade(blade_b, alg)
    wedge = a ∧ b

    e12 = e1 * e2
    e13 = e1 * e3
    e23 = e2 * e3
    coords = [
        blade_coefficient(wedge, e23),
        -blade_coefficient(wedge, e13),
        blade_coefficient(wedge, e12),
    ]

    return Dict(
        "operation" => "r3_cross",
        "a" => blade_a,
        "b" => blade_b,
        "coords" => coords,
    )
end

"""
Compute the determinant of three R3 column vectors via exterior algebra.
"""
function cmd_r3_det(
    x1::Float64,
    y1::Float64,
    z1::Float64,
    x2::Float64,
    y2::Float64,
    z2::Float64,
    x3::Float64,
    y3::Float64,
    z3::Float64,
)
    alg = get_algebra("R3")
    e1 = basis_vector(alg, 1)
    e2 = basis_vector(alg, 2)
    e3 = basis_vector(alg, 3)

    v1 = x1*e1 + y1*e2 + z1*e3
    v2 = x2*e1 + y2*e2 + z2*e3
    v3 = x3*e1 + y3*e2 + z3*e3
    pseudoscalar = e1 * e2 * e3
    determinant = blade_coefficient(v1 ∧ v2 ∧ v3, pseudoscalar)

    return Dict(
        "operation" => "r3_det",
        "columns" => [[x1, y1, z1], [x2, y2, z2], [x3, y3, z3]],
        "determinant" => determinant,
    )
end

"""
Evaluate one of the documented plot-producing examples from docs/src/algebra.md
at a scalar parameter and return Euclidean plotting coordinates.
"""
function cmd_julia_example_point(example_name::String, t::Float64)
    if example_name == "projective_torus"
        @basis S"∞+++"
        y = ↓(exp(pi * t * ((3 / 7) * v12 + v∞3)) >>> ↑(v1 + v2 + v3))
        vals = value(y)

        return Dict(
            "operation" => "julia_example_point",
            "example" => example_name,
            "t" => t,
            "coords" => [Float64(vals[2]), Float64(vals[3]), Float64(vals[4])],
        )
    elseif example_name == "projective_orbit_2"
        @basis S"∞+++"
        y = ↓(exp(t * v∞ * (sin(3t) * 3v1 + cos(2t) * 7v2 - sin(5t) * 4v3) / 2) >>> ↑(v1 + v2 - v3))
        vals = value(y)

        return Dict(
            "operation" => "julia_example_point",
            "example" => example_name,
            "t" => t,
            "coords" => [Float64(vals[2]), Float64(vals[3]), Float64(vals[4])],
        )
    elseif example_name == "projective_orbit_4"
        @basis S"∞+++"
        y = ↓(exp(t * (v12 + 0.07v∞ * (sin(3t) * 3v1 + cos(2t) * 7v2 - sin(5t) * 4v3) / 2)) >>> ↑(v1 + v2 - v3))
        vals = value(y)

        return Dict(
            "operation" => "julia_example_point",
            "example" => example_name,
            "t" => t,
            "coords" => [Float64(vals[2]), Float64(vals[3]), Float64(vals[4])],
        )
    else
        error("Unsupported Julia example point: $example_name")
    end
end

# Main
function main()
    if length(ARGS) == 0 || ARGS[1] == "test"
        run_tests()
        return
    end

    cmd = ARGS[1]

    result = try
        if cmd == "geometric_product" && length(ARGS) >= 4
            cmd_geometric_product(ARGS[2], ARGS[3], ARGS[4])
        elseif cmd == "wedge_product" && length(ARGS) >= 4
            cmd_wedge_product(ARGS[2], ARGS[3], ARGS[4])
        elseif cmd == "left_contraction" && length(ARGS) >= 4
            cmd_left_contraction(ARGS[2], ARGS[3], ARGS[4])
        elseif cmd == "right_contraction" && length(ARGS) >= 4
            cmd_right_contraction(ARGS[2], ARGS[3], ARGS[4])
        elseif cmd == "blade_coefficient" && length(ARGS) >= 6
            cmd_blade_coefficient(ARGS[2], ARGS[3], ARGS[4], ARGS[5], ARGS[6])
        elseif cmd == "point_embedding" && length(ARGS) >= 4
            cmd_point_embedding(parse(Float64, ARGS[2]),
                              parse(Float64, ARGS[3]),
                              parse(Float64, ARGS[4]))
        elseif cmd == "cga_point_distance" && length(ARGS) >= 7
            cmd_cga_point_distance(parse(Float64, ARGS[2]),
                                   parse(Float64, ARGS[3]),
                                   parse(Float64, ARGS[4]),
                                   parse(Float64, ARGS[5]),
                                   parse(Float64, ARGS[6]),
                                   parse(Float64, ARGS[7]))
        elseif cmd == "cga_translate_point" && length(ARGS) >= 7
            cmd_cga_translate_point(parse(Float64, ARGS[2]),
                                    parse(Float64, ARGS[3]),
                                    parse(Float64, ARGS[4]),
                                    parse(Float64, ARGS[5]),
                                    parse(Float64, ARGS[6]),
                                    parse(Float64, ARGS[7]))
        elseif cmd == "cga_translate_point_composed" && length(ARGS) >= 10
            cmd_cga_translate_point_composed(parse(Float64, ARGS[2]),
                                             parse(Float64, ARGS[3]),
                                             parse(Float64, ARGS[4]),
                                             parse(Float64, ARGS[5]),
                                             parse(Float64, ARGS[6]),
                                             parse(Float64, ARGS[7]),
                                             parse(Float64, ARGS[8]),
                                             parse(Float64, ARGS[9]),
                                             parse(Float64, ARGS[10]))
        elseif cmd == "verify_rotor" && length(ARGS) >= 3
            cmd_verify_rotor(ARGS[2], parse(Float64, ARGS[3]))
        elseif cmd == "signature_check" && length(ARGS) >= 2
            cmd_signature_check(ARGS[2])
        elseif cmd == "bivector_exp" && length(ARGS) >= 5
            cmd_bivector_exp(ARGS[2], parse(Int, ARGS[3]),
                           parse(Int, ARGS[4]), parse(Float64, ARGS[5]))
        elseif cmd == "r3_cross" && length(ARGS) >= 3
            cmd_r3_cross(ARGS[2], ARGS[3])
        elseif cmd == "r3_det" && length(ARGS) >= 10
            cmd_r3_det(parse(Float64, ARGS[2]),
                       parse(Float64, ARGS[3]),
                       parse(Float64, ARGS[4]),
                       parse(Float64, ARGS[5]),
                       parse(Float64, ARGS[6]),
                       parse(Float64, ARGS[7]),
                       parse(Float64, ARGS[8]),
                       parse(Float64, ARGS[9]),
                       parse(Float64, ARGS[10]))
        elseif cmd == "julia_example_point" && length(ARGS) >= 3
            cmd_julia_example_point(ARGS[2], parse(Float64, ARGS[3]))
        else
            Dict("error" => "Unknown command: $cmd",
                 "usage" => """Commands:
  test                                  - Run test suite
  geometric_product <sig> <a> <b>       - Compute a*b
  wedge_product <sig> <a> <b>           - Compute a∧b
  left_contraction <sig> <a> <b>        - Compute a⌋b
  right_contraction <sig> <a> <b>       - Compute a⌊b
  blade_coefficient <sig> <op> <a> <b> <target>
                                        - Coefficient of target in op(a,b)
  point_embedding <x> <y> <z>           - CGA point embedding
  cga_point_distance <x1> <y1> <z1> <x2> <y2> <z2>
                                        - CGA point distance
  cga_translate_point <x> <y> <z> <tx> <ty> <tz>
                                        - Translate a CGA point
  cga_translate_point_composed <x> <y> <z> <tx1> <ty1> <tz1> <tx2> <ty2> <tz2>
                                        - Compose two CGA translations
  verify_rotor <sig> <angle>            - Verify rotor
  signature_check <sig>                 - Check basis squares
  bivector_exp <sig> <i> <j> <angle>    - exp(angle*eij)
  r3_cross <a> <b>                       - R3 cross product coordinates
  r3_det <c1x> <c1y> <c1z> <c2x> <c2y> <c2z> <c3x> <c3y> <c3z>
                                        - R3 determinant from column vectors
  julia_example_point <name> <t>          - Documented plot example coordinates

Signatures: R2, R3, R4, PGA2, PGA3, CGA2, CGA3, STA""")
        end
    catch e
        Dict("error" => string(e), "backtrace" => sprint(showerror, e, catch_backtrace()))
    end

    println(JSON.json(result))
end

main()
