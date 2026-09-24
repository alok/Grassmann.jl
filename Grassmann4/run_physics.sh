#!/bin/bash
# GPU Physics Pipeline Runner
# Generated from Lean

echo "Compiling Metal shaders..."
xcrun -sdk macosx metal -c physics_pga3.metal -o physics_pga3.air
xcrun -sdk macosx metallib physics_pga3.air -o physics_pga3.metallib
echo "Metal shaders compiled."

echo "Running physics simulation..."
swift physics_runner.swift
