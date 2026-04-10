#!/bin/bash
# Post-create script for Dependent MBSE research project
set -e

echo "=== Dependent MBSE Research Environment Setup ==="

# 1. Install the toolchain specified in lean-toolchain
TOOLCHAIN=$(cat lean-toolchain | tr -d '[:space:]')
echo "Installing toolchain: $TOOLCHAIN"
elan default "$TOOLCHAIN"

# 2. Update lake dependencies
echo "Updating lake dependencies..."
lake update

# 3. Fetch Mathlib precompiled cache (essential for this project)
echo "Fetching Mathlib precompiled cache..."
echo "This will take several minutes on first run."
lake exe cache get || {
    echo "WARNING: Mathlib cache fetch failed."
    echo "Try running 'lake exe cache get' manually after container starts."
}

echo ""
echo "=== Setup Complete ==="
echo "Lean version: $(lean --version)"
echo "Lake version: $(lake --version)"
echo ""
echo "Project: Dependent Type-Theoretic Semantics for MBSE"
echo "Directories:"
echo "  DependentMBSE/KerML/  - KerML Core layer encoding"
echo "  DependentMBSE/SysML/  - SysML v2 type-theoretic formalization"
echo "  Notes/                 - Research notes and study logs"
