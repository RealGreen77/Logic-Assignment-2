#!/usr/bin/env bash
# ==============================================================================
# CS F214: Logic in Computer Science - Assignment 2
# BITS Pilani, Hyderabad Campus
# Automated Verification and Execution Runner
# ==============================================================================

set -e

# Add Dafny to PATH if installed locally
export PATH="/home/agnibh/.gemini/antigravity/bin:$PATH"

echo "======================================================================"
echo "          CS F214: LOGIC IN CS - ASSIGNMENT 2 DAFNY SUITE            "
echo "======================================================================"
echo "Checking Dafny installation..."
if ! command -v dafny &> /dev/null; then
    echo "ERROR: dafny command not found on PATH."
    exit 1
fi
echo "Using $(dafny --version)"
echo "----------------------------------------------------------------------"

FILES=(
  "Task1_Clamp.dfy"
  "Task2_Prime.dfy"
  "Task3_LargestPrimeFactor.dfy"
  "Task4_MaxProfit.dfy"
  "Assignment2.dfy"
)

echo "STEP 1: FORMAL VERIFICATION (dafny verify)"
echo "----------------------------------------------------------------------"
for f in "${FILES[@]}"; do
    echo ">>> Verifying formal specifications for $f ..."
    dafny verify "$f"
    echo "    [PASSED - 0 errors]"
done

echo ""
echo "======================================================================"
echo "STEP 2: RUNTIME TEST SUITES (dafny run -t py)"
echo "======================================================================"
for f in "${FILES[@]}"; do
    echo ">>> Executing test harness in $f ..."
    dafny run -t py "$f"
    echo "----------------------------------------------------------------------"
done

echo ""
echo "======================================================================"
echo " ALL TASKS (1, 2, 3, 4) & ASSIGNMENT2 SUITE FULLY VERIFIED & PASSED!  "
echo " Task 5 Experiments Report is available at: experiments.html          "
echo "======================================================================"
