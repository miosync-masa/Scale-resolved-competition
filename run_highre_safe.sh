#!/bin/bash
# run_highre_safe.sh
# Run each high-Re case in a SEPARATE process to free GPU memory between runs.
# This prevents OOM when N=256 eats 60+ GB.

set -e
mkdir -p data
# t=0 initial verification
verify_shell_sum(solver, u_hat, v_hat, w_hat)

echo "=========================================="
echo "  HIGH-RE RUN 1: N=256, nu=0.002"
echo "=========================================="
python runs/run_highre_single.py --nu 0.002 --label nu0002

echo ""
echo "  Run 1 complete. GPU memory freed."
echo ""

echo "=========================================="  
echo "  HIGH-RE RUN 2: N=256, nu=0.001"
echo "=========================================="
python runs/run_highre_single.py --nu 0.001 --label nu0001

echo ""
echo "=========================================="
echo "  ALL HIGH-RE RUNS COMPLETE!"
echo "=========================================="
