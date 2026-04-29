#!/bin/bash
# =============================================================================
#  run_all.sh — Execute all simulation runs and generate figures
#
#  Usage on Colab:
#    !bash run_all.sh
#
#  Or run individually:
#    !python runs/run_baseline.py
#    !python runs/run_viscosity.py
#    ...
#    !python figures/generate_all_figures.py
# =============================================================================

set -e
mkdir -p data figures
# t=0 initial verification
verify_shell_sum(solver, u_hat, v_hat, w_hat)

echo "=========================================="
echo "  Step 1/6: Baseline TG (Fig.1)"
echo "=========================================="
python runs/run_baseline.py

echo "=========================================="
echo "  Step 2/6: Viscosity variation (Fig.2)"
echo "=========================================="
python runs/run_viscosity.py

echo "=========================================="
echo "  Step 3/6: Shell-resolved baseline (Fig.3)"
echo "=========================================="
python runs/run_shell_baseline.py

echo "=========================================="
echo "  Step 4/6: Shell-resolved low-vis (Fig.4)"
echo "=========================================="
python runs/run_shell_lowvis.py

echo "=========================================="
echo "  Step 5/6: Matched energy (Fig.5)"
echo "=========================================="
python runs/run_matched_energy.py

echo "=========================================="
echo "  Step 6/6: TG vs ABC (Fig.6)"
echo "=========================================="
python runs/run_abc.py

echo "=========================================="
echo "  Generating all figures"
echo "=========================================="
python figures/generate_all_figures.py

echo ""
echo "  DONE! All data in data/, all figures in figures/"
