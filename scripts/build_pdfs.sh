#!/usr/bin/env bash
set -euo pipefail

# Rebuilds the active LaTeX monograph in tex/main.tex into tex/build/main.pdf.
# - On bookmark `nsa`, tex/main.tex builds the Stage 1 pure Nonstandard Analysis
#   edition (archived at pdf/nn_scaling_nsa.pdf).
# - On bookmark `main`, tex/main.tex builds the Stage 2 Nonstandard Clifford
#   Analysis edition (archived at pdf/nn_scaling_clifford.pdf).

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${REPO_ROOT}/tex"

latexmk -pdf -interaction=nonstopmode -outdir=build main.tex

TARGET="${1:-clifford}"
case "${TARGET}" in
  clifford)
    cp build/main.pdf "${REPO_ROOT}/pdf/nn_scaling_clifford.pdf"
    echo "Updated pdf/nn_scaling_clifford.pdf"
    ;;
  nsa)
    cp build/main.pdf "${REPO_ROOT}/pdf/nn_scaling_nsa.pdf"
    echo "Updated pdf/nn_scaling_nsa.pdf"
    ;;
  *)
    echo "Usage: $0 [clifford|nsa]" >&2
    exit 1
    ;;
esac
