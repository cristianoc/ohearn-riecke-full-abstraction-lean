#!/usr/bin/env bash
# Run from anywhere. Failure at any stage aborts the audit.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .validation
python3 scripts/static_audit.py | tee .validation/static.json
lake update
lake exe cache get
lake build 2>&1 | tee .validation/build.log
lake env lean OR/AxiomAudit.lean 2>&1 | tee .validation/axioms.log
python3 scripts/check_axioms.py .validation/axioms.log | tee .validation/axiom-check.log
printf '\nLean build and selected-theorem axiom audit completed successfully.\n'
