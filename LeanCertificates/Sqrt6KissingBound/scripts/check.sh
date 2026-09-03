#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if rg -n --glob '*.lean' '(^|[^A-Za-z])(sorry|admit)([^A-Za-z]|$)|^[[:space:]]*axiom[[:space:]]|native_decide' \
    Sqrt6KissingBound Sqrt6KissingBound.lean Axioms.lean; then
  echo 'forbidden proof hole, project-defined axiom, or native_decide found' >&2
  exit 1
fi
lake build
lake env lean Axioms.lean
