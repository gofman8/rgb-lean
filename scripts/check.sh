#!/usr/bin/env bash
# Builds every module (running every #guard scenario check) and refuses a proof
# hole, a declared axiom or a construct that trusts compiled code.
set -euo pipefail
cd "$(dirname "$0")/.."

if grep -rnwE 'sorry|admit|native_decide|bv_decide|implemented_by|extern' Rgb Rgb.lean; then
  echo "check: refused a proof hole or a construct outside the kernel" >&2
  exit 1
fi
if grep -rnE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable)[[:space:]]+)*axiom[[:space:]]' Rgb Rgb.lean; then
  echo "check: refused a declared axiom" >&2
  exit 1
fi

lake build
