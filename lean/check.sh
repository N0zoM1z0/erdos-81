#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if rg -n '^\s*(axiom|sorry)\b' Erdos81 Erdos81.lean; then
  echo "Refusing to certify a source tree containing an axiom or sorry declaration." >&2
  exit 1
fi

lake build
lake env lean Erdos81/AxiomAudit.lean
