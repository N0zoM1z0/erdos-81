#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

# Fast source-level guard; the environment audit below is authoritative and
# catches transitive uses (including generated `sorryAx` dependencies).
if rg -n '^\s*(private\s+)?axiom\b|^\s*(sorry|admit)\b|:=\s*(by\s+)?(sorry|admit)\b' \
    Erdos81 Erdos81.lean \
    --glob '!Erdos81/AxiomAudit.lean'; then
  echo "Refusing to certify a source tree containing an axiom, sorry, or admit." >&2
  exit 1
fi

lake build
lake env lean Erdos81/AxiomAudit.lean
