#!/usr/bin/env bash
set -euo pipefail
kit=/opt/gtrocq
python3 "$kit/check_versions.py"
rocq --version
ocamlc -version
scratch=$(mktemp -d /tmp/gtrocq-smoke.XXXXXX)
cp "$kit/Smoke.v" "$scratch/Smoke.v"
rocq compile "$scratch/Smoke.v"
python3 "$kit/mcp_smoke.py" "$scratch/Smoke.v"
echo 'PASS: environment smoke checks (libraries load, MCP opens and closes a proof)'
