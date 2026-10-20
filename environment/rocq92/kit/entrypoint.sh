#!/usr/bin/env bash
set -euo pipefail
umask 077
# Homes are separate per-invocation mounts. Never copy authentication caches.
mkdir -p "$HOME/.codex" "$HOME/.claude" "$HOME/mcp-scratch"
if [[ ! -e "$HOME/.codex/config.toml" ]]; then
    cp /opt/gtrocq/codex.config.toml "$HOME/.codex/config.toml"
fi
export ROCQ_WORKDIR="$HOME/mcp-scratch"
export ROCQ_PROJECT_ROOT="$PWD"
export ROCQ_QED_TIMEOUT=180
export ROCQ_STEP_TIMEOUT=30
exec "$@"
