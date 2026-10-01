"""Shared resolution of the repository's pinned Rocq/opam toolchain."""

from __future__ import annotations

import os
from pathlib import Path


def environment() -> dict[str, str]:
    """Prefer ROCQ_OPAM_SWITCH when set, otherwise the historical digraph switch.

    The override accepts an opam switch name or an absolute switch directory.
    Explicit selection is necessary when .vo files were built with a different
    OCaml version; the Rocq version alone does not identify compatible objects.
    """
    env = dict(os.environ)
    selected = env.get("ROCQ_OPAM_SWITCH", "digraph")
    switch = Path(selected) if Path(selected).is_absolute() else Path.home() / ".opam" / selected
    switch_bin = switch / "bin"
    if "ROCQ_OPAM_SWITCH" in env and not switch_bin.is_dir():
        raise RuntimeError(f"ROCQ_OPAM_SWITCH has no bin directory: {switch_bin}")
    if switch_bin.is_dir():
        env["PATH"] = str(switch_bin) + os.pathsep + env.get("PATH", "")
        env["OPAM_SWITCH_PREFIX"] = str(switch)
    return env
