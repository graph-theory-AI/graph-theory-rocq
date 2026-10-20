#!/usr/bin/env python3
"""Fail if the switch drifted from the pinned graph-theory-rocq package versions."""
import pathlib
import subprocess

base = pathlib.Path(__file__).resolve().parent
rows = subprocess.check_output([
    "opam", "list", "--switch=graph-theory-rocq", "--installed",
    "--columns=name,version", "--short", "--color=never", "--readonly",
], text=True)
installed = dict(row.split() for row in rows.splitlines() if row.strip())
required = ["ocaml.5.3.0", "rocq-mcp-evolve.dev"]
required += [s for s in (base / "opam-packages.lock").read_text().splitlines()
             if s and not s.startswith("#")]
for spec in required:
    package, version = spec.split(".", 1)
    if installed.get(package) != version:
        raise SystemExit(f"Version mismatch: {spec}; installed {installed.get(package)}")
print(f"PASS: {len(required)} pinned package versions")
