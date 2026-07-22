#!/usr/bin/env python3
"""List or run acceptance checks for milestone files changed between two commits."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
MILESTONE_RE = re.compile(
    r"^([^/]+)/theories/conjectures/(?:grounding_|implications_)?"
    r"((?:U|D|P|X|XE|T)[A-Za-z0-9_]+)\.v$"
)


def git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def normalize_base(base: str, head: str) -> str:
    if not base or set(base) == {"0"} or git("cat-file", "-e", f"{base}^{{commit}}").returncode:
        parent = git("rev-parse", f"{head}^")
        if parent.returncode:
            raise SystemExit("cannot determine a comparison base")
        return parent.stdout.strip()
    return base


def json_at(revision: str, relpath: str) -> dict:
    proc = git("show", f"{revision}:{relpath}")
    return json.loads(proc.stdout) if proc.returncode == 0 else {}


def changed_pairs(base: str, head: str) -> tuple[list[tuple[str, str]], list[str]]:
    proc = git("diff", "--name-only", base, head)
    if proc.returncode:
        raise SystemExit(proc.stderr)
    paths = [line for line in proc.stdout.splitlines() if line]
    pairs = set()
    for path in paths:
        match = MILESTONE_RE.match(path)
        if match and not Path(path).name.startswith("_faith_"):
            package, phase = match.groups()
            pairs.add((phase, package))

    waves_path = "meta/v2_statement_waves.json"
    if waves_path in paths:
        old = json_at(base, waves_path).get("waves", {})
        new = json_at(head, waves_path).get("waves", {})
        for key in set(old) | set(new):
            if old.get(key) != new.get(key) and key in new:
                wave = new[key]
                pairs.add((wave["phase"], wave["repo"]))
    return sorted(pairs), paths


def run(command: list[str]) -> None:
    print("+ " + " ".join(command), flush=True)
    proc = subprocess.run(command, cwd=ROOT)
    if proc.returncode:
        raise SystemExit(proc.returncode)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="HEAD^")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args(argv)
    base = normalize_base(args.base, args.head)
    pairs, paths = changed_pairs(base, args.head)

    for phase, package in pairs:
        print(f"{phase} {package}")
    if not args.run:
        return 0

    run([sys.executable, "meta/foundation_fidelity.py", "--check"])
    run([sys.executable, "meta/faithfulness_lint.py", "--new-waves", "--check"])
    run(["make", "audit"])

    if any(path.startswith("base/theories/") and path.endswith(".v") for path in paths):
        run(["make", "base"])
    for phase, package in pairs:
        run([sys.executable, "meta/check_milestone.py", phase, package])
        match = re.fullmatch(r"X(\d+)", phase)
        policy = json.loads((META / "faithfulness_policy.json").read_text())
        if match and int(match.group(1)) >= int(policy["prospective_v2_wave_min"]):
            run([sys.executable, "meta/vacuity_probe.py", "--wave", phase])
    print(f"changed-milestone acceptance OK: {len(pairs)} cells from {len(paths)} changed paths")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
