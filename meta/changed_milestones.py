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
# Every build unit is a top-level directory with its own _CoqProject: base,
# classical-lemmas, the `-theory` areas, atlas and graph-theory-misc.
PACKAGE_DIRS = {
    path.name
    for path in ROOT.iterdir()
    if path.is_dir() and (path / "_CoqProject").is_file()
}
MILESTONE_RE = re.compile(
    r"^([^/]+)/theories/conjectures/(?:grounding_|implications_)?"
    r"((?:U|D|P|X|XE|T)[A-Za-z0-9_]+)\.v$"
)
PROJECT_MAPPING_RE = re.compile(r"^-[QR]\s+\.\./([^/\s]+)/theories\s")


def project_reverse_dependencies() -> dict[str, set[str]]:
    """Map each package to the packages whose _CoqProject loads its theories."""
    reverse: dict[str, set[str]] = {}
    for package in sorted(PACKAGE_DIRS):
        for line in (ROOT / package / "_CoqProject").read_text().splitlines():
            match = PROJECT_MAPPING_RE.match(line.strip())
            if match and match.group(1) not in {"base", package}:
                reverse.setdefault(match.group(1), set()).add(package)
    return reverse


# Package dependency edges not already represented by the ubiquitous GTBase
# dependency, read from the packages' `-Q ../<package>/theories` mappings (atlas
# loads every area package).  A changed package is rebuilt together with every
# reverse dependency in this closure.
REVERSE_DEPENDENCIES = project_reverse_dependencies()

MUTATION_GATE_PATHS = {
    "meta/changed_milestones.py",
    "meta/check_library_migration.py",
    "meta/test_check_library_migration.py",
    "meta/check_milestone.py",
    "meta/faithfulness_mutation.py",
    "meta/faithfulness_policy.json",
    "meta/faithfulness_lint.py",
    "meta/foundation_fidelity.py",
    "meta/foundation_fidelity.json",
    "meta/library_inventory.py",
    "meta/library_helper_inventory.json",
    "meta/library_classification.py",
    "meta/test_library_inventory_classification.py",
    "meta/library_helper_classification.json",
    "meta/library_alias_retention.py",
    "meta/test_library_inventory_alias_retention.py",
    "meta/library_primitives.json",
    "meta/family_registry.py",
    "meta/test_family_registry.py",
    "meta/migration_report.py",
    "meta/test_migration_report.py",
}

MIGRATION_GATE_PATHS = {
    "meta/changed_milestones.py",
    "meta/check_library_migration.py",
    "meta/test_check_library_migration.py",
    "meta/library_inventory.py",
    "meta/library_helper_inventory.json",
    "meta/library_primitives.json",
    "meta/family_registry.py",
    "meta/test_family_registry.py",
    "meta/migration_report.py",
    "meta/test_migration_report.py",
    "base/theories/simple_edges.v",
}


def git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def family_registry_change(path: str) -> bool:
    """Family documents need the same gates as the former aggregate registries."""
    return path.startswith(("meta/library_primitives/", "meta/foundation_fidelity/"))


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


def package_source_change(path: str) -> str | None:
    """Return the package whose compilable source/config changed."""
    parts = Path(path).parts
    if not parts or parts[0] not in PACKAGE_DIRS:
        return None
    if path.endswith(".v") or path.endswith(".opam"):
        return parts[0]
    if len(parts) == 2 and parts[1] in {"_CoqProject", "Makefile"}:
        return parts[0]
    return None


def migration_report_change(path: str) -> bool:
    return (path in {"meta/migration_report.py", "meta/test_migration_report.py"}
            or path.startswith("meta/migration_reports/"))


def reverse_dependency_closure(packages: set[str]) -> set[str]:
    closure = set(packages)
    while True:
        expanded = closure | {
            dependent
            for package in closure
            for dependent in REVERSE_DEPENDENCIES.get(package, set())
        }
        if expanded == closure:
            return closure
        closure = expanded


def validate_project_membership(paths: list[str]) -> None:
    """Reject a new/renamed Rocq source that its package build would ignore."""
    errors = []
    for path in paths:
        package = package_source_change(path)
        source = ROOT / path
        if not package or not path.endswith(".v") or not source.exists():
            continue
        relative = source.relative_to(ROOT / package).as_posix()
        project = ROOT / package / "_CoqProject"
        listed = {
            line.split("#", 1)[0].strip()
            for line in project.read_text().splitlines()
            if line.split("#", 1)[0].strip().endswith(".v")
        }
        if relative not in listed:
            errors.append(f"{path}: missing from {package}/_CoqProject")
    if errors:
        raise SystemExit("changed Rocq sources excluded from package builds:\n  " + "\n  ".join(errors))


def validate_routing_fixtures() -> None:
    for path in ("meta/library_primitives/induced-free.json",
                 "meta/foundation_fidelity/induced-free.json"):
        if not family_registry_change(path):
            raise SystemExit(f"family registry routing fixture failed: {path}")
    if family_registry_change("meta/library_primitives_wrong/other.json"):
        raise SystemExit("family registry routing accepted an unrelated directory")
    for path in ("meta/migration_report.py", "meta/test_migration_report.py",
                 "meta/migration_reports/induced_free.spec.json", "meta/migration_reports/matching.md"):
        if not migration_report_change(path):
            raise SystemExit(f"migration report routing fixture failed: {path}")
    fixtures = {
        "base/_CoqProject": "base",
        "classical-lemmas/_CoqProject": "classical-lemmas",
        "classical-lemmas/theories/konig/line_colouring.v": "classical-lemmas",
        "classical-lemmas/theories/migration/incidence.v": "classical-lemmas",
        "classical-lemmas-other/theories/konig/line_colouring.v": None,
        "chromatic-theory/theories/migration/simple_edges.v": "chromatic-theory",
        "digraph-theory/rocq-digraph-theory.opam": "digraph-theory",
        "atlas/theories/conjectures/implications_A2.v": "atlas",
        "atlas/_CoqProject": "atlas",
        "graph-theory-misc/theories/conjectures/X14.v": "graph-theory-misc",
        "graph-theory-misc/_CoqProject": "graph-theory-misc",
        "blueprint/README.md": None,
        "meta/check_milestone.py": None,
    }
    for path, expected in fixtures.items():
        actual = package_source_change(path)
        if actual != expected:
            raise SystemExit(f"routing fixture failed for {path}: {actual!r} != {expected!r}")
    expected_closures = {
        "topological-graph-theory": {
            "topological-graph-theory",
            "hamiltonicity-theory",
            "packing-theory",
            "graph-theory-misc",
            "atlas",
        },
        "classical-lemmas": {"classical-lemmas", "packing-theory", "atlas"},
        "minor-theory": {"minor-theory", "graph-theory-misc", "atlas"},
        "chromatic-theory": {"chromatic-theory", "atlas"},
        "digraph-theory": {"digraph-theory", "atlas"},
        "graph-theory-misc": {"graph-theory-misc", "atlas"},
        "atlas": {"atlas"},
    }
    for package, expected_closure in expected_closures.items():
        actual_closure = reverse_dependency_closure({package})
        if actual_closure != expected_closure:
            raise SystemExit(f"reverse-dependency fixture failed for {package}: {actual_closure!r}")
    print("changed-path routing fixtures OK")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="HEAD^")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--validate", action="store_true", help="run deterministic routing fixtures")
    args = parser.parse_args(argv)
    if args.validate:
        validate_routing_fixtures()
        return 0
    base = normalize_base(args.base, args.head)
    pairs, paths = changed_pairs(base, args.head)

    for phase, package in pairs:
        print(f"{phase} {package}")
    if not args.run:
        return 0

    validate_project_membership(paths)
    if any(path.startswith("meta/") and path.endswith(".py") for path in paths):
        run([sys.executable, "-m", "compileall", "-q", "meta"])
    run([sys.executable, "meta/foundation_fidelity.py", "--check"])
    run([sys.executable, "meta/faithfulness_lint.py", "--new-waves", "--check"])
    run(["make", "audit"])

    changed_packages = {
        package for path in paths if (package := package_source_change(path))
    }
    base_changed = "base" in changed_packages or "Makefile" in paths
    if base_changed:
        # A shared foundation change must compile its reverse dependencies, not
        # merely GTBase itself. The root `all` target follows package topology.
        run(["make", "all"])
    else:
        build_packages = sorted(reverse_dependency_closure(changed_packages))
        if build_packages:
            run(["make", *build_packages])

    changed_opams = [path for path in paths if path.endswith(".opam") and (ROOT / path).exists()]
    if changed_opams:
        run(["opam", "lint", *changed_opams])

    mutation_changed = any(
        path in MUTATION_GATE_PATHS or family_registry_change(path)
        or path.startswith("meta/probe_hints/") or migration_report_change(path)
        for path in paths
    )
    if mutation_changed:
        run(["make", "mutation"])

    migration_changed = base_changed or "classical-lemmas" in changed_packages or any(
        path in MIGRATION_GATE_PATHS or family_registry_change(path)
        or "/theories/migration/" in path or migration_report_change(path)
        for path in paths
    )
    if migration_changed:
        run([sys.executable, "meta/check_library_migration.py"])
        run([sys.executable, "meta/migration_report.py", "--all", "--check", "--kernel"])
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
