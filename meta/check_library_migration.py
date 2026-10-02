#!/usr/bin/env python3
"""Axiom-audit public library APIs and migration compatibility certificates."""

from __future__ import annotations

import json
import re
import shlex
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

import rocq_toolchain as ROCQ


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "meta" / "library_primitives.json"

NAMESPACE_PACKAGES = {
    "GTBase": "base",
    "Chromatic": "chromatic-theory",
    "Hamilton": "hamiltonicity-theory",
    "Hom": "homomorphism-theory",
    "Cycle": "cycle-theory",
    "Minor": "minor-theory",
    "Packing": "packing-theory",
    "Reconstruction": "reconstruction-theory",
    "Hypergraph": "hypergraph-theory",
    "Topological": "topological-graph-theory",
    "GTMisc": "graph-theory-misc",
    "Spectral": "spectral-graph-theory",
    "Extremal": "extremal-graph-theory",
    "Infinite": "infinite-graph-theory",
    "Digraph": "digraph-theory",
}


def include_flags(project: Path) -> list[str]:
    flags: list[str] = []
    tokens = shlex.split(project.read_text(), comments=True)
    i = 0
    while i < len(tokens):
        if tokens[i] in {"-R", "-Q"} and i + 2 < len(tokens):
            flags.extend(tokens[i:i + 3])
            i += 3
        else:
            i += 1
    return flags


def source_for_module(package: str, module: str) -> Path:
    namespace, *parts = module.split(".")
    if NAMESPACE_PACKAGES.get(namespace) != package:
        raise ValueError(f"module/package mismatch: {module} / {package}")
    return ROOT / package / "theories" / Path(*parts).with_suffix(".v")


def project_dependencies(package: str) -> list[str]:
    project = ROOT / package / "_CoqProject"
    if not project.is_file():
        return []
    tokens = shlex.split(project.read_text(), comments=True)
    deps: list[str] = []
    for index, token in enumerate(tokens[:-2]):
        if token not in {"-R", "-Q"}:
            continue
        path = Path(tokens[index + 1])
        parts = path.parts
        if len(parts) == 3 and parts[0] == ".." and parts[2] == "theories":
            dep = parts[1]
            if (ROOT / dep / "_CoqProject").is_file() and dep not in deps:
                deps.append(dep)
    return deps


def dependency_order(packages: set[str]) -> tuple[list[str], set[str]]:
    order: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()
    dependency_packages: set[str] = set()

    def visit(package: str) -> None:
        if package in visited:
            return
        if package in visiting:
            raise ValueError(f"package dependency cycle at {package}")
        visiting.add(package)
        for dep in project_dependencies(package):
            dependency_packages.add(dep)
            visit(dep)
        visiting.remove(package)
        visited.add(package)
        order.append(package)

    for package in sorted(packages):
        visit(package)
    return order, dependency_packages


def main() -> int:
    data = json.loads(REGISTRY.read_text())
    by_module: dict[str, list[str]] = defaultdict(list)
    for spec in data["primitives"].values():
        if spec.get("status") not in {"canonical", "migrating", "deprecated", "complete"}:
            continue
        for name in spec.get("api_theorems", []) + spec.get("compatibility_theorems", []):
            module, _, _ = name.rpartition(".")
            by_module[module].append(name)

    errors: list[str] = []
    checked = 0
    env = ROCQ.environment()
    sources_by_package: dict[str, set[Path]] = defaultdict(set)
    for module in by_module:
        namespace = module.split(".", 1)[0]
        package = NAMESPACE_PACKAGES.get(namespace)
        if package is not None:
            sources_by_package[package].add(source_for_module(package, module))

    # Compile the exact registry-owned modules through each package project.
    # Forcing these targets prevents an old, clean .vo from masking a changed
    # source theorem during a standalone assumptions audit.
    failed_packages: set[str] = set()
    try:
        package_order, dependency_packages = dependency_order(set(sources_by_package))
    except ValueError as exc:
        print(f"  ERROR: {exc}", file=sys.stderr)
        return 1
    for package in package_order:
        project_dir = ROOT / package
        project = project_dir / "_CoqProject"
        if not project.is_file():
            errors.append(f"{package}: missing _CoqProject")
            failed_packages.add(package)
            continue
        generate = subprocess.run(
            ["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
            cwd=project_dir, env=env, text=True, capture_output=True, check=False,
        )
        if generate.returncode != 0:
            detail = re.sub(r"\s+", " ", (generate.stdout + generate.stderr)[-800:]).strip()
            errors.append(f"{package}: cannot generate Makefile.coq; {detail}")
            failed_packages.add(package)
            continue
        registry_targets = sorted(
            source.relative_to(project_dir).with_suffix(".vo").as_posix()
            for source in sources_by_package.get(package, set())
        )
        # A package imported by another audited package must refresh its public
        # closure, not just a registry target that may omit the imported module.
        targets = [] if package in dependency_packages else registry_targets
        build = subprocess.run(
            ["make", "-B", "-f", "Makefile.coq", *targets],
            cwd=project_dir, env=env, text=True, capture_output=True, check=False,
        )
        if build.returncode != 0:
            detail = re.sub(r"\s+", " ", (build.stdout + build.stderr)[-800:]).strip()
            errors.append(f"{package}: registry module build failed; {detail}")
            failed_packages.add(package)

    for module, names in sorted(by_module.items()):
        namespace = module.split(".", 1)[0]
        package = NAMESPACE_PACKAGES.get(namespace)
        if package is None:
            errors.append(f"{module}: unknown namespace")
            continue
        if package in failed_packages:
            continue
        source = source_for_module(package, module)
        if not source.exists():
            errors.append(f"{module}: source file does not exist: {source.relative_to(ROOT)}")
            continue
        project = ROOT / package / "_CoqProject"
        require_prefix, _, require_leaf = module.rpartition(".")
        body = f"From {require_prefix} Require Import {require_leaf}.\n"
        body += "".join(f"Print Assumptions {name}.\n" for name in sorted(set(names)))
        with tempfile.TemporaryDirectory(prefix="library-assum-") as tmp:
            probe = Path(tmp) / f"assum_{source.stem}.v"
            probe.write_text(body)
            command = ["coqc", *include_flags(project), str(probe)]
            proc = subprocess.run(
                command,
                cwd=ROOT / package,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            output = proc.stdout + proc.stderr
            expected = len(set(names))
            closed = output.count("Closed under the global context")
            if proc.returncode != 0 or "Axioms:" in output or closed != expected:
                detail = re.sub(r"\s+", " ", output[-800:]).strip()
                errors.append(
                    f"{module}: closed={closed}/{expected}, rc={proc.returncode}; {detail}"
                )
            else:
                checked += expected

    if errors:
        for error in errors:
            print(f"  ERROR: {error}", file=sys.stderr)
        return 1
    print(
        f"library-migration assumptions gate OK: "
        f"{checked} API and compatibility theorems, {len(by_module)} modules"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
