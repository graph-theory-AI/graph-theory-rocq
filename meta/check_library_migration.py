#!/usr/bin/env python3
"""Axiom-audit public library APIs and migration compatibility certificates.

Fresh pinned coqdep output determines the full local source closure of every
registered module. Every required .vo is rebuilt through its owning project's
generated Makefile with -B; unrelated source targets are excluded. Load snippets
remain source inputs of their forced parents. Project/compiler overrides whose
dependencies or output modes coqdep cannot represent are rejected, as are
unowned sources and external prerequisites outside the selected toolchain.
"""

from __future__ import annotations

import os
import re
import shlex
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

import rocq_toolchain as ROCQ
from family_registry import RegistryError, load_library_registry


ROOT = Path(__file__).resolve().parents[1]

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


class BuildError(ValueError):
    pass


def run_build_tool(command: list[str], directory: Path, env: dict[str, str], *,
                   reject_warnings: bool = False) -> str:
    try:
        proc = subprocess.run(command, cwd=directory, env=build_environment(env), text=True,
                              capture_output=True, check=False)
    except OSError as exc:
        raise BuildError(f"cannot execute {command[0]}: {exc}") from exc
    # Pinned OCaml's verbose-GC exit counters are runtime instrumentation,
    # not unresolved-import warnings. Preserve them for compile diagnostics.
    diagnostics = re.sub(
        r"(?m)^(?:allocated_words|minor_words|promoted_words|major_words|"
        r"minor_collections|major_collections|forced_major_collections|"
        r"heap_words|top_heap_words): [0-9]+\r?$", "", proc.stderr)
    if proc.returncode or (reject_warnings and diagnostics.strip()):
        detail = re.sub(r"\s+", " ", (proc.stdout + proc.stderr)[-1600:]).strip()
        raise BuildError(f"{directory.name}: {' '.join(command)} failed; {detail}")
    return proc.stdout


def build_environment(env: dict[str, str]) -> dict[str, str]:
    """Keep the selected toolchain, never inherited Make/compiler overrides.

    MAKEFLAGS=-n/-t and environment variables such as ROCQ, COQFLAGS or TIMER
    can leave a stale clean .vo while make returns success. An allowlist also
    prevents less obvious generated-Makefile variables from doing the same.
    Keep explicit numeric parallelism; inherited jobserver descriptors are not
    available to our subprocesses and all other make options are discarded.
    """
    permitted = {
        "PATH", "HOME", "USER", "LOGNAME", "TMPDIR", "TMP", "TEMP", "TZ",
        "LANG", "LANGUAGE", "TERM", "OPAMROOT", "OPAM_SWITCH_PREFIX",
        "ROCQ_OPAM_SWITCH", "CAML_LD_LIBRARY_PATH", "OCAMLPATH", "OCAMLFIND_CONF",
        "LD_LIBRARY_PATH", "OCAMLRUNPARAM", "OCAML_GC_STATS",
    }
    clean = {key: value for key, value in env.items()
             if key in permitted or key.startswith("LC_")}
    try:
        options = shlex.split(env.get("MAKEFLAGS", ""))
    except ValueError:
        options = []
    jobs = None
    for i, option in enumerate(options):
        if re.fullmatch(r"-j[1-9][0-9]*|--jobs=[1-9][0-9]*", option):
            jobs = option.removeprefix("-j").removeprefix("--jobs=")
        elif option in {"-j", "--jobs"} and i + 1 < len(options):
            if re.fullmatch(r"[1-9][0-9]*", options[i + 1]):
                jobs = options[i + 1]
    if jobs:
        clean["MAKEFLAGS"] = f"-j{jobs}"
    return clean


def make_words(text: str) -> list[str]:
    """Decode coqdep's escaped Make filenames, not shell-quoted strings."""
    words, word = [], []
    i = 0
    while i < len(text):
        char = text[i]
        if char == "\\":
            i += 1
            if i == len(text):
                raise BuildError("trailing escape in dependency output")
            word.append(text[i])
        elif char == "$":
            if text[i:i + 2] != "$$":
                raise BuildError("unsupported Make variable in dependency output")
            word.append("$")
            i += 1
        elif char.isspace():
            if word:
                words.append("".join(word))
                word = []
        else:
            word.append(char)
        i += 1
    if word:
        words.append("".join(word))
    return words


def dependency_rules(output: str) -> dict[str, set[str]]:
    """Read fresh multi-target coqdep rules, including Load .v prerequisites."""
    rules = {}
    for line in re.sub(r"\\\r?\n", " ", output).splitlines():
        if not line.strip():
            continue
        separator = None
        i = 0
        while i < len(line):
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == ":":
                separator = i
                break
            i += 1
        if separator is None:
            raise BuildError(f"malformed dependency rule: {line}")
        targets = make_words(line[:separator])
        prerequisites = set(make_words(line[separator + 1:]))
        for target in targets:
            if target.endswith(".vo"):
                if target in rules:
                    raise BuildError(f"duplicate dependency target: {target}")
                rules[target] = prerequisites
    return rules


def validate_project_options(project: Path) -> None:
    """Reject hidden imports/resolution or output modes that coqdep cannot model."""
    unsupported = {
        "-load-vernac-source", "-l", "-load-vernac-source-verbose", "-lv",
        "-require", "-require-import", "-ri", "-require-export", "-re",
        "-require-from", "-rfrom", "-require-import-from", "-rifrom",
        "-require-export-from", "-refrom", "-load-vernac-object", "-compat-from",
        "-init-file", "-compat", "-R", "-Q", "-I", "-include", "-coqlib", "-exclude-dir",
        "-boot", "-noinit", "-nois", "-vos", "-vok", "-o", "-top", "-topfile",
        "-where", "-config", "--config", "-v", "--version", "-print-version",
        "-list-tags", "-h", "-help", "--help",
    }
    tokens = shlex.split(project.read_text(), comments=True)
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token == "-arg":
            if i + 1 == len(tokens):
                raise BuildError(f"{project}: missing -arg value")
            for flag in shlex.split(tokens[i + 1]):
                if flag in unsupported:
                    raise BuildError(f"{project}: unsupported compiler flag {flag} for source-closure builds")
            i += 2
        elif token in {"-R", "-Q"}:
            i += 3
        elif token in {"-I", "-docroot", "-generate-meta-for-package"}:
            i += 2
        elif token in {"-f", "-coqlib"} or "=" in token:
            # Nested/custom Make configuration needs an explicit dependency
            # model before it can override the project parsed by this gate.
            raise BuildError(f"{project}: unsupported project override {token}")
        else:
            i += 1


def source_build_plan(roots: set[Path], env: dict[str, str]) -> list[tuple[str, set[Path]]]:
    """Fresh concrete source closure; neither stale .d files nor mtimes are inputs."""
    root = ROOT.resolve()
    library = run_build_tool(["rocq", "compile", "-where"], root, env,
                             reject_warnings=True).strip()
    if not library or not Path(library).is_dir():
        raise BuildError("cannot locate the pinned Rocq library directory")
    pinned_libraries = Path(library).resolve().parent
    projects = {path.parent.name: path.parent for path in sorted(root.glob("*/_CoqProject"))}
    owners: dict[Path, str] = {}
    for package, directory in projects.items():
        validate_project_options(directory / "_CoqProject")
        for custom in ("Makefile.coq.local", "Makefile.coq.local-late"):
            if (directory / custom).exists():
                raise BuildError(f"{package}: custom {custom} is not supported by source-closure builds")
        # Ask the same project parser as the generated Makefile; -arg values
        # must never be mistaken for project source filenames.
        sources = run_build_tool(["rocq", "makefile", "-sources-of", "-f", "_CoqProject"],
                                 directory, env, reject_warnings=True)
        for name in shlex.split(sources):
            if not name.endswith(".v"):
                continue
            source = (directory / name).resolve()
            if not source.is_relative_to(directory) or not source.is_file():
                raise BuildError(f"{package}: missing or non-owned project source: {name}")
            if source in owners:
                raise BuildError(f"ambiguous project ownership: {source}")
            owners[source] = package

    graphs: dict[str, dict[Path, set[Path]]] = {}
    required: dict[str, set[Path]] = defaultdict(set)
    package_dependencies: dict[str, set[str]] = defaultdict(set)
    visiting: set[Path] = set()
    visited: set[Path] = set()

    def concrete_path(directory: Path, name: str) -> Path:
        declared = Path(os.path.abspath(directory / name))
        resolved = (directory / name).resolve()
        if declared.is_relative_to(root):
            # A stale local object may alias an installed object with the right
            # logical name. Resolving it first would hide its owned source from
            # the closure. This also rejects symlinked containing directories.
            if declared.suffix == ".vo" and declared != resolved:
                raise BuildError(f"local object alias is not supported: {declared}")
        elif not declared.is_relative_to(pinned_libraries):
            # An external alias into the pinned installation is not itself a
            # pinned dependency; validate its declared origin before resolving.
            raise BuildError(f"non-pinned external dependency: {declared}")
        return resolved

    def visit(source: Path) -> None:
        source = source.resolve()
        if source in visiting:
            raise BuildError(f"source dependency cycle: {source}")
        if source in visited:
            return
        package = owners.get(source)
        if package is None:
            raise BuildError(f"required source is missing or absent from its _CoqProject: {source}")
        directory = projects[package]
        if package not in graphs:
            # Full project load paths and parsing order match make's coqdep.
            # A missing module can be only a warning with rc=0: fail closed.
            output = run_build_tool(["rocq", "dep", "-f", "_CoqProject"], directory,
                                    env, reject_warnings=True)
            graph = {}
            for target, dependencies in dependency_rules(output).items():
                target_source = concrete_path(directory, target).with_suffix(".v")
                if target_source in graph:
                    raise BuildError(f"ambiguous normalized dependency target: {target}")
                graph[target_source] = {concrete_path(directory, dep) for dep in dependencies}
            graphs[package] = graph
        dependencies = graphs[package].get(source)
        if dependencies is None or source not in dependencies:
            raise BuildError(f"missing source dependency rule: {source}")
        visiting.add(source)
        required[package].add(source)
        for dependency in sorted(dependencies):
            if dependency == source:
                continue
            local = dependency.is_relative_to(root)
            if dependency.suffix == ".vo" and local:
                dep_source = dependency.with_suffix(".v")
                visit(dep_source)
                dep_owner = owners[dep_source]
                if dep_owner != package:
                    package_dependencies[package].add(dep_owner)
            elif dependency.suffix == ".v" and local:
                # Load snippets need not be standalone project targets. coqdep
                # adds their Require edges to the parent rule; the forced
                # parent rereads the snippet, even with a preserved timestamp.
                relative = dependency.relative_to(root)
                if (not dependency.is_file() or not relative.parts
                        or relative.parts[0] not in projects):
                    raise BuildError(f"missing or non-owned Load source: {dependency}")
            elif local or not dependency.is_file():
                raise BuildError(f"unsupported or missing dependency: {dependency}")
            elif not dependency.is_relative_to(pinned_libraries):
                raise BuildError(f"non-pinned external dependency: {dependency}")
            # Only the selected toolchain's installed libraries/runtime are
            # external; mutable sibling checkouts must never lend stale objects.
        visiting.remove(source)
        visited.add(source)

    for source in sorted(roots):
        visit(source)

    order, active, done = [], set(), set()

    def order_package(package: str) -> None:
        if package in active:
            raise BuildError(f"package dependency cycle: {package}")
        if package in done:
            return
        active.add(package)
        for dependency in sorted(package_dependencies[package]):
            order_package(dependency)
        active.remove(package)
        done.add(package)
        order.append((package, required[package]))

    for package in sorted(required):
        order_package(package)
    return order


def build_registry_sources(roots: set[Path], env: dict[str, str]) -> list[tuple[str, set[Path]]]:
    plan = source_build_plan(roots, env)
    for package, sources in plan:
        directory = ROOT / package
        targets = sorted(source.relative_to(directory).with_suffix(".vo").as_posix()
                         for source in sources)
        if not targets:
            raise BuildError(f"{package}: refusing an empty-target build")
        run_build_tool(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
                       directory, env)
        # Force EVERY local transitive source, including unregistered helpers.
        # Generated project rules preserve compiler flags and refresh .d files.
        run_build_tool(["make", "-B", "-f", "Makefile.coq", *targets], directory, env)
    return plan


def main() -> int:
    try:
        data = load_library_registry(ROOT)
    except RegistryError as exc:
        print(f"  ERROR: {exc}", file=sys.stderr)
        return 1
    by_module: dict[str, list[str]] = defaultdict(list)
    for spec in data["primitives"].values():
        if spec.get("status") not in {"canonical", "migrating", "deprecated", "complete"}:
            continue
        for name in spec.get("api_theorems", []) + spec.get("compatibility_theorems", []):
            module, _, _ = name.rpartition(".")
            by_module[module].append(name)

    errors: list[str] = []
    checked = 0
    env = build_environment(ROCQ.environment())
    sources_by_package: dict[str, set[Path]] = defaultdict(set)
    for module in by_module:
        namespace = module.split(".", 1)[0]
        package = NAMESPACE_PACKAGES.get(namespace)
        if package is not None:
            sources_by_package[package].add(source_for_module(package, module))

    try:
        plan = build_registry_sources(set().union(*sources_by_package.values()), env)
    except (BuildError, OSError, ValueError) as exc:
        print(f"  ERROR: {exc}", file=sys.stderr)
        return 1
    print(f"library-migration build: {sum(len(sources) for _, sources in plan)} "
          f"local source targets across {len(plan)} packages")

    for module, names in sorted(by_module.items()):
        namespace = module.split(".", 1)[0]
        package = NAMESPACE_PACKAGES.get(namespace)
        if package is None:
            errors.append(f"{module}: unknown namespace")
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
