#!/usr/bin/env python3
"""Generate the public library's source API and explicit fidelity index.

Uses the migration gate's declaration/scope parser and registry readers. This
is a source index, not a compiler symbol table or an installation certificate.
The tracked sources are read from git only when the repository root is itself a
git toplevel; an archive, or a tree nested in another checkout, is refused
rather than indexed from an enclosing repository (the O-1 rule).
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import os
from pathlib import Path
import re
import subprocess
import sys

import foundation_fidelity as FF
import library_inventory as INV
import migration_report as MR
from family_registry import RegistryError, load_library_registry, public_repository_path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "meta/LIBRARY_API.md"
KIND = re.compile(r"^(?P<modifiers>(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*)"
                  rf"(?P<kind>{MR.DECL_KEYWORDS})\s+")
# The variables that would make git read another repository than the root's own.
GIT_SELECT_ENV = ("GIT_DIR", "GIT_WORK_TREE", "GIT_COMMON_DIR", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                  "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE")


def cell(value: str) -> str:
    return value.replace("|", r"\|").replace("\n", " ")


def source_link(name: str, path: str, line: int | None = None) -> str:
    anchor = f"#L{line}" if line is not None else ""
    return f"[{name}](../{path}{anchor})"


def tracked_files(root: Path) -> list[str]:
    """The files git tracks at `root`, read only when `root` is its own git toplevel, without the variables that select
    another repository; anything else (no repository, an archive, a tree nested in another checkout) is refused."""
    env = {key: value for key, value in os.environ.items() if key not in GIT_SELECT_ENV}

    def git(*args: str) -> subprocess.CompletedProcess:
        return subprocess.run(["git", "--no-optional-locks", "--no-replace-objects", *args], cwd=root, env=env,
                              capture_output=True)

    try:
        top = git("rev-parse", "--show-toplevel")
    except FileNotFoundError as exc:
        raise ValueError("git is not available: the API index reads the tracked sources of a git checkout") from exc
    toplevel = top.stdout.decode().strip()
    if top.returncode or not toplevel or os.path.realpath(toplevel) != os.path.realpath(root):
        reason = top.stderr.decode().strip() or f"its toplevel is {toplevel}"
        raise ValueError(f"{root} is not its own git toplevel ({reason}); run the API index in a checkout of the "
                         "source, not in an archive or a tree nested in another repository")
    listed = git("ls-files", "-z")
    if listed.returncode:
        raise ValueError(f"git ls-files in {root}: {listed.stderr.decode().strip()}")
    return listed.stdout.decode().split("\0")


def public_declarations() -> tuple[dict[str, str], dict[str, dict]]:
    tracked = tracked_files(ROOT)
    modules, declarations = {}, {}
    for relative in sorted(set(tracked)):
        if not relative.endswith(".v") or not public_repository_path(relative):
            continue
        path = ROOT / relative
        if not path.is_file() or path.resolve() != path:
            raise ValueError(f"public source missing or aliased: {relative}")
        project = ROOT / relative.split("/", 1)[0] / "_CoqProject"
        if not project.is_file() or project.resolve() != project:
            raise ValueError(f"public project missing or aliased: {project.relative_to(ROOT)}")
        module = INV.project_module(relative, project.read_text())
        if module in modules:
            raise ValueError(f"duplicate public module: {module}")
        modules[module] = relative
        for decl in MR.declarations(path.read_text()):
            match = KIND.match(decl["text"])
            if match is None:
                raise ValueError(f"unrecognized declaration: {relative}:{decl['line']}")
            if "Local" in match["modifiers"].split() or match["kind"] == "Let":
                continue
            name = ".".join(filter(None, (module, decl["module"], decl["name"])))
            if name in declarations:
                raise ValueError(f"duplicate public declaration: {name}")
            declarations[name] = {"module": module, "path": relative,
                                  "line": decl["line"], "kind": match["kind"]}
    return modules, declarations


def render() -> str:
    modules, declarations = public_declarations()
    families = load_library_registry(ROOT)["primitives"]
    verdicts, errors = FF.expand_registry()
    if errors:
        raise ValueError("; ".join(errors))
    explicit = {entry["qualified_name"]: entry for entry in verdicts}
    for name, entry in explicit.items():
        if public_repository_path(entry["path"]) and name not in declarations:
            raise ValueError(f"audited public primitive has no indexed declaration: {name}")

    canonical, principal = defaultdict(list), defaultdict(list)
    for family, spec in sorted(families.items()):
        if spec["canonical_name"]:
            canonical[spec["canonical_name"]].append(family)
        for name in spec.get("api_theorems", []):
            principal[name].append(family)

    def link(name: str) -> str:
        if name in declarations:
            decl = declarations[name]
            return source_link(name, decl["path"], decl["line"])
        return f"`{name}`"

    out = ["# Graph library API index", "",
           "Generated by `python3 meta/library_api.py --write`; checked with `--check`.", "",
           f"This index covers {len(modules)} project-enrolled public source modules and "
           f"{len(declarations)} explicit declarations, plus {len(families)} registered migration families. "
           "Source links provide the full types, guards and proofs. Local declarations and Let bindings "
           "are omitted. Generated constructors, fields, instances, notations and module aliases are "
           "documented by their source; this is not an exhaustive compiler symbol table.", "",
           "A fidelity verdict applies only to an explicitly enrolled primitive. A family verdict below "
           "describes that family's canonical contract; it does not audit every declaration in the same "
           "module. Unclassified declarations remain unclassified. Principal lemmas are exactly the "
           "family registry's `api_theorems`; compatibility certificates are not public imports.", "",
           "The listing describes the intended public source surface. Independent installation, "
           "corpus-free dependency checks and assumptions gates are separate release requirements; "
           "an index entry does not establish them. Useful application results are a separate release "
           "component and are not included in this public-module index.", "",
           "## Canonical families and principal lemmas", "",
           "The status column records the migration of legacy aliases. In particular, `deprecated` "
           "does not deprecate the canonical public API. Upstream endpoints have no repository source link.", "",
           "| Family | Owner / module | Canonical declaration | Family fidelity | Alias migration status | Principal lemmas |",
           "|---|---|---|---|---|---|"]
    for family, spec in sorted(families.items()):
        name = spec["canonical_name"]
        owner = spec["owner"] + (" / " + name.rsplit(".", 1)[0] if name else "")
        lemmas = "<br>".join(link(name) for name in spec.get("api_theorems", [])) or "None registered"
        values = [f"[{family}](library_primitives/{family}.json)", owner,
                  link(name) if name else "Pending", spec["fidelity"], spec["status"], lemmas]
        out.append("| " + " | ".join(map(cell, values)) + " |")

    out.extend(["", "## Modules and declarations", ""])
    for module, relative in sorted(modules.items()):
        out.extend([f"### {module}", "", f"Source: {source_link(relative, relative)}.", "",
                    "| Declaration | Kind | Explicit primitive fidelity | Registry roles |",
                    "|---|---|---|---|"])
        for name, decl in sorted(declarations.items(), key=lambda item: (item[1]["line"], item[0])):
            if decl["module"] != module:
                continue
            roles = ["Canonical: " + f for f in canonical[name]] + ["Principal lemma: " + f for f in principal[name]]
            entry = explicit.get(name)
            verdict = (entry["verdict"] + ": " + entry["note"]) if entry else "Unclassified"
            out.append("| " + " | ".join(map(cell, [link(name), decl["kind"], verdict,
                                                     "; ".join(roles) or "—"])) + " |")
        out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        text = render()
        if args.write:
            OUTPUT.write_text(text)
            print(f"wrote {OUTPUT.relative_to(ROOT)}")
        elif not OUTPUT.is_file() or OUTPUT.read_text() != text:
            print("meta/LIBRARY_API.md is missing or stale; run python3 meta/library_api.py --write", file=sys.stderr)
            return 1
        else:
            print("library API index is current")
    except (OSError, ValueError, RegistryError, subprocess.CalledProcessError) as exc:
        print(f"library API index: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
