#!/usr/bin/env python3
"""Stage one public library package, without corpus sources or cached objects.

The source classifier and project/namespace checks are the same readers used
by the migration gates. rocq makefile does the build; opam installs an explicit
list of public .v/.vo/.glob files. No sibling source load path is staged.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shlex
import shutil

import check_library_migration as G
import library_inventory as INV
from family_registry import public_repository_path

ROOT = Path(__file__).resolve().parents[1]

# Explicit opam names: repository package directory -> rocq-graph-theory-<suffix>.
# hamiltonicity-theory and homomorphism-theory have no public layer yet, so no package.
PACKAGES = {
    "base": "base", "classical-lemmas": "classical-lemmas",
    "topological-graph-theory": "topological", "minor-theory": "minor",
    "chromatic-theory": "chromatic", "cycle-theory": "cycle", "packing-theory": "packing",
    "reconstruction-theory": "reconstruction", "hypergraph-theory": "hypergraph",
    "graph-theory-misc": "misc", "spectral-graph-theory": "spectral",
    "extremal-graph-theory": "extremal", "infinite-graph-theory": "infinite",
    "digraph-theory": "digraph", "atlas": "atlas",
}


def prepare(package: str) -> None:
    projects = {p.parent.name: p for p in ROOT.glob("*/_CoqProject")}
    if package not in projects:
        raise ValueError(f"unknown package: {package}")
    project = projects[package]
    if project.resolve() != project or not project.is_file():
        raise ValueError(f"missing or aliased project: {project}")
    G.validate_project_options(project)
    content = project.read_text()
    tokens = shlex.split(content, comments=True)
    sources = sorted(p for p in project.parent.rglob("*.v")
                     if public_repository_path(p.relative_to(ROOT).as_posix()))
    if not sources:
        raise ValueError(f"{package}: no public foundation layer to package")
    modules = {}
    for source in sources:
        if source.resolve() != source or not source.is_file():
            raise ValueError(f"missing or aliased public source: {source}")
        relative = source.relative_to(ROOT).as_posix()
        module = INV.project_module(relative, content)
        if module in modules:
            raise ValueError(f"duplicate public module: {module}")
        modules[module] = source
    namespaces = {m.split(".")[0] for m in modules}
    if len(namespaces) != 1:
        raise ValueError(f"{package}: ambiguous namespace: {namespaces}")
    namespace = namespaces.pop()
    args = []
    for index, token in enumerate(tokens):
        if token == "-arg":
            args.extend(["-arg", tokens[index + 1]])
    stage = ROOT / "_build" / "library" / package
    if package not in PACKAGES:
        raise ValueError(f"{package}: public modules but no supported package name")
    name = "rocq-graph-theory-" + PACKAGES[package]
    manifest = ROOT / (name + ".install")
    if (stage.resolve() != stage or stage.exists()
            or manifest.resolve() != manifest or manifest.exists()):
        raise ValueError(f"refusing to overwrite or follow aliases: {stage}, {manifest}")
    stage.mkdir(parents=True)
    project_lines = [f"-R theories {namespace}", shlex.join(args)]
    install_lines = ['opam-version: "2.0"', "lib_root: ["]
    for module, source in sorted(modules.items()):
        relative = source.relative_to(project.parent)
        target = stage / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        project_lines.append(relative.as_posix())
        for extension in (".v", ".vo", ".glob"):
            artifact = target.with_suffix(extension).relative_to(ROOT).as_posix()
            destination = "coq/user-contrib/" + module.replace(".", "/") + extension
            install_lines.append(f"  {json.dumps(artifact)} {{{json.dumps(destination)}}}")
    install_lines.append("]")
    (stage / "_CoqProject").write_text("\n".join(project_lines) + "\n")
    manifest.write_text("\n".join(install_lines) + "\n")
    print(f"STAGED {name}: {len(modules)} public modules in {stage}")
    print(f"INSTALL MANIFEST {manifest}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", help="repository package directory, e.g. base")
    options = parser.parse_args()
    try:
        prepare(options.package)
    except (ValueError, OSError, G.BuildError) as exc:
        parser.exit(1, f"library package: {exc}\n")
