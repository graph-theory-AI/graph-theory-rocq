#!/usr/bin/env python3
"""The public-library install gate (G-6) and the opam metadata lint (G-8).

`make install-gate` checks that the public library installs, and serves a downstream client,
exactly as packaged:

1. lint (G-8): `opam lint` passes with no warning on every opam/*.opam file; the three
   old-location copies are byte-equal to their opam/ wrappers; every file keeps the metadata
   contract below; each canonical package's internal depends are exactly the repository
   packages its public modules import; every external pin equals the installed toolchain.
2. copy: a fresh inclusion-only copy of the packaging inputs: the readers library_package.py
   imports, opam/, the packages' _CoqProject files and the public sources. No conjecture,
   migration, application, example, grounding or implication file and no JSON is copied.
3. build + install: in internal-dependency order, each package's own opam build: commands,
   parsed from its file with %{jobs}% expanded to --jobs, run in the copy with ROCQPATH = the
   prefix only; then `opam-installer --prefix` into a FRESH PRIVATE PREFIX. Each manifest
   installs exactly its package's public modules (.v/.vo/.glob, byte-equal), and after the
   last package the prefix holds exactly the manifests' files.
4. downstream: every theories/examples/ source, copied flat outside the copy, compiles with
   ROCQPATH = the prefix only; `Locate Library` names a prefix file for every repository
   module they import; then a planted client importing a non-public module must FAIL with an
   error naming that module.
5. receipt: OUT/install-gate.json, OUT/inputs.sha256 and OUT/logs/.

The metadata contract (comments are never read). Fields: opam-version, synopsis,
description, maintainer, authors, license, homepage, bug-reports, dev-repo, depends, build,
pin-depends. A canonical file's build: is exactly four commands: the Python version guard;
`python3 -B meta/library_package.py <dir>`; `rocq makefile` in _build/library/<dir>;
`make -C _build/library/<dir> -f Makefile.coq -j%{jobs}%`. %{jobs}% is the only variable and
no command or argument carries a filter. depends constraints are `{= version}` (internal),
`{= "<v>"}` (external), `{build}` (conf-python-3 only); coq-graph-theory is `{= "dev"}` with
a pin-depends on the image's commit of record (environment/rocq92/pins.tsv). A wrapper has
no build: and depends only on its canonical package `{= version}`. External pins are compared
by VERSION with the installed toolchain only; that every external a public module needs is
declared is measured elsewhere (the E-2 ext_scan table, the Mac's fresh-OPAMROOT receipt).

The source identity is DECLARED by the caller (--source-commit / --source-tree: the ids the
D-5 kit binds). The gate never reads git. It records the sha256 of every input it reads
(OUT/inputs.sha256: the copied files, the example sources, the metadata it checks and this
file); with --tree-sha256 each must equal its row in the caller's manifest of the tree.

Exit 0 PASS, 1 FAIL, 2 REFUSED (arguments or preconditions). --lint-only runs step 1 alone
(`make opam-lint`) and needs neither --out nor the source ids.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

META = Path(__file__).resolve().parent
ROOT = META.parent
if str(META) not in sys.path:
    sys.path.insert(0, str(META))

import check_library_migration as CLM  # noqa: E402
import library_inventory as INV  # noqa: E402
import library_package as PKG  # noqa: E402
from family_registry import public_repository_path  # noqa: E402

# The readers library_package.py imports (corpus_registry through library_inventory).
READERS = ("library_package.py", "check_library_migration.py", "library_inventory.py",
           "family_registry.py", "rocq_toolchain.py", "corpus_registry.py")
EXCLUDED_DIRS = frozenset({"conjectures", "migration", "applications", "examples"})
EXCLUDED_STEMS = ("grounding", "implications")
CANONICAL_PREFIX = "rocq-graph-theory-"
WRAPPERS = {"coq-graph-theory-base": "rocq-graph-theory-base",
            "coq-digraph-theory": "rocq-graph-theory-digraph",
            "rocq-digraph-theory": "rocq-graph-theory-digraph"}
LEGACY_COPIES = {"base/coq-graph-theory-base.opam": "opam/coq-graph-theory-base.opam",
                 "digraph-theory/coq-digraph-theory.opam": "opam/coq-digraph-theory.opam",
                 "digraph-theory/rocq-digraph-theory.opam": "opam/rocq-digraph-theory.opam"}
FIELDS = frozenset({"opam-version", "synopsis", "description", "maintainer", "authors", "license",
                    "homepage", "bug-reports", "dev-repo", "depends", "build", "pin-depends"})
GUARD = ("import sys; sys.exit(0 if sys.version_info >= (3, 9) else "
         "'rocq-graph-theory packaging needs Python >= 3.9 at build time')")
JOBS_ARG = "-j%{jobs}%"
BUILD_ONLY = "conf-python-3"
GRAPH_THEORY = "coq-graph-theory"
GRAPH_THEORY_PIN = "coq-graph-theory.dev"
GRAPH_THEORY_URL = "git+https://github.com/rocq-community/graph-theory.git#"
PINS = "environment/rocq92/pins.tsv"
NEG_SOURCE = "base/theories/migration/edge_count.v"
NEG_NAME = "migration.edge_count"
NEG_CLIENT = "neg__nonpublic.v"
NEG_TEXT = "From GTBase Require Import migration.edge_count.\n"
LOCATE_PROBE = "locate__probe.v"
HEX40 = re.compile(r"[0-9a-f]{40}")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
OPAM_LIST = ["opam", "list", "--readonly", "--installed", "--columns=name,version", "--short", "--color=never"]


class Refused(Exception):
    """An argument or precondition the gate does not run with (exit 2)."""


class OpamSyntax(ValueError):
    """Text outside the subset of the opam format the gate reads."""


# ── the opam format subset ──

_SINGLE = "[]{}():"
_OPERATORS = ("!=", "<=", ">=", "=", "<", ">", "&", "|", "!", "?")
_ESCAPES = {"n": "\n", "t": "\t", "r": "\r", "b": "\b", '"': '"', "\\": "\\"}
_WORD = re.compile(r"[A-Za-z0-9_+\-.~/%@]+")


def _string(text: str, i: int) -> tuple[str, int]:
    out, n = [], len(text)
    while i < n:
        c = text[i]
        if c == '"':
            return "".join(out), i + 1
        if c == "\\":
            if i + 1 >= n:
                break
            nxt = text[i + 1]
            if nxt in _ESCAPES:
                out.append(_ESCAPES[nxt])
                i += 2
            elif nxt == "\n":
                i += 2
                while i < n and text[i] in " \t":
                    i += 1
            else:
                raise OpamSyntax(f"unsupported escape \\{nxt}")
            continue
        out.append(c)
        i += 1
    raise OpamSyntax("unterminated string")


def opam_tokens(text: str) -> list[tuple[str, str]]:
    """("str", s), ("ident", s), ("punct", c) and ("op", o) tokens; comments are dropped."""
    tokens: list[tuple[str, str]] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == "#":
            end = text.find("\n", i)
            i = n if end < 0 else end + 1
        elif text.startswith("(*", i):
            end = text.find("*)", i + 2)
            if end < 0:
                raise OpamSyntax("unterminated comment")
            i = end + 2
        elif text.startswith('"""', i):
            end = text.find('"""', i + 3)
            if end < 0:
                raise OpamSyntax("unterminated triple-quoted string")
            tokens.append(("str", text[i + 3:end]))
            i = end + 3
        elif c == '"':
            value, i = _string(text, i + 1)
            tokens.append(("str", value))
        elif c in _SINGLE:
            tokens.append(("punct", c))
            i += 1
        else:
            for op in _OPERATORS:
                if text.startswith(op, i):
                    tokens.append(("op", op))
                    i += len(op)
                    break
            else:
                match = _WORD.match(text, i)
                if not match:
                    raise OpamSyntax(f"unexpected character {c!r} at offset {i}")
                tokens.append(("ident", match.group()))
                i = match.end()
    return tokens


def _value(tokens: list[tuple[str, str]], i: int) -> tuple[tuple, int]:
    if i >= len(tokens):
        raise OpamSyntax("missing value")
    token = tokens[i]
    if token == ("punct", "["):
        items, i = [], i + 1
        while i < len(tokens) and tokens[i] != ("punct", "]"):
            item, i = _value(tokens, i)
            items.append(item)
        if i >= len(tokens):
            raise OpamSyntax("unterminated list")
        node, i = ("list", items), i + 1
    elif token[0] in ("str", "ident"):
        node, i = token, i + 1
    else:
        raise OpamSyntax(f"unexpected {token[1]!r}")
    if i < len(tokens) and tokens[i] == ("punct", "{"):
        depth, j = 1, i + 1
        while j < len(tokens) and depth:
            if tokens[j] == ("punct", "{"):
                depth += 1
            elif tokens[j] == ("punct", "}"):
                depth -= 1
            j += 1
        if depth:
            raise OpamSyntax("unterminated filter")
        node, i = ("opt", node, tuple(tokens[i + 1:j - 1])), j
    return node, i


def parse_opam(text: str) -> dict[str, tuple]:
    """Top-level fields as nodes: ("str", s), ("ident", s), ("list", [nodes]) and
    ("opt", node, filter tokens). Sections, groups and formulas are refused."""
    tokens = opam_tokens(text)
    fields: dict[str, tuple] = {}
    i = 0
    while i < len(tokens):
        if tokens[i][0] != "ident" or i + 1 >= len(tokens) or tokens[i + 1] != ("punct", ":"):
            raise OpamSyntax(f"expected a field, got {tokens[i][1]!r}")
        name = tokens[i][1]
        if name in fields:
            raise OpamSyntax(f"duplicate field {name}")
        fields[name], i = _value(tokens, i + 2)
    return fields


def strings_in(node: tuple) -> list[str]:
    if node[0] == "str":
        return [node[1]]
    if node[0] == "list":
        return [s for item in node[1] for s in strings_in(item)]
    if node[0] == "opt":
        return strings_in(node[1]) + [t[1] for t in node[2] if t[0] == "str"]
    return []


def has_option(node: tuple) -> bool:
    if node[0] == "opt":
        return True
    return node[0] == "list" and any(has_option(item) for item in node[1])


# ── the metadata contract ──

def expected_build(directory: str) -> tuple:
    stage = f"_build/library/{directory}"

    def command(*atoms: str | tuple) -> tuple:
        return ("list", [atom if isinstance(atom, tuple) else ("str", atom) for atom in atoms])

    return ("list", [
        command("python3", "-c", GUARD),
        command("python3", "-B", "meta/library_package.py", directory),
        command("sh", "-c", f"cd {stage} && rocq makefile -f _CoqProject -o Makefile.coq"),
        command(("ident", "make"), "-C", stage, "-f", "Makefile.coq", JOBS_ARG),
    ])


def expand(build: tuple, jobs: int) -> list[list[str]]:
    """The build: commands as argv lists, with %{jobs}% replaced by the explicit value."""
    return [[f"-j{jobs}" if atom[1] == JOBS_ARG else atom[1] for atom in command[1]] for command in build[1]]


def field_problems(name: str, fields: dict[str, tuple]) -> list[str]:
    problems = [f"{name}: unknown field {field}" for field in sorted(set(fields) - FIELDS)]
    if fields.get("opam-version") != ("str", "2.0"):
        problems.append(f"{name}: opam-version is not \"2.0\"")
    problems += [f"{name}: {field}: carries a filter or constraint"
                 for field, node in sorted(fields.items()) if field != "depends" and has_option(node)]
    variables = [s for node in fields.values() for s in strings_in(node) if "%{" in s]
    allowed = [JOBS_ARG] if "build" in fields else []
    if variables != allowed:
        problems.append(f"{name}: opam variables {variables}; allowed: {allowed}")
    return problems


def depends_of(name: str, fields: dict[str, tuple]) -> tuple[list[tuple[str, str, str | None]], list[str]]:
    """(package, kind, value) per depends entry; kind: version (= version), eq (= "v"), build, none."""
    node = fields.get("depends")
    if node is None or node[0] != "list":
        return [], [f"{name}: depends: is missing or not a list"]
    entries, problems = [], []
    for item in node[1]:
        constraint: tuple = ()
        if item[0] == "opt":
            item, constraint = item[1], item[2]
        if item[0] != "str":
            problems.append(f"{name}: depends entry {item[1]!r} is not a package name")
        elif constraint == ():
            entries.append((item[1], "none", None))
        elif constraint == (("op", "="), ("ident", "version")):
            entries.append((item[1], "version", None))
        elif len(constraint) == 2 and constraint[0] == ("op", "=") and constraint[1][0] == "str":
            entries.append((item[1], "eq", constraint[1][1]))
        elif constraint == (("ident", "build"),):
            entries.append((item[1], "build", None))
        else:
            problems.append(f"{name}: depends {item[1]} has the unsupported constraint "
                            f"{' '.join(t[1] for t in constraint)}")
    names = [package for package, _, _ in entries]
    problems += [f"{name}: depends lists {p} twice" for p in sorted(set(names)) if names.count(p) > 1]
    return entries, problems


def pin_depends_commit(name: str, fields: dict[str, tuple]) -> tuple[str | None, list[str]]:
    node = fields.get("pin-depends")
    if node is None:
        return None, []
    wrong = [f"{name}: pin-depends is not the single "
             f"[\"{GRAPH_THEORY_PIN}\" \"{GRAPH_THEORY_URL}<40-hex commit>\"] entry"]
    if node[0] != "list" or len(node[1]) != 1 or node[1][0][0] != "list":
        return None, wrong
    atoms = node[1][0][1]
    if [atom[0] for atom in atoms] != ["str", "str"]:
        return None, wrong
    pin, url = atoms[0][1], atoms[1][1]
    commit = url[len(GRAPH_THEORY_URL):] if url.startswith(GRAPH_THEORY_URL) else ""
    if pin != GRAPH_THEORY_PIN or not HEX40.fullmatch(commit):
        return None, wrong
    return commit, []


def canonical_problems(name: str, fields: dict[str, tuple], directory: str,
                       entries: list[tuple[str, str, str | None]]) -> list[str]:
    problems = field_problems(name, fields)
    if fields.get("build") != expected_build(directory):
        problems.append(f"{name}: build: is not the 4-command contract for {directory}")
    for package, kind, _ in entries:
        if package.startswith(CANONICAL_PREFIX):
            if kind != "version":
                problems.append(f"{name}: internal {package} must be {{= version}}")
        elif package == BUILD_ONLY:
            if kind != "build":
                problems.append(f"{name}: {BUILD_ONLY} must be {{build}}")
        elif kind != "eq":
            problems.append(f"{name}: external {package} must be an exact pin {{= \"<version>\"}}")
    return problems


def wrapper_problems(name: str, fields: dict[str, tuple], entries: list[tuple[str, str, str | None]]) -> list[str]:
    problems = field_problems(name, fields)
    if "build" in fields:
        problems.append(f"{name}: a wrapper has no build:")
    if entries != [(WRAPPERS[name], "version", None)]:
        problems.append(f"{name}: depends must be exactly \"{WRAPPERS[name]}\" {{= version}}")
    return problems


def lint_output_problems(path: str, rc: int, output: str) -> list[str]:
    """opam lint must exit 0 and print one line, '<path>: Passed.' (no warning)."""
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if rc != 0 or len(lines) != 1 or not lines[0].endswith(": Passed."):
        return [f"{path}: opam lint rc {rc}: {' | '.join(lines) or '(no output)'}"]
    return []


def graph_theory_commit(root: Path) -> str | None:
    """The commit of record of the image's coq-graph-theory dev (pins.tsv's path-pin row)."""
    path = root / PINS
    if not path.is_file():
        return None
    for line in path.read_text(encoding="utf-8").splitlines():
        columns = line.split("\t")
        if len(columns) >= 4 and columns[0] == "path-pin" and columns[1] == GRAPH_THEORY:
            match = re.search(r"commit ([0-9a-f]{40}) tree [0-9a-f]{40}", columns[3])
            return match.group(1) if match else None
    return None


def pin_problems(files: dict[str, dict], installed: dict[str, str], commit: str | None) -> list[str]:
    """Every external pin equals the installed toolchain; coq-graph-theory is dev at the commit of record."""
    problems = []
    for name, info in sorted(files.items()):
        externals = [(p, k, v) for p, k, v in info["depends"]
                     if not p.startswith(CANONICAL_PREFIX) and p != BUILD_ONLY]
        pinned = info["pin"]
        needs_pin = any(p == GRAPH_THEORY for p, _, _ in externals)
        if pinned is not None or needs_pin:
            if pinned is None:
                problems.append(f"{name}: {GRAPH_THEORY} is not released for this toolchain; pin-depends is required")
            elif commit is None:
                problems.append(f"{name}: no {GRAPH_THEORY} commit of record in {PINS}")
            elif pinned != commit:
                problems.append(f"{name}: pin-depends commit {pinned} != the image's {commit} ({PINS})")
            if pinned is not None and not needs_pin and name not in WRAPPERS:
                problems.append(f"{name}: pin-depends without a {GRAPH_THEORY} dependency")
        for package, kind, value in externals:
            have = installed.get(package)
            if package == GRAPH_THEORY:
                if (kind, value) != ("eq", "dev") or have != "dev":
                    problems.append(f"{name}: {GRAPH_THEORY} {{= {value!r}}}; must be {{= \"dev\"}} "
                                    f"(installed: {have})")
            elif kind != "eq" or value != have:
                problems.append(f"{name}: {package} {{= {value!r}}} but the installed toolchain has {have}")
    return problems


# ── the import table ──

SENTENCE_END = re.compile(r"\.(?=\s|$)")
REQUIRE = re.compile(r"(?:From\s+(\S+)\s+)?Require(?:\s+(?:Import|Export))?\s+(.+)", re.S)


def strip_comments(text: str) -> str:
    """Coq source without its (nested) comments; strings outside comments are kept."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("*)", i):
            depth, i = depth - 1, i + 2
            if not depth:
                out.append(" ")
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if text.startswith('""', j):
                        j += 2
                        continue
                    break
                j += 1
            if not depth:
                out.append(text[i:j + 1])
            i = j + 1
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def required_modules(source: str) -> list[tuple[str | None, str]]:
    """(From prefix, name) for every Require of a Coq source."""
    found = []
    for sentence in SENTENCE_END.split(strip_comments(source)):
        # Collapse AND trim: a leading blank would hide a Require that is the first sentence.
        sentence = " ".join(sentence.split())
        match = REQUIRE.fullmatch(sentence)
        if match:
            names = re.sub(r"\([^)]*\)", " ", match.group(2)).split()
            found += [(match.group(1), name) for name in names if name != "-"]
    return found


class SourceTree:
    """The repository's Coq modules (logical name -> repository path) under <dir>/theories."""

    def __init__(self, root: Path, namespaces: dict[str, str]):
        self.root = root
        self.namespaces = {d: ns for d, ns in sorted(namespaces.items()) if (root / d / "theories").is_dir()}
        owners: dict[str, list[str]] = {}
        for directory, namespace in self.namespaces.items():
            owners.setdefault(namespace, []).append(directory)
        shared = {ns: ds for ns, ds in owners.items() if len(ds) > 1}
        if shared:
            raise Refused(f"namespaces owned by more than one directory: {shared}")
        self.directories = {ns: ds[0] for ns, ds in owners.items()}
        self.modules: dict[str, str] = {}
        for directory, namespace in self.namespaces.items():
            theories = root / directory / "theories"
            for path in sorted(theories.rglob("*.v")):
                logical = namespace + "." + path.relative_to(theories).as_posix()[:-2].replace("/", ".")
                self.modules[logical] = path.relative_to(root).as_posix()

    def resolve(self, prefix: str | None, name: str) -> tuple[str, str | None]:
        """("external", None), ("module", logical name) or ("unresolved", reason)."""
        full = f"{prefix}.{name}" if prefix else name
        namespace = full.split(".", 1)[0]
        if namespace not in self.directories:
            return "external", None
        if full in self.modules:
            return "module", full
        head = (prefix or namespace) + "."
        tail = "." + full[len(head):]
        candidates = sorted(m for m in self.modules if m.startswith(head) and m.endswith(tail))
        if len(candidates) == 1:
            return "module", candidates[0]
        return "unresolved", f"{full} ({len(candidates)} candidates)"

    def imports(self, rel: str) -> tuple[list[str], list[str]]:
        """The repository modules a source requires, and its unresolved requires."""
        modules, unresolved = set(), []
        for prefix, name in required_modules((self.root / rel).read_text(encoding="utf-8")):
            kind, value = self.resolve(prefix, name)
            if kind == "module":
                modules.add(value)
            elif kind == "unresolved":
                unresolved.append(value)
        return sorted(modules), unresolved


def is_example(rel: str) -> bool:
    return "examples" in PurePosixPath(rel).parts[2:-1]


def static_analysis(tree: SourceTree, packages: dict[str, str], is_public) -> dict:
    """Public modules per package, their direct package dependencies, the examples' imports,
    and the problems: barriers, leaks, examples importing examples, unresolved requires."""
    owner = {logical: rel.split("/", 1)[0] for logical, rel in tree.modules.items()}
    public = {logical for logical, rel in tree.modules.items() if is_public(rel)}
    problems = [f"{tree.modules[m]}: public, but {owner[m]} has no package"
                for m in sorted(public) if owner[m] not in packages]
    result: dict = {"public": {}, "deps": {}, "examples": {}, "problems": problems}
    for directory in sorted(packages):
        modules = sorted(m for m in public if owner[m] == directory)
        if not modules:
            problems.append(f"{directory}: no public module to package")
        deps = set()
        for module in modules:
            rel = tree.modules[module]
            imported, unresolved = tree.imports(rel)
            problems += [f"{rel}: unresolved Require {u}" for u in unresolved]
            for target in imported:
                if target not in public:
                    problems.append(f"BARRIER {rel} imports the non-public {target} ({tree.modules[target]})")
                elif owner[target] != directory:
                    deps.add(owner[target])
        result["public"][directory] = modules
        result["deps"][directory] = sorted(deps)
    for logical, rel in sorted(tree.modules.items(), key=lambda kv: kv[1]):
        if not is_example(rel):
            continue
        imported, unresolved = tree.imports(rel)
        problems += [f"{rel}: unresolved Require {u}" for u in unresolved]
        for target in imported:
            if is_example(tree.modules[target]):
                problems.append(f"EXAMPLE {rel} imports the example {target}")
            elif target not in public:
                problems.append(f"LEAK {rel} imports the non-public {target} ({tree.modules[target]})")
        result["examples"][rel] = imported
    return result


def install_order(names: list[str], files: dict[str, dict]) -> tuple[list[str], list[str]]:
    deps = {n: sorted(p for p, _, _ in files[n]["depends"] if p.startswith(CANONICAL_PREFIX)) for n in names}
    order: list[str] = []
    while len(order) < len(names):
        ready = [n for n in names if n not in order and all(d in order for d in deps[n])]
        if not ready:
            return order, [f"internal depends: a cycle or an unknown package among "
                           f"{sorted(set(names) - set(order))}"]
        order.append(ready[0])
    return order, []


def project_flags(text: str) -> list[str]:
    """The compiler flags of a _CoqProject's -arg options."""
    tokens = shlex.split(text, comments=True)
    flags = []
    for i, token in enumerate(tokens[:-1]):
        if token == "-arg":
            flags += shlex.split(tokens[i + 1])
    return flags


def metadata(root: Path) -> tuple[dict, list[str]]:
    """Step 1 without tools: the opam files, the contract, the import table, the order."""
    problems: list[str] = []
    packages = {d: CANONICAL_PREFIX + suffix for d, suffix in sorted(PKG.PACKAGES.items())}
    dirs = {name: d for d, name in packages.items()}
    texts = {p.stem: p.read_text(encoding="utf-8") for p in sorted((root / "opam").glob("*.opam"))}
    expected = set(packages.values()) | set(WRAPPERS)
    if set(texts) != expected:
        problems.append(f"opam/: unexpected {sorted(set(texts) - expected)}, missing {sorted(expected - set(texts))}")
    for old, new in sorted(LEGACY_COPIES.items()):
        a, b = root / old, root / new
        if not (a.is_file() and b.is_file() and a.read_bytes() == b.read_bytes()):
            problems.append(f"{old}: not byte-equal to {new}")
    files: dict[str, dict] = {}
    for name, text in sorted(texts.items()):
        if name not in expected:
            continue
        try:
            fields = parse_opam(text)
        except OpamSyntax as exc:
            problems.append(f"opam/{name}.opam: {exc}")
            continue
        entries, more = depends_of(name, fields)
        pin, pin_more = pin_depends_commit(name, fields)
        more += pin_more
        if name in WRAPPERS:
            more += wrapper_problems(name, fields, entries)
        else:
            more += canonical_problems(name, fields, dirs[name], entries)
        problems += more
        files[name] = {"fields": fields, "depends": entries, "pin": pin, "contract_ok": not more}
    tree = SourceTree(root, INV.repository_namespaces())
    missing_ns = sorted(d for d in packages if d not in tree.namespaces)
    if missing_ns:
        raise Refused(f"package directories without a namespace or theories/: {missing_ns}")
    analysis = static_analysis(tree, packages, public_repository_path)
    problems += analysis["problems"]
    canonical = [n for n in sorted(packages.values()) if n in files]
    for name in canonical:
        declared = sorted(p for p, _, _ in files[name]["depends"] if p.startswith(CANONICAL_PREFIX))
        measured = sorted(packages[d] for d in analysis["deps"][dirs[name]])
        if declared != measured:
            problems.append(f"{name}: internal depends {declared} != the packages its public modules import {measured}")
    order, more = install_order(canonical, files)
    problems += more
    flags = {d: project_flags((root / d / "_CoqProject").read_text(encoding="utf-8"))
             for d in tree.namespaces if (root / d / "_CoqProject").is_file()}
    info = {"packages": packages, "dirs": dirs, "names": sorted(texts), "files": files, "tree": tree,
            "analysis": analysis, "order": order, "flags": flags}
    return info, problems


# ── tools ──

def run_command(argv: list[str], *, cwd: Path, env: dict[str, str], log: Path | None = None) -> tuple[int, str]:
    """Run argv without a shell; (rc, stdout + stderr). A program that cannot start gives rc 127."""
    try:
        proc = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        rc, output = proc.returncode, proc.stdout.decode("utf-8", "replace")
    except OSError as exc:
        rc, output = 127, f"{argv[0]}: {exc}\n"
    if log is not None:
        log.write_text(f"$ {shlex.join(argv)}\n# cwd {cwd}\n{output}# rc {rc}\n", encoding="utf-8")
    return rc, output


def lint_tools(root: Path, names: list[str], env: dict[str, str]) -> list[str]:
    problems = []
    for name in names:
        rel = f"opam/{name}.opam"
        rc, output = run_command(["opam", "lint", rel], cwd=root, env=env)
        problems += lint_output_problems(rel, rc, output)
    return problems


def installed_versions(root: Path, env: dict[str, str]) -> tuple[dict[str, str], list[str]]:
    rc, output = run_command(OPAM_LIST, cwd=root, env=env)
    if rc != 0:
        return {}, [f"opam list rc {rc}: {' '.join(output.split())[:300]}"]
    versions = dict(line.split() for line in output.splitlines() if len(line.split()) == 2)
    return versions, ([] if versions else ["opam list printed no installed package"])


def tool_versions(root: Path, env: dict[str, str]) -> dict[str, str | None]:
    versions: dict[str, str | None] = {}
    for key, argv in (("rocq", ["rocq", "--version"]), ("opam", ["opam", "--version"]),
                      ("opam-installer", ["opam-installer", "--version"]), ("make", ["make", "--version"])):
        rc, output = run_command(argv, cwd=root, env=env)
        lines = output.strip().splitlines()
        versions[key] = " ".join(lines[0].split()) if rc == 0 and lines else None
    versions["python3"] = sys.version.split()[0]
    return versions


# ── source identity and inputs ──

def source_identity(commit: str | None, tree: str | None) -> dict:
    for flag, value in (("--source-commit", commit), ("--source-tree", tree)):
        if not value:
            raise Refused(f"{flag} is required (make: set GATE_SOURCE_COMMIT and GATE_SOURCE_TREE); "
                          "the gate never reads git")
        if not HEX40.fullmatch(value):
            raise Refused(f"{flag} {value!r} is not 40 lower-case hex digits")
    return {"commit": commit, "tree": tree, "declared_by": "caller"}


def normal_row_path(path: str) -> str | None:
    """'./a/b' and 'a/b' name the same row; an absolute path or a '.', '..' or empty component is refused."""
    if path.startswith("./"):
        path = path[2:]
    parts = path.split("/")
    if not path or path.startswith("/") or any(p in ("", ".", "..") for p in parts):
        return None
    return path


def tree_manifest(path: Path) -> dict[str, str]:
    """A sha256sum manifest (`<hex>  <path>` or `<hex> *<path>`), keyed by the normalised path."""
    if not path.is_file():
        raise Refused(f"--tree-sha256 {path} is not a file")
    rows: dict[str, str] = {}
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-f]{64}) [ *](.+)", line)
        key = normal_row_path(match.group(2)) if match else None
        if key is None:
            raise Refused(f"{path}:{number}: not a sha256sum row with a relative path: {line[:120]!r}")
        if key in rows:
            raise Refused(f"{path}:{number}: a second row for {key}")
        rows[key] = match.group(1)
    return rows


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_digests(root: Path, paths: list[str]) -> dict[str, str]:
    digests = {}
    for rel in sorted(set(paths)):
        source = root / rel
        if source.is_symlink() or not source.is_file():
            raise Refused(f"input {rel} is missing or a symlink")
        digests[rel] = sha256_file(source)
    return digests


def manifest_problems(digests: dict[str, str], manifest: dict[str, str]) -> list[str]:
    problems = []
    for rel, digest in sorted(digests.items()):
        if rel not in manifest:
            problems.append(f"{rel}: not a row of the tree manifest")
        elif manifest[rel] != digest:
            problems.append(f"{rel}: sha256 {digest} != the tree manifest's {manifest[rel]}")
    return problems


def excluded(rel: str) -> bool:
    path = PurePosixPath(rel)
    return (path.suffix == ".json" or bool(EXCLUDED_DIRS.intersection(path.parts[:-1]))
            or path.name.startswith(EXCLUDED_STEMS))


def copy_plan(info: dict) -> list[str]:
    tree, analysis = info["tree"], info["analysis"]
    paths = [f"meta/{reader}" for reader in READERS]
    paths += [f"opam/{name}.opam" for name in info["names"]]
    paths += [f"{d}/_CoqProject" for d in info["packages"]]
    paths += [tree.modules[m] for modules in analysis["public"].values() for m in modules]
    bad = sorted(p for p in paths if excluded(p))
    if bad:
        raise Refused(f"the inclusion-only copy would contain {bad[:5]}")
    return sorted(set(paths))


def make_copy(root: Path, copy: Path, paths: list[str]) -> None:
    for rel in paths:
        target = copy / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / rel, target)


def fresh_out(out: Path | None, root: Path) -> Path:
    if out is None or not str(out):
        raise Refused("--out is required (make: set INSTALL_GATE_OUT=<a fresh directory outside the repository>)")
    out = Path(os.path.abspath(out))
    if out.exists() or out.is_symlink():
        raise Refused(f"--out {out} exists; give a fresh directory")
    target, real_root = out.parent.resolve() / out.name, root.resolve()
    if inside(target, real_root) or inside(real_root, target):
        raise Refused(f"--out {out} must be outside the repository {real_root}")
    target.mkdir(parents=True)
    return target


def inside(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


# ── install ──

def client_env(prefix_uc: Path) -> dict[str, str]:
    """The environment of the package builds and of the downstream clients: check_library_migration's allowlist (no
    inherited MAKEFLAGS options, MAKEOVERRIDES, MFLAGS, GNUMAKEFLAGS, COQFLAGS, COQPATH, PYTHONPATH...; an explicit -jN in
    MAKEFLAGS is kept, and the builds pass -j%{jobs}% expanded anyway), with ROCQPATH = the prefix only."""
    env = CLM.build_environment(dict(os.environ))
    env["ROCQPATH"] = str(prefix_uc)
    return env


def install_entries(text: str) -> list[tuple[str, str]]:
    """(source, destination) rows of a library_package.py manifest (lib_root only)."""
    fields = parse_opam(text)
    if set(fields) != {"opam-version", "lib_root"} or fields["lib_root"][0] != "list":
        raise OpamSyntax(f"manifest fields {sorted(fields)}")
    entries = []
    for item in fields["lib_root"][1]:
        if item[0] != "opt" or item[1][0] != "str" or len(item[2]) != 1 or item[2][0][0] != "str":
            raise OpamSyntax(f"manifest entry {item!r}")
        entries.append((item[1][1], item[2][0][1]))
    return entries


def entry_problems(name: str, directory: str, namespace: str, entries: list[tuple[str, str]],
                   expected_modules: list[str]) -> list[str]:
    """Each public module exactly once as .v/.vo/.glob, from the stage, and nothing else."""
    problems, by_module = [], {}
    stage, top = f"_build/library/{directory}/theories/", f"coq/user-contrib/{namespace}/"
    for source, destination in entries:
        stem, extension = os.path.splitext(destination)
        if not destination.startswith(top) or extension not in (".v", ".vo", ".glob"):
            problems.append(f"{name}: manifest destination {destination}")
            continue
        if source != stage + stem[len(top):] + extension:
            problems.append(f"{name}: {source} installs as {destination}")
        module = stem[len("coq/user-contrib/"):].replace("/", ".")
        by_module.setdefault(module, []).append(extension)
    problems += [f"{name}: {m} installs {sorted(x)}" for m, x in sorted(by_module.items())
                 if sorted(x) != [".glob", ".v", ".vo"]]
    extra, missing = sorted(set(by_module) - set(expected_modules)), sorted(set(expected_modules) - set(by_module))
    if extra or missing:
        problems.append(f"{name}: manifest modules: non-public or unexpected {extra}, missing {missing}")
    return problems


def installed_problems(name: str, root: Path, copy: Path, prefix: Path, directory: str, namespace: str,
                       entries: list[tuple[str, str]]) -> list[str]:
    problems, top = [], f"coq/user-contrib/{namespace}/"
    for source, destination in entries:
        target = prefix / "lib" / destination
        if not target.is_file():
            problems.append(f"{name}: {destination} is not installed")
            continue
        if target.read_bytes() != (copy / source).read_bytes():
            problems.append(f"{name}: {destination} differs from {source}")
        if destination.endswith(".v"):
            original = root / directory / "theories" / destination[len(top):]
            if not original.is_file() or original.read_bytes() != target.read_bytes():
                problems.append(f"{name}: {destination} differs from the tree's source")
    return problems


def prefix_problems(prefix: Path, expected: set[str]) -> list[str]:
    files = {p.relative_to(prefix).as_posix() for p in prefix.rglob("*") if p.is_file() or p.is_symlink()}
    extra, missing = sorted(files - expected), sorted(expected - files)
    return ([f"the prefix holds {len(extra)} file(s) no manifest names: {extra[:5]}"] if extra else []) + \
           ([f"the prefix lacks {len(missing)} manifest file(s): {missing[:5]}"] if missing else [])


# ── downstream ──

def downstream_name(namespace: str, rel: str) -> str:
    """base/theories/examples/a/b.v -> GTBase__a__b.v (a valid module name outside every package)."""
    return namespace + "__" + "__".join(PurePosixPath(rel).parts[3:])[:-2] + ".v"


def client_path_problems(argv: list[str], env: dict[str, str], cwd: Path, prefix_uc: Path,
                         forbidden: list[Path]) -> list[str]:
    """A client sees the prefix and its own directory, never a repository or copy path; and the prefix is never inside a
    client load path (Rocq would remap it there: overriding-logical-loadpath, seen in V-a r2's probe)."""
    problems = []
    if "COQPATH" in env:
        problems.append("COQPATH is set for a client")
    if env.get("ROCQPATH") != str(prefix_uc):
        problems.append(f"ROCQPATH is {env.get('ROCQPATH')!r}, not the prefix")
    for i, arg in enumerate(argv[:-1]):
        if arg in ("-R", "-Q", "-I"):
            path = (cwd / argv[i + 1]).resolve()
            hit = [str(root) for root in forbidden if inside(path, root)]
            if hit:
                problems.append(f"the client load path {argv[i + 1]} is inside {hit}")
            if inside(prefix_uc.resolve(), path):
                problems.append(f"the prefix {prefix_uc} is inside the client load path {argv[i + 1]}")
    return problems


LOCATED = r"(?:Library\s+)?{module}\s+(?:has\s+been\s+loaded\s+from|is\s+bound\s+to)\s+file\s+(\S+)"


def located_files(output: str, modules: list[str]) -> dict[str, str | None]:
    joined = " ".join(output.split())
    found: dict[str, str | None] = {}
    for module in modules:
        match = re.search(LOCATED.format(module=re.escape(module)), joined)
        found[module] = match.group(1).rstrip(".") if match else None
    return found


def locate_problems(found: dict[str, str | None], prefix_uc: Path) -> list[str]:
    problems = []
    for module, path in sorted(found.items()):
        if path is None:
            problems.append(f"Locate Library {module}: no file named")
        elif not path.endswith(".vo") or not inside(Path(path).resolve(), prefix_uc.resolve()):
            problems.append(f"Locate Library {module}: {path} is not a prefix file")
    return problems


def neg_preconditions(root: Path, prefix_uc: Path, is_public) -> list[str]:
    """The planted client must fail for the right reason: its module exists, is non-public and is not installed."""
    problems = []
    if not (root / NEG_SOURCE).is_file():
        problems.append(f"{NEG_SOURCE} is not in the tree, so the planted client would fail vacuously")
    elif is_public(NEG_SOURCE):
        problems.append(f"{NEG_SOURCE} is public")
    installed = sorted(p.name for p in (prefix_uc / "GTBase" / "migration").glob("edge_count.*"))
    if installed:
        problems.append(f"the prefix holds {installed}")
    return problems


def neg_verdict(rc: int, output: str) -> tuple[bool, str]:
    """The planted client passes only by FAILING with an error that names the non-public module."""
    joined = " ".join(output.split())
    at = joined.find("Error")
    error = joined[at:at + 300] if at >= 0 else joined[:300]
    return rc != 0 and at >= 0 and NEG_NAME in joined[at:], error


# ── the gate ──

def lint_only(root: Path) -> int:
    with tempfile.TemporaryDirectory(prefix="opam-lint-logs-") as logs:
        env = dict(os.environ, OPAMLOGS=logs)
        info, problems = metadata(root)
        problems += lint_tools(root, info["names"], env)
        installed, more = installed_versions(root, env)
        problems += more + pin_problems(info["files"], installed, graph_theory_commit(root))
    for problem in problems:
        print(f"LINT FAIL {problem}")
    print(f"OPAM_LINT {'FAIL' if problems else 'PASS'}: {len(info['names'])} opam files "
          f"(+ {len(LEGACY_COPIES)} byte-equal copies), {len(problems)} problems")
    return 1 if problems else 0


def gate(root: Path, a: argparse.Namespace) -> int:
    source = source_identity(a.source_commit, a.source_tree)
    tree_rows = tree_manifest(a.tree_sha256) if a.tree_sha256 is not None else None
    out = fresh_out(a.out, root)
    logs, copy, prefix, downstream = out / "logs", out / "copy", out / "prefix", out / "downstream"
    for directory in (logs, logs / "opam", copy, prefix, downstream):
        directory.mkdir()
    prefix_uc = prefix / "lib" / "coq" / "user-contrib"
    prefix_uc.mkdir(parents=True)  # ROCQPATH names it from the first package's build on
    opam_env = dict(os.environ, OPAMLOGS=str(logs / "opam"))
    env = client_env(prefix_uc)
    problems: list[str] = []
    steps: dict[str, dict] = {}
    started = time.time()

    def done(step: str, since: float, more: list[str]) -> None:
        problems.extend(f"{step}: {p}" for p in more)
        steps[step] = {"problems": len(more), "elapsed_s": round(time.time() - since, 1)}
        print(f"STEP {step}: {len(more)} problems, {steps[step]['elapsed_s']} s", flush=True)

    # 1. lint
    t = time.time()
    info, more = metadata(root)
    more += lint_tools(root, info["names"], opam_env)
    installed, more_installed = installed_versions(root, opam_env)
    commit = graph_theory_commit(root)
    more += more_installed + pin_problems(info["files"], installed, commit)
    versions = tool_versions(root, opam_env)
    done("lint", t, more)

    # 2. copy, and the digest of every input
    t = time.time()
    paths = copy_plan(info)
    examples = sorted(info["analysis"]["examples"])
    read = paths + examples + [f"{d}/_CoqProject" for d in info["flags"]] \
        + [p for p in [*sorted(LEGACY_COPIES), PINS] if (root / p).is_file()]
    digests = input_digests(root, read)
    digests["meta/install_gate.py"] = sha256_file(Path(__file__))
    rows = "".join(f"{digest}  ./{rel}\n" for rel, digest in sorted(digests.items()))
    (out / "inputs.sha256").write_text(rows, encoding="utf-8")
    more = manifest_problems(digests, tree_rows) if tree_rows is not None else []
    make_copy(root, copy, paths)
    done("copy", t, more)

    # 3. build + install, in internal-dependency order
    t = time.time()
    more, built, records, expected_prefix = [], [], [], set()
    for name in info["order"]:
        directory = info["dirs"][name]
        namespace = info["tree"].namespaces[directory]
        record: dict = {"package": name, "dir": directory, "namespace": namespace, "commands": []}
        records.append(record)
        file = info["files"][name]
        deps = [p for p, _, _ in file["depends"] if p.startswith(CANONICAL_PREFIX)]
        if not file["contract_ok"] or any(d not in built for d in deps):
            record["skipped"] = "a metadata problem, or a dependency not installed"
            more.append(f"{name}: skipped ({record['skipped']})")
            continue
        for k, argv in enumerate(expand(file["fields"]["build"], a.jobs), 1):
            log = logs / f"{name}.build{k}.log"
            rc, _ = run_command(argv, cwd=copy, env=env, log=log)
            record["commands"].append({"argv": argv, "rc": rc, "log": log.name, "log_sha256": sha256_file(log)})
            if rc != 0:
                more.append(f"{name}: build command {k} rc {rc} (logs/{log.name})")
                break
        else:
            try:
                entries = install_entries((copy / f"{name}.install").read_text(encoding="utf-8"))
            except (OSError, OpamSyntax) as exc:
                more.append(f"{name}: manifest: {exc}")
                continue
            expected_modules = info["analysis"]["public"][directory]
            found = entry_problems(name, directory, namespace, entries, expected_modules)
            log = logs / f"{name}.install.log"
            rc, output = run_command(["opam-installer", f"--prefix={prefix}", f"{name}.install"],
                                     cwd=copy, env=env, log=log)
            record["install"] = {"rc": rc, "log": log.name, "log_sha256": sha256_file(log)}
            if rc != 0 or "[ERROR]" in output:
                found.append(f"{name}: opam-installer rc {rc} (logs/{log.name})")
            else:
                found += installed_problems(name, root, copy, prefix, directory, namespace, entries)
            record.update(modules=len(expected_modules), manifest_rows=len(entries), problems=found)
            expected_prefix |= {"lib/" + destination for _, destination in entries}
            more += found
            if not found:
                built.append(name)
    more += prefix_problems(prefix, expected_prefix)
    done("install", t, more)

    # 4. downstream: the examples with ROCQPATH = the prefix only, Locate, then the planted client
    t = time.time()
    more, clients = [], []
    if a.expect_examples is not None and len(examples) != a.expect_examples:
        more.append(f"{len(examples)} examples, expected {a.expect_examples}")
    forbidden = [root.resolve(), copy.resolve()]
    if len(built) != len(info["order"]) or not info["order"]:
        more.append("skipped: not every package installed")
    else:
        names = {}
        for rel in examples:
            namespace = info["tree"].namespaces[rel.split("/", 1)[0]]
            name = downstream_name(namespace, rel)
            if not IDENT.fullmatch(name[:-2]) or name in names.values():
                more.append(f"{rel}: no unique downstream name ({name})")
                continue
            names[rel] = name
            shutil.copyfile(root / rel, downstream / name)
        (downstream / "_CoqProject").write_text("-R . Downstream\n", encoding="utf-8")
        for rel, name in sorted(names.items()):
            argv = ["rocq", "compile", "-R", ".", "Downstream", *info["flags"].get(rel.split("/", 1)[0], []), name]
            found = client_path_problems(argv, env, downstream, prefix_uc, forbidden)
            log = logs / f"client.{name[:-2]}.log"
            rc = None
            if not found:
                rc, _ = run_command(argv, cwd=downstream, env=env, log=log)
                if rc != 0:
                    found.append(f"{rel}: rc {rc} (logs/{log.name})")
            clients.append({"example": rel, "client": name, "sha256": digests[rel], "argv": argv, "rc": rc,
                            "log_sha256": sha256_file(log) if log.exists() else None})
            more += found
    imported = sorted({m for ms in info["analysis"]["examples"].values() for m in ms})
    located: dict = {}
    neg: dict = {}
    if not more and clients:
        probe = downstream / LOCATE_PROBE
        probe.write_text("".join(f"Locate Library {m}.\n" for m in imported), encoding="utf-8")
        log = logs / "client.locate.log"
        rc, output = run_command(["rocq", "compile", "-R", ".", "Downstream", LOCATE_PROBE],
                                 cwd=downstream, env=env, log=log)
        located = located_files(output, imported)
        more += ([f"the Locate probe rc {rc}"] if rc != 0 else []) + locate_problems(located, prefix_uc)
        # The planted client runs only AFTER every positive client compiled.
        found = neg_preconditions(root, prefix_uc, public_repository_path)
        if not found:
            (downstream / NEG_CLIENT).write_text(NEG_TEXT, encoding="utf-8")
            log = logs / "client.neg.log"
            argv = ["rocq", "compile", "-R", ".", "Downstream", NEG_CLIENT]
            found = client_path_problems(argv, env, downstream, prefix_uc, forbidden)
            if not found:
                rc, output = run_command(argv, cwd=downstream, env=env, log=log)
                ok, error = neg_verdict(rc, output)
                neg = {"client": NEG_CLIENT, "requires": NEG_TEXT.strip(), "rc": rc, "error": error, "passed": ok}
                if not ok:
                    found.append(f"the planted non-public client did not fail naming {NEG_NAME} "
                                 f"(rc {rc}: {error[:120]})")
        more += [f"planted client: {p}" for p in found]
    elif not more:
        more.append("no example to compile")
    done("downstream", t, more)

    # 5. receipt
    failed = sum(1 for c in clients if c["rc"] != 0)
    modules = sum(len(ms) for ms in info["analysis"]["public"].values())
    prefix_files = len(expected_prefix)
    if problems:
        final = f"INSTALL_GATE FAIL: {len(problems)} problems; first: {problems[0][:200]}"
    else:
        final = (f"INSTALL_GATE PASS: {len(built)} packages, {modules} public modules, {prefix_files} prefix files, "
                 f"{len(clients)} examples, {failed} failed")
    replay = [{"package": n, "dir": info["dirs"][n],
               "depends": [{"package": p, "constraint": k, "value": v} for p, k, v in info["files"][n]["depends"]],
               "pin_depends_commit": info["files"][n]["pin"]} for n in info["order"]]
    receipt = {
        "tool": "meta/install_gate.py", "tool_sha256": digests["meta/install_gate.py"],
        "source": source,
        "inputs": {"file": "inputs.sha256", "rows": len(digests), "sha256": sha256_file(out / "inputs.sha256")},
        "tree_sha256": sha256_file(a.tree_sha256) if a.tree_sha256 is not None else None,
        "jobs": a.jobs, "makeflags": os.environ.get("MAKEFLAGS"), "toolchain": versions,
        "build_env": {"keys": sorted(env), "makeflags": env.get("MAKEFLAGS"), "rocqpath": env["ROCQPATH"]},
        "installed_packages": installed, "graph_theory_commit_of_record": commit,
        "opam_files": {"linted": len(info["names"]), "byte_equal_copies": sorted(LEGACY_COPIES)},
        "order": info["order"], "packages": records, "prefix_files": prefix_files,
        "examples": clients, "locate": located, "planted_client": neg, "replay": replay,
        "steps": steps, "elapsed_s": round(time.time() - started, 1),
        "problems": problems, "verdict": "FAIL" if problems else "PASS", "final": final,
    }
    (out / "install-gate.json").write_text(json.dumps(receipt, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    for problem in problems:
        print(f"PROBLEM {problem}")
    print(final)
    return 1 if problems else 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    ap.add_argument("--out", type=Path, help="a fresh directory outside the repository")
    ap.add_argument("--source-commit", help="the 40-hex commit the caller binds (D-5's S)")
    ap.add_argument("--source-tree", help="the 40-hex tree the caller binds")
    ap.add_argument("--tree-sha256", type=Path, help="the caller's sha256sum manifest of the tree")
    ap.add_argument("--jobs", type=int, default=1, help="the value of %%{jobs}%% (D-5: 1, under MAKEFLAGS=-j1)")
    ap.add_argument("--expect-examples", type=int, help="the number of example files to require")
    ap.add_argument("--lint-only", action="store_true", help="step 1 alone (make opam-lint)")
    a = ap.parse_args(argv)
    try:
        if a.jobs < 1:
            raise Refused("--jobs must be at least 1")
        return lint_only(ROOT) if a.lint_only else gate(ROOT, a)
    except Refused as exc:
        print(f"INSTALL_GATE REFUSED: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
