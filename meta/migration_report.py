#!/usr/bin/env python3
"""Generate and check the migration report of one library-migration family.

Usage:
    python3 meta/migration_report.py FAMILY [--write | --check] [--kernel]
    python3 meta/migration_report.py --all --check [--kernel]
    python3 meta/migration_report.py FAMILY --details /tmp/migration-details
    python3 meta/migration_report.py --validate

FAMILY names a spec file meta/migration_reports/FAMILY.spec.json.  The spec lists
every frozen object of the family's certificates: the original declaration (path,
name and the commit it is frozen from), the frozen copy (certificate path, module
and name), the identifier substitutions that turn the original text into the
frozen one, and the certificate theorem relating the frozen body to the live one.

The default checks are toolchain-free. --kernel additionally checks the exact
types and assumptions of closed statement certificates, using already-built
modules; check_library_migration.py checks the registered helper/API assumptions.
Lexical reference discovery is conservative, not Rocq name resolution. In
particular it does not certify Section scaffolding or compiled dependency closure;
family-specific Section and kernel dependency evidence remains required.
Statement objects may select corpus "opg" or "v2", or explicitly set
"non_corpus": true. Unmarked statements must resolve uniquely in the manifests.
An optional "additional_statements" list explicitly classifies reached, closed
non-corpus Props whose names are not discovered automatically. Enrollment is
restricted to unambiguous top-level nullary Definitions, with ordinary frozen
body, complete-iff and zero-assumption checks still required. A separate
"parametric_statements" list explicitly enrolls reached whole Props lying
directly in one top-level Section: each entry pins the Section, its complete
Variable scaffold, the discharged parameters with fully qualified kernel types,
generated @-bindings of referenced same-Section declarations and a live-shape
witness; certificates are pointwise iffs at every parameter.
Every occurrence of a complete row requires a statement role and an exact iff
probe, independently of its label. New reused nonstatement objects use the
"historical" role; the existing named historical roles remain supported aliases.
It verifies that

  * each frozen copy equals its original declaration, after comment stripping,
    whitespace normalization and the listed substitutions, and records the
    original declaration hash (the inventory's declaration_hash) and git blob;
  * each source helper's recorded hash matches the baseline helper inventory,
    or its explicitly enrolled immutable public repository source;
  * each affected statement's frozen chain covers every same-file declaration
    through which the statement reaches a source helper; enrolled public sources
    also require complete reaching paths through public base/foundation nodes;
  * no frozen body in any migration certificate still resolves through a live
    helper or chain declaration of this family (reported, not hidden, when an
    earlier family's certificate does);
  * statement texts, their doc blocks, manifest rows and leg states are unchanged
    since the baseline, and the listed distinct name matches are untouched;
  * every certificate theorem is declared in its certificate file.

--write refreshes only the compact committed meta/migration_reports/FAMILY.md;
--check verifies its contents and all source checks. --details DIR writes the
full deterministic JSON and Markdown evidence to DIR, independently of the
compact output. DIR must be outside the committed report directory and its
descendants. --all --check rejects non-specification JSON anywhere in that
directory. Full reports are generated on demand, not committed artifacts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import posixpath
import re
import shlex
import subprocess
import sys
import tempfile
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

import library_inventory as INV
import corpus_registry as REG
import rocq_toolchain as ROCQ
from family_registry import RegistryError, load_library_registry, public_repository_path


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "meta" / "migration_reports"
IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
DECL_KEYWORDS = (
    "Definition|Let|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Variant|Class|"
    "Instance|Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example"
)
DECL_RE = re.compile(
    rf"^\s*(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*"
    rf"(?:{DECL_KEYWORDS})\s+({IDENT})" + INV.IDENT_END,
    re.M,
)
SKIP_PREFIXES = ("_assum_", "_faith_", "scratch_", "gcheck")
QUALIFIED_IDENT_RE = re.compile(rf"(?<![A-Za-z0-9_'.]){IDENT}(?:\.{IDENT})*(?![A-Za-z0-9_'])")
STATEMENT_KINDS = frozenset({"statement", "original-statement"})
HISTORICAL_KINDS = frozenset({
    "historical", "a1-frozen", "a5-frozen", "a6-frozen", "b1-frozen",
    "b3-frozen", "b4-frozen", "c5-frozen", "m1-frozen",
})
FROZEN_KINDS = STATEMENT_KINDS | HISTORICAL_KINDS | {"source", "chain", "original-chain"}


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def _git_at(root: str | Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, check=True, capture_output=True, text=True
    ).stdout


def git(*args: str) -> str:
    return _git_at(ROOT, *args)


def _resolve_commit(root: str, identity: tuple, commit: str) -> str:
    return _git_at(root, "rev-parse", "--verify", commit + "^{commit}").strip()


_full_commit = lru_cache(maxsize=256)(_resolve_commit)


def _historical_key(repository: tuple, commit: str) -> tuple | None:
    # Only full object names are immutable. Resolve HEAD, branches and tags
    # afresh even if a prior call successfully resolved the same spelling.
    resolve = (_full_commit if re.fullmatch(r"[0-9a-f]{40}", commit)
               else _resolve_commit)
    try:
        return (*repository, resolve(*repository, commit))
    except subprocess.CalledProcessError:
        # Git also accepts tree expressions here. Unsupported cache keys and
        # missing references must retain the original operation/error behavior.
        return None


def _history_repository() -> tuple | None:
    # Replacement refs can change a full object's effective contents. Read
    # their presence afresh, including packed refs, and use original Git reads
    # for custom repository/ref environments or unsupported ref storage.
    if any(name.startswith("GIT_") for name in os.environ):
        return None
    root = ROOT.resolve()
    try:
        dotgit = root / ".git"
        if dotgit.is_dir():
            gitdir = dotgit.resolve()
        else:
            pointer = dotgit.read_text().strip()
            if not pointer.startswith("gitdir: "):
                return None
            gitdir = (root / pointer[8:]).resolve()
        common_file = gitdir / "commondir"
        common = ((gitdir / common_file.read_text().strip()).resolve()
                  if common_file.exists() else gitdir)
        # Bind repository indirection afresh without a subprocess on each hit.
        # Reused checkout paths and replaced object directories are distinct.
        identity = tuple((str(path), path.stat().st_dev, path.stat().st_ino)
                         for path in (gitdir, common, common / "objects"))
        if any(path.exists() for path in (
                common / "refs/replace", common / "reftable",
                common / "objects/info/alternates")):
            return None
        packed = common / "packed-refs"
        if packed.exists() and "refs/replace/" in packed.read_text():
            return None
        return str(root), identity
    except (OSError, UnicodeError):
        # Unsupported/missing repository metadata retains Git's own errors.
        return None


@lru_cache(maxsize=2048)
def _historical_source(root: str, identity: tuple, commit: str, path: str) -> str:
    return _git_at(root, "show", f"{commit}:{path}")


@lru_cache(maxsize=2048)
def _historical_blob(root: str, identity: tuple, commit: str, path: str) -> str:
    return _git_at(root, "rev-parse", f"{commit}:{path}").strip()


def source_at(commit: str | None, path: str) -> str:
    """File text at a commit, or in the working tree when commit is None."""
    if commit is None:
        return (ROOT / path).read_text()
    repository = _history_repository()
    key = _historical_key(repository, commit) if repository is not None else None
    if key is None:
        return git("show", f"{commit}:{path}")
    return _historical_source(*key, path)


def blob_at(commit: str, path: str) -> str:
    repository = _history_repository()
    key = _historical_key(repository, commit) if repository is not None else None
    if key is None:
        return git("rev-parse", f"{commit}:{path}").strip()
    return _historical_blob(*key, path)


def ref_re(name: str) -> re.Pattern[str]:
    # Match from the beginning of a qualified name; callers can distinguish a
    # live module reference from Legacy.foo without losing either reference.
    return re.compile(rf"(?<![A-Za-z0-9_'.])(?:{IDENT}\.)*{re.escape(name)}(?![A-Za-z0-9_'])")


def frozen_reference(name: str, modules: set[str] = frozenset()) -> bool:
    return any(part in modules or part == "Legacy" or part.endswith(("Legacy", "Original"))
               for part in name.split(".")[:-1])


def live_reference(text: str, name: str, modules: set[str] = frozenset()) -> bool:
    return any(not frozen_reference(m.group(), modules) for m in ref_re(name).finditer(text))


class ProviderContext:
    """Conservative source attribution in the declared project build context.

    Repository namespaces belong exclusively to repository project roots;
    installed libraries must not inject or shadow them. This is a supported
    build contract, not certification of an arbitrary ambient Rocq loader.
    Unknown contexts keep the old candidate superset. Instances are local to a
    single dependency/report query, so current reads are never cached across it.
    """

    NON_LOADER_SETTINGS = {
        "ROCQ_OPAM_SWITCH", "ROCQ_STEP_TIMEOUT", "ROCQ_QED_TIMEOUT",
        "ROCQ_WORKDIR", "ROCQ_PROJECT_ROOT", "ROCQ_CLI_CPUS", "ROCQ_CLI_MEMORY",
        "ROCQ_MCP_MEMORY",
    }

    def __init__(self, commit: str | None):
        self.commit = commit
        self.namespaces = INV.repository_namespaces()
        self.roots = {package + "/theories": namespace
                      for package, namespace in self.namespaces.items()}
        self.projects: dict[str, tuple[set[str], set[str]] | None] = {}
        self.contexts: dict[str, set[str] | None] = {}
        self.fallbacks: set[tuple[str, str]] = set()
        self.modes: dict[str, str] | None = None
        self.regular_paths: set[str] = set()

    def unknown(self, path: str, reason: str) -> None:
        self.fallbacks.add((path, reason))

    def regular_text(self, path: str) -> str:
        relative = Path(path)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("non-repository path")
        if self.commit is not None:
            if self.modes is None:
                self.modes = {}
                for line in git("ls-tree", "-r", self.commit).splitlines():
                    identity, name = line.split("\t", 1)
                    self.modes[name] = identity.split()[0]
            if self.modes.get(path) not in {"100644", "100755"}:
                raise ValueError("missing or non-regular historical source")
        else:
            target = ROOT / relative
            if (not target.is_file() or any((ROOT / parent).is_symlink()
                    for parent in (relative, *relative.parents) if parent != Path("."))):
                raise ValueError("missing or non-regular current source")
        text = source_at(self.commit, path)
        self.regular_paths.add(path)
        return text

    def project(self, package: str) -> tuple[set[str], set[str]] | None:
        if package in self.projects:
            return self.projects[package]
        path = package + "/_CoqProject"
        try:
            text = self.regular_text(path)
            tokens = shlex.split(text, comments=True)
            mappings, members = [], set()
            i = 0
            while i < len(tokens):
                token = tokens[i]
                if token in {"-R", "-Q"} and i + 2 < len(tokens):
                    directory, namespace = tokens[i + 1:i + 3]
                    root = posixpath.normpath(package + "/" + directory)
                    if (directory != posixpath.relpath(root, package)
                            or self.roots.get(root) != namespace):
                        raise ValueError("unsupported or remapped namespace root")
                    mappings.append((root, namespace))
                    i += 3
                elif (tokens[i:i + 3] == ["-arg", "-w", "-arg"] and i + 3 < len(tokens)
                      and re.fullmatch(r"[+-]?[A-Za-z][A-Za-z0-9_-]*(?:,[+-]?[A-Za-z][A-Za-z0-9_-]*)*",
                                       tokens[i + 3])):
                    i += 4
                elif (token.startswith("theories/") and token.endswith(".v")
                      and ".." not in Path(token).parts):
                    members.add(token)
                    i += 1
                else:
                    raise ValueError("unsupported project option or source path")
            roots = {root for root, namespace in mappings}
            if (not mappings or len(roots) != len(mappings)
                    or len({namespace for root, namespace in mappings}) != len(mappings)
                    or package + "/theories" not in roots):
                raise ValueError("missing, duplicate or ambiguous namespace mapping")
            self.projects[package] = members, roots
        except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
            self.unknown(path, str(exc))
            self.projects[package] = None
        return self.projects[package]

    def context(self, package: str) -> set[str] | None:
        if package in self.contexts:
            return self.contexts[package]
        path = package + "/_CoqProject"
        overrides = sorted(name for name, value in os.environ.items() if value
                           and name.startswith(("COQ", "ROCQ"))
                           and name not in self.NON_LOADER_SETTINGS)
        if overrides:
            self.unknown(path, "ambient loader/compiler settings: " + ", ".join(overrides))
            self.contexts[package] = None
            return None
        project = self.project(package)
        if project is None:
            self.contexts[package] = None
            return None
        _, roots = project
        try:
            local_modules = set()
            all_local_modules = set()
            imported_projects = {}
            for root in sorted(roots):
                owner = root.split("/", 1)[0]
                imported = self.project(owner)
                if imported is None:
                    raise ValueError("unsupported mapped project: " + owner)
                imported_projects[owner] = imported
                local_modules.update(self.namespaces[owner] + "." + member[len("theories/"):-2].replace("/", ".")
                                     for member in imported[0])
                if self.commit is not None:
                    paths = [path for path in self.modes or {} if path.startswith(root + "/") and path.endswith(".v")]
                else:
                    paths = [path.relative_to(ROOT).as_posix() for path in (ROOT / root).rglob("*.v")]
                all_local_modules.update(self.namespaces[owner] + "." + path[len(root) + 1:-2].replace("/", ".")
                                         for path in paths)
            # Scan the whole declared local context, not an under-approximated
            # textual Require closure. No assertion about empty external deps.
            for owner, imported in imported_projects.items():
                for member in sorted(imported[0]):
                    source = owner + "/" + member
                    clean = statement_ownership_text(self.regular_text(source))
                    if re.search(r"\b(?:Load|LoadPath)\b|\b(?:Add|Remove|Declare)\s+ML\b", clean):
                        raise ValueError("dynamic loader command in " + source)
                    self.check_requires(clean, local_modules, all_local_modules, source)
            self.contexts[package] = roots
        except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
            self.unknown(path, str(exc))
            self.contexts[package] = None
        return self.contexts[package]

    def check_requires(self, clean: str, local_modules: set[str], all_local_modules: set[str], source: str) -> None:
        # An unlisted local .vo can carry loader effects even though its source
        # is not among the checked members. Unsupported/bare unknown imports
        # therefore retain candidates; external qualified identities remain
        # subject to the documented non-injection contract, not an empty graph.
        qualified = rf"{IDENT}(?:\.{IDENT})*"
        start = 0
        for end in (*[match.end() for match in re.finditer(r"\.(?=\s|$)", clean)], len(clean)):
            sentence = clean[start:end].strip()
            start = end
            if not re.search(r"\bRequire\b", sentence):
                continue
            command = re.fullmatch(rf"(?:From\s+({qualified})\s+)?Require\s+"
                                   rf"(?:(?:Import|Export)\s+)?({qualified}(?:\s+{qualified})*)\s*\.", sentence)
            if command is None:
                raise ValueError("unsupported Require command in " + source)
            prefix, names = command.groups()
            for name in names.split():
                target = (prefix + "." if prefix else "") + name
                head, _, tail = target.partition(".")
                # Recursive -R roots also permit e.g. Packing.X15 for
                # Packing.conjectures.X15. Keep every possible suffix, never
                # choose an import-order winner; unchecked matches fall back.
                candidates = {module for module in all_local_modules
                              if module == target or module.endswith("." + target)
                              or (head in self.namespaces.values() and tail
                                  and module.startswith(head + ".") and module.endswith("." + tail))}
                if candidates - local_modules:
                    raise ValueError("unlisted local Require " + target + " in " + source)
                if candidates:
                    continue
                if target.split(".", 1)[0] in self.namespaces.values():
                    raise ValueError("unlisted or unmapped local Require " + target + " in " + source)
                if prefix is None:
                    raise ValueError("unresolved or partial Require " + target + " in " + source)

    def possible(self, consumer: str, provider: str) -> bool:
        package = consumer.split("/", 1)[0]
        if package == provider.split("/", 1)[0]:
            return True
        roots = self.context(package)
        if roots is None:
            return True
        try:
            for path in (consumer, provider):
                owner, relative = path.split("/", 1)
                project = self.project(owner)
                if project is None or relative not in project[0]:
                    raise ValueError("missing/unknown provider or consumer project membership: " + path)
                if path not in self.regular_paths:
                    self.regular_text(path)
        except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
            self.unknown(consumer, str(exc))
            return True
        return any(provider.startswith(root + "/") for root in roots)

    def reference(self, consumer: str, token: str, providers: set[str]) -> bool:
        # Qualified references retain the previous full/suffix treatment.
        if "." in token:
            return True
        if not providers:
            self.unknown(consumer, "missing provider provenance for " + token)
            return True
        return any(self.possible(consumer, provider) for provider in sorted(providers))

    def diagnostics(self) -> list[dict]:
        return [{"commit": self.commit, "path": path, "reason": reason}
                for path, reason in sorted(self.fallbacks)]


def declarations(src: str) -> list[dict]:
    """Every declaration of a file: name, enclosing module, normalized text, line.

    The module is the dotted path of the enclosing Modules (Sections leave no
    trace), or None at top level. Unsupported scope structure raises.
    """
    # Callers may modify their result; cached data contains immutable scalars.
    return [dict(zip(("name", "module", "text", "line"), row))
            for row in _declarations(src)]


@lru_cache(maxsize=2048)
def _declarations(src: str) -> tuple[tuple, ...]:
    clean = INV.strip_comments(src)
    masked = INV.scope_mask(src)
    modules = [o for o in INV.scope_openers(masked) if o["kind"] == "Module"]
    out = []
    for match in DECL_RE.finditer(clean):
        start = clean.rfind("\n", 0, match.start(1)) + 1
        if masked[match.start(1)].isspace():
            line = clean.count("\n", 0, match.start(1)) + 1
            raise ValueError(f"declaration {match.group(1)} at line {line} is inside a string")
        module = ".".join(o["label"] for o in modules
                          if o["body_start"] <= match.start(1) < o["close_start"]) or None
        text = INV.normalize_space(clean[start:INV.sentence_end(clean, start)])
        out.append((match.group(1), module, text,
                    clean.count("\n", 0, match.start(1)) + 1))
    return tuple(out)


def find_decl(src: str, name: str, module: str | None = None) -> dict:
    hits = [d for d in declarations(src) if d["name"] == name and d["module"] == module]
    if len(hits) != 1:
        where = f"{module}.{name}" if module else name
        raise ValueError(f"expected one declaration {where}, found {len(hits)}")
    return hits[0]


def substitute(text: str, substitutions: dict[str, str]) -> str:
    # One pass over identifiers, so replacements never cascade.
    if not substitutions:
        return text
    pattern = re.compile(
        r"(?<![A-Za-z0-9_'.])(" + "|".join(
            re.escape(k) for k in sorted(substitutions, key=len, reverse=True)
        ) + r")(?![A-Za-z0-9_'])"
    )
    return pattern.sub(lambda m: substitutions[m.group(1)], text)


@lru_cache(maxsize=128)
def _inventory_index(root: str, identity: tuple, commit: str) -> dict[str, str] | None:
    data = json.loads(_historical_source(root, identity, commit, "meta/library_helper_inventory.json"))
    helpers = data.get("helpers", []) if isinstance(data, dict) else None
    # Malformed shapes use the original ordered lookup below: an error after
    # a matching entry must not make a formerly successful lookup fail early.
    if not isinstance(helpers, list) or any(
            not isinstance(h, dict) or not isinstance(h.get("qualified_name"), str)
            or not isinstance(h.get("declaration_hash"), str) for h in helpers):
        return None
    index = {}
    for helper in helpers:
        index.setdefault(helper["qualified_name"], helper["declaration_hash"])
    return index


def inventory_hash(commit: str, qualified: str) -> str | None:
    repository = _history_repository()
    key = _historical_key(repository, commit) if repository is not None else None
    if key is not None:
        index = _inventory_index(*key)
        if index is not None:
            return index.get(qualified)
    data = json.loads(source_at(commit, "meta/library_helper_inventory.json"))
    for helper in data.get("helpers", []):
        if helper["qualified_name"] == qualified:
            return helper["declaration_hash"]
    return None


def doc_block(src: str, name: str) -> str | None:
    """Raw text of the comment that immediately precedes `Definition name`."""
    match = re.search(rf"^Definition\s+{re.escape(name)}" + INV.IDENT_END, src, re.M)
    if not match:
        return None
    head = src[:match.start()].rstrip()
    if not head.endswith("*)"):
        return None
    return head[head.rfind("(**"):]


def manifest_rows(commit: str | None) -> tuple[dict, dict]:
    rows: dict[str, list[dict]] = {}
    overlays = {}
    for corpus, paths in REG.CORPORA.items():
        manifest = json.loads(source_at(commit, "meta/" + paths["manifest"]))
        legs = json.loads(source_at(commit, "meta/" + paths["overlay"]))
        overlays[corpus] = legs.get("entries", {})
        for row in manifest["rows"]:
            if row.get("formal_name"):
                rows.setdefault(row["formal_name"], []).append({"_corpus": corpus, **row})
    return rows, overlays


def rows_for_object(rows: dict, obj: dict) -> list[dict]:
    package = obj["path"].split("/", 1)[0]
    return [row for row in rows.get(obj["name"], [])
            if row.get("repo") == package
            and ("corpus" not in obj or row["_corpus"] == obj["corpus"])]


def module_for_path(path: str, namespaces: dict | None = None) -> str:
    package, relative = path.split("/theories/", 1)
    namespaces = {"base": "GTBase", "atlas": "Atlas", **REG.NS, **(namespaces or {})}
    return namespaces[package] + "." + relative[:-2].replace("/", ".")


def additional_statement_names(spec: dict) -> set[str]:
    names = spec.get("additional_statements", [])
    if (not isinstance(names, list)
            or any(not isinstance(name, str)
                   or not re.fullmatch(rf"{IDENT}(?:\.{IDENT})+", name) for name in names)
            or len(names) != len(set(names))):
        raise ValueError("additional_statements must be a list of unique qualified names")
    return set(names)


def statement_ownership_text(source: str) -> str:
    """Mask nested comments and Rocq doubled-quote strings without moving offsets.

    The enrollment lexer is shared with declaration scope attribution. Joint
    scanning matters: comment delimiters inside strings must not hide real
    scope commands, and scope words in strings must not close scopes.
    """
    return INV.scope_mask(source, "additional statement")


def additional_statement_path(qualified: str) -> str:
    """Resolve only known conjecture or supported public-library locations."""
    owners = {namespace: package for package, namespace in INV.repository_namespaces().items()}
    owners.update(GTBase="base", Atlas="atlas", ClassicalLemmas="classical-lemmas")
    namespace, *parts, name = qualified.split(".")
    package = owners.get(namespace)
    if package is None or not parts:
        raise ValueError(f"{qualified}: additional statement needs a known module")
    path = package + "/theories/" + "/".join(parts) + ".v"
    public = public_repository_path(path)
    if parts[0] != "conjectures" and not public:
        raise ValueError(f"{qualified}: unsupported additional statement location")
    if public and Path(path).name.startswith(SKIP_PREFIXES):
        raise ValueError(f"{qualified}: probe sources cannot own additional statements")
    return path


def validate_additional_statements(spec: dict, rows_base: dict, rows_now: dict) -> set[str]:
    """Explicitly reviewed classification, never inferred from a Prop's meaning.

    The initial format deliberately rejects Section/module parameters and
    inferred signatures. The existing source comparison binds the complete
    frozen body to this immutable declaration; kernel mode checks @ endpoints.
    """
    names = additional_statement_names(spec)
    if not names:
        return names
    base = spec["baseline_commit"]
    if (not re.fullmatch(r"[0-9a-f]{40}", base)
            or INV.source_git(ROOT, "cat-file", "-t", base).strip() != "commit"):
        raise ValueError("additional statements require an immutable full baseline commit")
    for qualified in sorted(names):
        path = additional_statement_path(qualified)
        package, name = path.split("/", 1)[0], qualified.rsplit(".", 1)[1]
        project_path = package + "/_CoqProject"
        if rows_base.get(name) or rows_now.get(name):
            raise ValueError(f"{qualified}: additional statement must be outside both corpus manifests")
        related = [obj for obj in spec["frozen"] if obj.get("qualified") == qualified]
        objects = [obj for obj in related if obj.get("kind") == "statement"]
        if any(obj.get("kind") not in {"statement", "original-statement"} for obj in related):
            raise ValueError(f"{qualified}: additional statements require whole statement roles")
        if (len(objects) != 1 or objects[0].get("kind") != "statement"
                or objects[0].get("non_corpus") is not True or "corpus" in objects[0]
                or objects[0].get("path") != path or objects[0].get("name") != name
                or objects[0].get("commit", base) != base
                or not objects[0].get("certificate")):
            raise ValueError(f"{qualified}: additional statement needs one exact non_corpus statement mapping")
        commits = {base}
        for obj in related:
            if (obj.get("non_corpus") is not True or "corpus" in obj
                    or obj.get("path") != path or obj.get("name") != name
                    or not obj.get("certificate")):
                raise ValueError(f"{qualified}: additional statement snapshots need exact non_corpus identity")
            commit = obj.get("commit", base)
            if (not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit)
                    or INV.source_git(ROOT, "cat-file", "-t", commit).strip() != "commit"):
                raise ValueError(f"{qualified}: additional statement snapshots require immutable full commits")
            commits.add(commit)
        # A historical Original is enrolled as the same complete Prop: apply
        # every source/project/shape/scope guard at its own effective commit.
        for commit in (*sorted(commits), None):
            if commit is not None:
                if commit != base and manifest_rows(commit)[0].get(name):
                    raise ValueError(f"{qualified}: additional statement snapshot must be outside historical corpus manifests")
                _, source = INV.regular_source_blob(ROOT, commit, path)
                _, project = INV.regular_source_blob(ROOT, commit, project_path)
            else:
                for relative in (path, project_path):
                    file = ROOT / relative
                    if not file.is_file() or file.resolve() != ROOT.resolve() / relative:
                        raise ValueError(f"{qualified}: current source/project missing or aliased")
                source, project = source_at(None, path), source_at(None, project_path)
            if INV.project_module(path, project) + "." + name != qualified:
                raise ValueError(f"{qualified}: additional statement ownership mismatch")
            clean = statement_ownership_text(source)
            matches = [match for match in DECL_RE.finditer(clean) if match.group(1) == name]
            if (len(matches) != 1 or not re.match(
                    rf"\s*Definition\s+{re.escape(name)}\s*:\s*Prop\s*:=",
                    clean[matches[0].start():])):
                raise ValueError(f"{qualified}: additional statement requires a nullary Definition : Prop")
            prefix, stack = clean[:matches[0].start()], []
            if re.search(r"\bLoad\b", prefix):
                raise ValueError(f"{qualified}: additional statement cannot follow source-splicing Load")
            # Reserved scope keywords may follow Time/Timeout/Redirect or another
            # command on the same line. Scan conservatively: ambiguous command
            # text must fail closed rather than hide an opener behind a wrapper.
            scope_keywords = re.compile(r"\b(?:Module|Section|End)\b")
            scopes = re.compile(rf"(Module(?:\s+Type)?(?:\s+(?:Import|Export))?|Section|End)\s+({IDENT})" + INV.IDENT_END)
            command_start = 0
            for keyword in scope_keywords.finditer(prefix):
                scope = scopes.match(prefix, keyword.start())
                if scope is None:
                    raise ValueError(f"{qualified}: unsupported Module/Section identifier syntax")
                while INV.sentence_end(prefix, command_start) <= scope.start():
                    command_start = INV.sentence_end(prefix, command_start)
                if prefix[command_start:scope.start()].strip():
                    raise ValueError(f"{qualified}: additional statement must be outside Module/Section scopes; wrapped scope commands are unsupported")
                kind, label = scope.groups()
                if kind == "End":
                    if not stack or stack.pop() != label:
                        raise ValueError(f"{qualified}: unsupported scope structure")
                else:
                    tail = prefix[scope.end():INV.sentence_end(prefix, scope.end())]
                    if not (kind.startswith("Module") and re.fullmatch(
                            rf"\s*:=\s*{IDENT}(?:\.{IDENT})*\s*\.\s*", tail)):
                        stack.append(label)
            if stack:
                raise ValueError(f"{qualified}: additional statement must be outside Module/Section scopes")
    return names


PARAMETRIC_KEYS = frozenset({"qualified", "section", "variables", "parameters", "bindings", "live_shape"})
VARIABLE_COMMAND_RE = re.compile(rf"Variable ({IDENT}) : (\S.*)\.")
SECTION_DECLARATION_RE = re.compile(rf"(Definition|Inductive)\s+({IDENT})(?![A-Za-z0-9_'])")
KERNEL_TYPE_TOKEN_RE = re.compile(rf"\s*(->|\(|\)|{IDENT}(?:\.{IDENT})*)")


def kernel_type_wellformed(text: str) -> bool:
    """Token grammar of reviewed kernel types (no inference, no notation):

    type := app ('->' app)*;  app := atom+;  atom := NAME | '(' type ')'
    where NAME is Prop, Set, Type or a fully qualified identifier. Isolated
    punctuation, digits, holes and scopes are not tokens, so they are rejected.
    """
    tokens, pos = [], 0
    while text[pos:].strip():
        match = KERNEL_TYPE_TOKEN_RE.match(text, pos)
        if match is None:
            return False
        tokens.append(match.group(1))
        pos = match.end()
    index = 0

    def atom() -> bool:
        nonlocal index
        if index < len(tokens) and tokens[index] == "(":
            index += 1
            if not arrows() or index >= len(tokens) or tokens[index] != ")":
                return False
            index += 1
            return True
        if (index < len(tokens) and tokens[index] not in {"(", ")", "->"}
                and (tokens[index] in {"Prop", "Set", "Type"} or "." in tokens[index])):
            index += 1
            return True
        return False

    def application() -> bool:
        if not atom():
            return False
        while index < len(tokens) and tokens[index] not in {")", "->"}:
            if not atom():
                return False
        return True

    def arrows() -> bool:
        nonlocal index
        if not application():
            return False
        while index < len(tokens) and tokens[index] == "->":
            index += 1
            if not application():
                return False
        return True

    return bool(tokens) and arrows() and index == len(tokens)


def scope_tree(clean: str, what: str) -> list[dict]:
    """Every Module/Section scope of a masked file, with its enclosing scope.

    Parametric enrollment only; the nullary scan above is unchanged. The same
    fail-closed command rules apply: wrapped scope keywords and source-splicing
    Load are rejected, `Module M := N.` aliases are not scopes, and every scope
    must be closed. A Module is plain only when its opener is `Module M.`.
    """
    if re.search(r"\bLoad\b", clean):
        raise ValueError(f"{what}: parametric enrollment cannot follow source-splicing Load")
    scope_keywords = re.compile(r"\b(?:Module|Section|End)\b")
    scopes = re.compile(rf"(Module(?:\s+Type)?(?:\s+(?:Import|Export))?|Section|End)\s+({IDENT})" + INV.IDENT_END)
    openers, stack, command_start = [], [], 0
    for keyword in scope_keywords.finditer(clean):
        scope = scopes.match(clean, keyword.start())
        if scope is None:
            raise ValueError(f"{what}: unsupported Module/Section identifier syntax")
        while INV.sentence_end(clean, command_start) <= scope.start():
            command_start = INV.sentence_end(clean, command_start)
        if clean[command_start:scope.start()].strip():
            raise ValueError(f"{what}: wrapped scope commands are unsupported")
        kind, label = scope.groups()
        end = INV.sentence_end(clean, scope.end())
        if kind == "End":
            if not stack or openers[stack[-1]]["label"] != label:
                raise ValueError(f"{what}: unsupported scope structure")
            openers[stack.pop()]["close_start"] = scope.start()
            continue
        tail = clean[scope.end():end]
        if kind.startswith("Module") and re.fullmatch(rf"\s*:=\s*{IDENT}(?:\.{IDENT})*\s*\.\s*", tail):
            continue
        openers.append({"kind": "Section" if kind == "Section" else "Module",
                        "plain": kind == "Module" and re.fullmatch(r"\s*\.\s*", tail) is not None,
                        "label": label, "body_start": end, "close_start": None,
                        "parent": stack[-1] if stack else None})
        stack.append(len(openers) - 1)
    if stack:
        raise ValueError(f"{what}: unclosed Module/Section scope")
    return openers


def scope_chain(openers: list[dict], offset: int) -> list[int]:
    """Indices of the scopes enclosing offset, outermost first."""
    return [index for index, opener in enumerate(openers)
            if opener["body_start"] <= offset < opener["close_start"]]


def unique_label(openers: list[dict], parent: int | None, label: str) -> bool:
    """One opener of any kind with this label directly in the same enclosing scope."""
    return sum(o["parent"] == parent and o["label"] == label for o in openers) == 1


def section_commands(clean: str, start: int, stop: int) -> list[str]:
    """Normalized commands of a masked Section body between start and stop."""
    out, pos = [], start
    while True:
        while pos < stop and clean[pos].isspace():
            pos += 1
        if pos >= stop:
            return out
        end = INV.sentence_end(clean, pos)
        out.append(INV.normalize_space(clean[pos:end]))
        pos = end


def plain_tokens(text: str) -> set[str]:
    return {token for token in QUALIFIED_IDENT_RE.findall(text) if "." not in token}


def parametric_statement_entries(spec: dict) -> dict[str, dict]:
    """Schema of the explicit Section-parametric enrollment list (never inferred)."""
    entries = spec.get("parametric_statements", [])
    if not isinstance(entries, list):
        raise ValueError("parametric_statements must be a list of entries")
    cert_modules = {module_for_path(path, spec.get("namespaces")) for path in spec.get("certificate_files", [])}
    out: dict[str, dict] = {}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != PARAMETRIC_KEYS:
            raise ValueError("parametric_statements entries need exactly the keys " + ", ".join(sorted(PARAMETRIC_KEYS)))
        qualified, section = entry["qualified"], entry["section"]
        if (not isinstance(qualified, str) or not re.fullmatch(rf"{IDENT}(?:\.{IDENT})+", qualified)
                or qualified in out):
            raise ValueError("parametric_statements need unique qualified names")
        name = qualified.rsplit(".", 1)[1]
        if not isinstance(section, str) or not re.fullmatch(IDENT, section):
            raise ValueError(f"{qualified}: parametric statement needs a Section label")
        variables, parameters, bindings = entry["variables"], entry["parameters"], entry["bindings"]
        if (not isinstance(variables, list) or not variables
                or any(not isinstance(text, str) or not VARIABLE_COMMAND_RE.fullmatch(text) for text in variables)):
            raise ValueError(f"{qualified}: parametric statement variables must list the reviewed `Variable NAME : TYPE.` commands")
        if (not isinstance(parameters, list) or not parameters
                or any(not isinstance(p, dict) or set(p) != {"name", "kernel_type"}
                       or not isinstance(p["name"], str) or not re.fullmatch(IDENT, p["name"])
                       or not isinstance(p["kernel_type"], str) for p in parameters)
                or len({p["name"] for p in parameters}) != len(parameters)):
            raise ValueError(f"{qualified}: parametric statement parameters must be unique {{name, kernel_type}} objects")
        for parameter in parameters:
            if not kernel_type_wellformed(parameter["kernel_type"]):
                raise ValueError(f"{qualified}: kernel_type of {parameter['name']} must use only "
                                 "fully qualified names, Prop, Set, Type, arrows and parentheses")
        if (not isinstance(bindings, dict)
                or any(not re.fullmatch(IDENT, key) or not isinstance(args, list)
                       or any(not isinstance(arg, str) or not re.fullmatch(IDENT, arg) for arg in args)
                       for key, args in bindings.items())):
            raise ValueError(f"{qualified}: parametric statement bindings must map declaration names to argument name lists")
        shape = entry["live_shape"]
        if (not isinstance(shape, str) or "." not in shape
                or shape.rsplit(".", 1)[1] != name + "_live_shape"
                or shape.rsplit(".", 1)[0] not in cert_modules):
            raise ValueError(f"{qualified}: live_shape must be <certificate module>.{name}_live_shape")
        out[qualified] = entry
    overlap = set(out) & additional_statement_names(spec)
    if overlap:
        raise ValueError(f"parametric and nullary additional statements must be disjoint: {sorted(overlap)}")
    return out


def parametric_history_guard(base: str) -> None:
    """Forged or rewritten history must not reach parametric enrollment reads."""
    if os.environ.get("GIT_REPLACE_REF_BASE") or os.environ.get("GIT_GRAFT_FILE"):
        raise ValueError("parametric statements do not support replacement or graft environments")
    if INV.source_git(ROOT, "for-each-ref", "--count=1", "refs/replace/").strip():
        raise ValueError("parametric statements do not support replacement refs")
    common = Path(INV.source_git(ROOT, "rev-parse", "--git-common-dir").strip())
    if ((common if common.is_absolute() else ROOT / common) / "info" / "grafts").exists():
        raise ValueError("parametric statements do not support grafts")
    try:
        INV.source_git(ROOT, "merge-base", "--is-ancestor", base, "HEAD")
    except RegistryError:
        raise ValueError("parametric statements require a baseline that is an ancestor of HEAD") from None


def parametric_source_facts(source: str, name: str, entry: dict, what: str) -> dict:
    """Scope, scaffold, parameters and binding keys of one source at one commit."""
    clean = statement_ownership_text(source)
    matches = [match for match in DECL_RE.finditer(clean) if match.group(1) == name]
    if (len(matches) != 1 or not re.match(rf"\s*Definition\s+{re.escape(name)}\s*:\s*Prop\s*:=",
                                          clean[matches[0].start():])):
        raise ValueError(f"{what}: parametric statement requires one Definition : Prop")
    offset = matches[0].start() + len(clean[matches[0].start():]) - len(clean[matches[0].start():].lstrip())
    openers = scope_tree(clean, what)
    chain = scope_chain(openers, offset)
    if (len(chain) != 1 or openers[chain[0]]["kind"] != "Section"
            or openers[chain[0]]["label"] != entry["section"]):
        raise ValueError(f"{what}: parametric statement must lie directly in top-level Section {entry['section']}")
    if not unique_label(openers, None, entry["section"]):
        raise ValueError(f"{what}: Section label {entry['section']} must open exactly one top-level scope")
    variables, types, declarations = [], {}, []
    for text in section_commands(clean, openers[chain[0]]["body_start"], offset):
        variable = VARIABLE_COMMAND_RE.fullmatch(text)
        declaration = SECTION_DECLARATION_RE.match(text)
        if variable:
            variables.append(text)
            types[variable.group(1)] = variable.group(2)
        elif declaration and not (declaration.group(1) == "Inductive" and re.search(r"\bwith\b", text)):
            declarations.append(declaration.group(2))
        else:
            raise ValueError(f"{what}: unsupported Section command {text.split()[0]}")
    if variables != entry["variables"]:
        raise ValueError(f"{what}: Section scaffold differs from the reviewed variables")
    names = [VARIABLE_COMMAND_RE.fullmatch(text).group(1) for text in variables]
    if len(set(names)) != len(names) or set(names) & set(declarations):
        raise ValueError(f"{what}: duplicate Section names")
    for variable in names:
        if plain_tokens(types[variable]) & (set(names) | set(declarations)):
            raise ValueError(f"{what}: dependent Section variable {variable} is unsupported")
    tokens = plain_tokens(INV.normalize_space(clean[offset:INV.sentence_end(clean, offset)]))
    bindings = entry["bindings"]
    if set(bindings) != {declaration for declaration in declarations if declaration in tokens}:
        raise ValueError(f"{what}: bindings must name exactly the referenced same-Section declarations")
    for key, args in bindings.items():
        positions = [names.index(arg) if arg in names else -1 for arg in args]
        if -1 in positions or positions != sorted(set(positions)):
            raise ValueError(f"{what}: binding {key} must apply Section variables in Section order")
    used = [variable for variable in names
            if variable in tokens or any(variable in args for args in bindings.values())]
    if [parameter["name"] for parameter in entry["parameters"]] != used:
        raise ValueError(f"{what}: parameters must be exactly the Section variables the statement uses, "
                         "in Section order")
    return {"variables": names, "declarations": declarations}


def generated_binding(qualified: str, key: str, args: list[str]) -> str:
    return "(@" + qualified.rsplit(".", 1)[0] + "." + key + "".join(" " + arg for arg in args) + ")"


def check_parametric_substitutions(obj: dict, entry: dict, facts: dict, what: str) -> None:
    substitutions = obj.get("substitutions", {})
    if (not isinstance(substitutions, dict)
            or any(not isinstance(k, str) or not isinstance(v, str) for k, v in substitutions.items())):
        raise ValueError(f"{what}: substitutions must map names to text")
    variables, declarations = set(facts["variables"]), set(facts["declarations"])
    for key, args in entry["bindings"].items():
        if substitutions.get(key) != generated_binding(entry["qualified"], key, args):
            raise ValueError(f"{what}: binding {key} must be the generated "
                             f"{generated_binding(entry['qualified'], key, args)}")
    for key, value in substitutions.items():
        if key in entry["bindings"]:
            continue
        if key in variables or key in declarations:
            raise ValueError(f"{what}: substitutions cannot replace Section variable or declaration {key}")
        if plain_tokens(value) & variables:
            raise ValueError(f"{what}: substitution values cannot mention Section variables")


def validate_parametric_statements(spec: dict, rows_base: dict, rows_now: dict) -> set[str]:
    """Explicit Section-parametric whole Props: separate from the nullary list.

    Each entry pins the enclosing Section, its complete Variable scaffold, the
    discharged parameters with kernel types, generated @-bindings and a
    live-shape witness. Checked at the baseline, every snapshot commit and in
    the current tree; kernel mode checks exact discharged types and conversion.
    """
    entries = parametric_statement_entries(spec)
    if not entries:
        return set()
    base = spec["baseline_commit"]
    if (not re.fullmatch(r"[0-9a-f]{40}", base)
            or INV.source_git(ROOT, "cat-file", "-t", base).strip() != "commit"):
        raise ValueError("parametric statements require an immutable full baseline commit")
    parametric_history_guard(base)
    for qualified, entry in sorted(entries.items()):
        path = additional_statement_path(qualified)
        package, name = path.split("/", 1)[0], qualified.rsplit(".", 1)[1]
        project_path = package + "/_CoqProject"
        if rows_base.get(name) or rows_now.get(name):
            raise ValueError(f"{qualified}: parametric statement must be outside both corpus manifests")
        related = [obj for obj in spec["frozen"] if obj.get("qualified") == qualified]
        if any(obj.get("kind") not in STATEMENT_KINDS for obj in related):
            raise ValueError(f"{qualified}: parametric statements require whole statement roles")
        rows = [obj for obj in related if obj.get("kind") == "statement"]
        snapshots = [obj for obj in related if obj.get("kind") == "original-statement"]
        for obj in related:
            if (obj.get("non_corpus") is not True or "corpus" in obj or obj.get("path") != path
                    or obj.get("name") != name or not obj.get("certificate")
                    or "." not in str(obj.get("frozen", ""))):
                raise ValueError(f"{qualified}: parametric statement objects need exact non_corpus identity")
        if len(rows) != 1 or rows[0].get("commit", base) != base:
            raise ValueError(f"{qualified}: parametric statement needs one baseline statement mapping")
        by_commit = {base: rows[0]}
        for obj in snapshots:
            commit = obj.get("commit")
            if (not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit)
                    or INV.source_git(ROOT, "cat-file", "-t", commit).strip() != "commit"
                    or commit in by_commit):
                raise ValueError(f"{qualified}: parametric snapshots need distinct immutable full commits")
            try:
                INV.source_git(ROOT, "merge-base", "--is-ancestor", commit, base)
            except RegistryError:
                raise ValueError(f"{qualified}: parametric snapshot commit must be an ancestor of the baseline") from None
            by_commit[commit] = obj
        targets = {}
        for commit in (*sorted(by_commit, key=lambda c: c != base), None):
            what = f"{qualified} at {commit[:7] if commit else 'current tree'}"
            if commit is not None:
                if commit != base and manifest_rows(commit)[0].get(name):
                    raise ValueError(f"{qualified}: parametric snapshot must be outside historical corpus manifests")
                _, source = INV.regular_source_blob(ROOT, commit, path)
                _, project = INV.regular_source_blob(ROOT, commit, project_path)
            else:
                for relative in (path, project_path):
                    file = ROOT / relative
                    if not file.is_file() or file.resolve() != ROOT.resolve() / relative:
                        raise ValueError(f"{qualified}: current source/project missing or aliased")
                source, project = source_at(None, path), source_at(None, project_path)
            if INV.project_module(path, project) + "." + name != qualified:
                raise ValueError(f"{qualified}: parametric statement ownership mismatch")
            facts = parametric_source_facts(source, name, entry, what)
            check_parametric_substitutions(by_commit.get(commit, rows[0]), entry, facts, what)
            for key in entry["bindings"]:
                text = find_decl(source, key)["text"]
                if targets.setdefault(key, text) != text:
                    raise ValueError(f"{what}: binding target {key} differs from the baseline")
    return set(entries)


def parametric_reach_errors(spec: dict, entries: dict, sources: set[str], include_public: bool,
                            reaching_base: set[str], reaching_now: set[str]) -> list[str]:
    """Binding targets must not reach migrated sources at any pin (provider-aware)."""
    errors = []
    for qualified, entry in sorted(entries.items()):
        targets = {qualified.rsplit(".", 1)[0] + "." + key for key in entry["bindings"]}
        reaching = set(reaching_base) | set(reaching_now) | set(sources)
        for obj in spec["frozen"]:
            if obj.get("qualified") != qualified or obj.get("kind") != "original-statement":
                continue
            rows, _ = manifest_rows(obj["commit"])
            try:
                reaching |= statement_dependencies(obj["commit"], set(sources), rows,
                                                   include_public=include_public,
                                                   additional_statements={qualified})[1]
            except ValueError as exc:
                # An endpoint the sources do not reach at that commit cannot
                # make its referenced companions reach them either.
                if "must be reached" not in str(exc):
                    raise
        if targets & reaching:
            errors.append(f"{qualified}: binding targets reach migrated sources and would be live chains: "
                          f"{sorted(targets & reaching)}")
    return errors


def parametric_probe(entry: dict, frozen: str, certificate: str, with_live: bool) -> list[str]:
    """Exact discharged types, the pointwise certificate and live-shape conversion.

    Every endpoint is @-applied, so no implicit argument can be instantiated;
    Prop is not a product, so no discharged parameter can be absorbed.
    """
    binders = " ".join(f"({p['name']} : {p['kernel_type']})" for p in entry["parameters"])
    args = " ".join(p["name"] for p in entry["parameters"])
    live, shape = entry["qualified"], entry["live_shape"]
    lines = [f"Check (@{frozen} : forall {binders}, Prop)."]
    if with_live:
        lines += [f"Check (@{live} : forall {binders}, Prop).",
                  f"Check (@{shape} : forall {binders}, Prop).",
                  f"Check (fun {binders} => (@Corelib.Init.Logic.eq_refl Prop (@{live} {args})"
                  f" : @Corelib.Init.Logic.eq Prop (@{live} {args}) (@{shape} {args})))."]
    lines.append(f"Check (@{certificate} : forall {binders}, @{frozen} {args} <-> @{live} {args}).")
    return lines


def section_copy_problem(clean: str, name: str, module: str | None, entry: dict, what: str) -> str | None:
    """Placement of a frozen copy (module given) or live-shape witness (top level)."""
    try:
        openers = scope_tree(clean, what)
    except ValueError as exc:
        return str(exc)
    label = entry["section"]
    candidates = []
    for match in DECL_RE.finditer(clean):
        if match.group(1) != name:
            continue
        offset = match.start() + len(clean[match.start():]) - len(clean[match.start():].lstrip())
        chain = scope_chain(openers, offset)
        shape = [(openers[i]["kind"], openers[i]["label"]) for i in chain]
        if shape == ([("Module", module)] if module else []) + [("Section", label)]:
            candidates.append((offset, chain))
    if len(candidates) != 1:
        return f"expected one {name} directly in Section {label}" + (f" of module {module}" if module else " at top level")
    offset, chain = candidates[0]
    section = openers[chain[-1]]
    if module and (not openers[chain[0]]["plain"] or not unique_label(openers, None, module)):
        return f"module {module} must be a plain unique top-level Module"
    if not unique_label(openers, section["parent"], label):
        return f"Section label {label} must open exactly one scope in its enclosing scope"
    commands = section_commands(clean, section["body_start"], section["close_start"])
    declaration = INV.normalize_space(clean[offset:INV.sentence_end(clean, offset)])
    if commands != [*entry["variables"], declaration]:
        return f"Section {label} must hold exactly the reviewed variables followed by {name}"
    if not re.match(rf"Definition {re.escape(name)} : Prop :=", declaration):
        return f"{name} must be a Definition : Prop"
    return None


def parametric_copy_checks(spec: dict, entries: dict, check) -> None:
    """Frozen copies and live-shape witnesses sit in their reviewed Section scaffolds."""
    base = spec["baseline_commit"]
    certificate_paths = {module_for_path(path, spec["namespaces"]): path for path in spec["certificate_files"]}
    for obj in spec["frozen"]:
        entry = entries.get(obj.get("qualified"))
        if entry is None:
            continue
        module, _, name = obj["frozen"].rpartition(".")
        problem = section_copy_problem(statement_ownership_text(source_at(None, obj["frozen_path"])),
                                       name, module, entry, obj["frozen_path"])
        check(problem is None, f"{obj['qualified']}: frozen copy {obj['frozen']} lies in its Section scaffold",
              problem or "")
    for qualified, entry in sorted(entries.items()):
        module, _, name = entry["live_shape"].rpartition(".")
        source = source_at(None, certificate_paths[module])
        problem = section_copy_problem(statement_ownership_text(source), name, None, entry,
                                       certificate_paths[module])
        check(problem is None, f"{qualified}: live-shape witness {name} lies in its top-level Section scaffold",
              problem or "")
        short = qualified.rsplit(".", 1)[1]
        original = find_decl(source_at(base, additional_statement_path(qualified)), short)["text"]
        substitutions = {key: generated_binding(qualified, key, args) for key, args in entry["bindings"].items()}
        substitutions[short] = name
        expected = substitute(original, substitutions)
        try:
            actual = find_decl(source, name)["text"]
        except ValueError as exc:
            actual = str(exc)
        check(actual == expected, f"{qualified}: live-shape witness matches the original modulo generated bindings",
              "" if actual == expected else f"expected: {expected} | witness: {actual}")


def statement_dependencies(base: str | None, sources: set[str], rows: dict, *,
                           include_public: bool = False,
                           additional_statements: set[str] = frozenset(),
                           provider_context: ProviderContext | None = None) -> tuple[set[str], set[str]]:
    """Discover baseline statement consumers independently of the frozen list.

    Read build-listed conjecture declarations, resolve same-file names first,
    then qualified suffixes / unambiguous short names. Ambiguous imported short
    names conservatively add all candidates. This can request extra review for
    ambiguous explicit references. Notation and constructor resolution still
    require the separate kernel dependency checks and independent review.

    Explicit public sources also need public intermediary nodes, including
    build-listed ClassicalLemmas siblings outside conjecture directories. This indexes
    declaration bodies, not proof terms or every internal module, and does not
    enroll those nodes as sources or add them to the helper debt inventory.
    """
    include_public = include_public or any(
        public_repository_path(additional_statement_path(name)) for name in additional_statements)
    paths = (git("ls-tree", "-r", "--name-only", base).splitlines() if base is not None
             else sorted(set(git("ls-files", "--cached", "--others", "--exclude-standard").splitlines())))
    context = provider_context if provider_context is not None else ProviderContext(base)
    projects, nodes, node_packages, short_names = {}, {}, {}, defaultdict(set)
    node_paths = {}
    for path in paths:
        public = public_repository_path(path)
        if not path.endswith(".v") or not ("/theories/conjectures/" in path or include_public and public):
            continue
        if Path(path).name.startswith(SKIP_PREFIXES):
            continue
        package = path.split("/", 1)[0]
        if package not in projects:
            project_path = package + "/_CoqProject"
            project = (INV.regular_source_blob(ROOT, base, project_path)[1]
                       if include_public and public and base is not None else source_at(base, project_path))
            projects[package] = INV.project_sources(project)[0]
        if path.split("/", 1)[1] not in projects[package]:
            continue
        if public and include_public:
            if base is not None:
                INV.regular_source_blob(ROOT, base, path)
                _, project = INV.regular_source_blob(ROOT, base, package + '/_CoqProject')
            else:
                project = source_at(None, package + '/_CoqProject')
            module = INV.project_module(path, project)
        else:
            module = module_for_path(path)
        for decl in declarations(source_at(base, path)):
            if decl["module"] is None:
                qualified = module + "." + decl["name"]
                nodes[qualified] = (module, decl)
                node_packages[qualified] = package
                node_paths[qualified] = path
                short_names[decl["name"]].add(qualified)
    if include_public and sources - set(nodes):
        raise RegistryError(f"source declarations missing from baseline dependency index: {sorted(sources - set(nodes))}")
    reverse, forward = defaultdict(set), defaultdict(set)
    unrestricted = set()
    for qualified, (module, decl) in nodes.items():
        for token in QUALIFIED_IDENT_RE.findall(body_after_name(decl)):
            if "." in token:
                candidates = {name for name in short_names[token.rsplit(".", 1)[-1]]
                              if name == token or name.endswith("." + token)}
            elif module + "." + token in nodes:
                candidates = {module + "." + token}
            else:
                candidates = short_names[token]
            for dependency in candidates:
                reverse[dependency].add(qualified)
                forward[qualified].add(dependency)
                if "." in token or module + "." + token in nodes:
                    unrestricted.add((qualified, dependency))

    def eligible(consumer: str, dependency: str) -> bool:
        return ((consumer, dependency) in unrestricted
                or context.possible(node_paths[consumer], node_paths[dependency]))

    # Evaluate the same edge predicate only along source-reachable paths. In
    # particular, unrelated declarations need not inspect their project context.
    reached, pending = set(sources), sorted(sources)
    while pending:
        dependency = pending.pop()
        for consumer in sorted(reverse[dependency] - reached):
            if eligible(consumer, dependency):
                reached.add(consumer)
                pending.append(consumer)
    if additional_statements & sources or additional_statements - (reached & set(nodes)):
        raise ValueError("additional statements must be reached from migrated sources and cannot be source helpers")
    statements = {name for name in reached if name in nodes and
            (name.rsplit(".", 1)[-1].endswith("_statement") or
             any(row.get("repo") == node_packages[name]
                 for row in rows.get(name.rsplit(".", 1)[-1], [])))}
    statements.update(additional_statements)
    ancestors, pending = set(statements), sorted(statements)
    while pending:
        consumer = pending.pop()
        # Every intermediary on a source-to-statement path is already reached.
        for dependency in sorted((forward[consumer] & reached) - ancestors):
            if eligible(consumer, dependency):
                ancestors.add(dependency)
                pending.append(dependency)
    return statements, reached & ancestors


def affected_statements(base: str, sources: set[str], rows: dict) -> set[str]:
    return statement_dependencies(base, sources, rows)[0]


def migrated_registry_sources(entry: dict) -> set[str]:
    classes = list(entry.get("semantic_classes", {}).values())
    migrated = [group for group in classes if group.get("state", "").startswith("migrated")]
    return ({name for group in migrated for name in group.get("members", [])}
            if migrated else set(entry.get("source_definitions", [])))


def certificate_endpoints(declaration: str, obj: dict, frozen_module: str) -> bool:
    """A textual cross-check only: exact statement types are checked by --kernel."""
    frozen = frozen_module + "." + obj["frozen"]
    live = obj["qualified"]
    tokens = set(QUALIFIED_IDENT_RE.findall(declaration))
    return any(token == frozen or token == obj["frozen"] for token in tokens) and any(
        token == live or token == obj["name"] for token in tokens)


def validate_frozen_kinds(spec: dict) -> None:
    for index, obj in enumerate(spec["frozen"]):
        kind = obj.get("kind")
        if not isinstance(kind, str) or kind not in FROZEN_KINDS:
            raise ValueError(f"frozen[{index}]: unsupported kind {kind!r}; "
                             "use a statement role for complete rows and historical "
                             "for reused nonstatement objects")


def statement_obligations(spec: dict, *, expected_statements: set[str] | None = None,
                          rows_base: dict | None = None,
                          rows_now: dict | None = None) -> tuple[list[dict], list[str]]:
    """Validate roles and identify every complete frozen row, not just its first copy.

    Discovery uses the real baseline declarations and registry sources. Manifest
    matching uses declaration name/package, not phase=filename (e.g. D2chr), and
    deliberately ignores the object's corpus selection when identifying a row.
    Non-corpus consumers are also found by the independent dependency discovery.
    A Prop-valued helper, Record or proof lemma is not thereby a complete row.
    """
    validate_frozen_kinds(spec)
    base = spec["baseline_commit"]
    if rows_base is None:
        rows_base, _ = manifest_rows(base)
    if rows_now is None:
        rows_now, _ = manifest_rows(None)
    additional = validate_additional_statements(spec, rows_base, rows_now)
    parametric = validate_parametric_statements(spec, rows_base, rows_now)
    enrolled = additional | parametric
    reach_errors = []
    if expected_statements is None:
        entry = load_library_registry(ROOT)["primitives"].get(spec["family"], {})
        sources = migrated_registry_sources(entry)
        expected_statements, reaching = statement_dependencies(
            base, sources, rows_base,
            include_public=bool(entry.get("repository_sources")),
            additional_statements=enrolled)
        if enrolled:
            _, reaching_now = statement_dependencies(None, sources, rows_now,
                                                     include_public=bool(entry.get("repository_sources")),
                                                     additional_statements=enrolled)
            if parametric:
                reach_errors = parametric_reach_errors(
                    spec, parametric_statement_entries(spec), sources,
                    bool(entry.get("repository_sources")), reaching, reaching_now)
    objects, errors = [], list(reach_errors)
    for obj in spec["frozen"]:
        identity = module_for_path(obj["path"], spec["namespaces"]) + "." + obj["name"]
        if identity != obj["qualified"]:
            errors.append(f"{obj['qualified']}: source identity matches its path and declaration")
        unselected = {key: value for key, value in obj.items() if key != "corpus"}
        base_matches = rows_for_object(rows_base, unselected)
        live_matches = rows_for_object(rows_now, unselected)
        is_row = identity in expected_statements or bool(base_matches or live_matches)
        is_statement = obj["kind"] in STATEMENT_KINDS
        if is_row and not is_statement:
            errors.append(f"{identity}: complete statement requires statement or original-statement "
                          f"kind, not {obj['kind']}")
        if not (is_row or is_statement):
            # A nonstatement role cannot hide a claimed non-corpus statement.
            if "non_corpus" in obj:
                errors.append(f"{identity}: non_corpus is only valid on statement objects")
            continue
        objects.append(obj)
        non_corpus = obj.get("non_corpus", False)
        if (not isinstance(non_corpus, bool)
                or ("corpus" in obj and obj["corpus"] not in ("opg", "v2"))
                or (non_corpus and "corpus" in obj)):
            errors.append(f"{obj['name']}: corpus selection is valid")
        if non_corpus:
            if rows_base.get(obj["name"]) or rows_now.get(obj["name"]):
                errors.append(f"{obj['name']}: explicitly non-corpus statement has no manifest row")
        elif (len(rows_for_object(rows_base, obj)) != 1
              or len(rows_for_object(rows_now, obj)) != 1):
            errors.append(f"{obj['name']}: complete statement must select one baseline and current corpus row")
    return objects, errors


def check_kernel(spec: dict) -> list[str]:
    """Check statement exact types and all named assumptions; never build packages."""
    try:
        statements, errors = statement_obligations(spec)
    except ValueError as exc:
        return [str(exc)]
    if errors:
        return errors
    parametric = parametric_statement_entries(spec)
    groups = defaultdict(list)
    certificates = defaultdict(set)
    packages = {namespace: package for package, namespace in spec["namespaces"].items()}
    theorem_names = {obj["certificate"] for obj in spec["frozen"] if obj.get("certificate")}
    theorem_names.update(spec.get("extra_certificates", []))
    for name in theorem_names:
        certificates[packages[name.split(".", 1)[0]]].add(name)
    for obj in statements:
        groups[obj["frozen_path"].split("/", 1)[0]].append(obj)
    errors = []
    for package in sorted(certificates):
        objects = groups[package]
        tokens = shlex.split((ROOT / package / "_CoqProject").read_text(), comments=True)
        flags = []
        for index, token in enumerate(tokens[:-2]):
            if token in {"-R", "-Q"}:
                flags.extend(tokens[index:index + 3])
        live_modules = {module for obj in objects if obj["qualified"] in parametric
                        for module in (obj["qualified"].rsplit(".", 1)[0],
                                       parametric[obj["qualified"]]["live_shape"].rsplit(".", 1)[0])}
        imports = sorted({module_for_path(obj["frozen_path"], spec["namespaces"])
                          for obj in objects} | {name.rsplit(".", 1)[0]
                                                for name in certificates[package]} | live_modules)
        body = ["Require " + module + "." for module in imports]
        probed = set()
        for obj in objects:
            frozen = module_for_path(obj["frozen_path"], spec["namespaces"]) + "." + obj["frozen"]
            if obj["qualified"] in parametric:
                body.extend(parametric_probe(parametric[obj["qualified"]], frozen, obj["certificate"],
                                             obj["qualified"] not in probed))
                probed.add(obj["qualified"])
                continue
            if obj["qualified"] in additional_statement_names(spec):
                body.append(f"Check (@{frozen} : Prop).")
                body.append(f"Check (@{obj['qualified']} : Prop).")
            body.append(f"Check ({obj['certificate']} : {frozen} <-> {obj['qualified']}).")
        body.extend(f"Print Assumptions {name}." for name in sorted(certificates[package]))
        with tempfile.TemporaryDirectory(prefix="migration-exact-type-") as tmp:
            probe = Path(tmp) / "migration_exact_type.v"
            probe.write_text("\n".join(body) + "\n")
            proc = subprocess.run(["coqc", *flags, str(probe)], cwd=ROOT / package,
                                  env=ROCQ.environment(), text=True, capture_output=True)
        output = proc.stdout + proc.stderr
        if proc.returncode or "Axioms:" in output or output.count("Closed under the global context") != len(certificates[package]):
            errors.append(f"{package}: statement exact-type/assumptions probe failed: {output[-1600:]}")
    return errors


def body_after_name(decl: dict) -> str:
    """The declaration text after its own name, for reference scans."""
    text = decl["text"]
    match = re.search(rf"(?<![A-Za-z0-9_']){re.escape(decl['name'])}(?![A-Za-z0-9_'])", text)
    return text[match.end():] if match else text


def theory_files() -> list[Path]:
    return sorted(
        p for p in ROOT.glob("*/theories/**/*.v") if not p.name.startswith(SKIP_PREFIXES)
    )


def local_closure(decls: dict[str, dict], name: str) -> set[str]:
    seen, pending = set(), [name]
    while pending:
        current = pending.pop()
        if current in seen or current not in decls:
            continue
        seen.add(current)
        body = decls[current]["text"]
        pending.extend(n for n in decls if n != current and ref_re(n).search(body))
    return seen


def build_report(spec: dict, *, allow_missing_reports: bool = False) -> dict:
    validate_frozen_kinds(spec)
    base = spec["baseline_commit"]
    checks: list[dict] = []

    def check(ok: bool, what: str, detail: str = "") -> None:
        checks.append({"ok": bool(ok), "check": what, "detail": detail})

    registry = load_library_registry(ROOT, allow_missing_reports=allow_missing_reports)["primitives"]
    entry = registry.get(spec["family"], {})
    rows_base, legs_base = manifest_rows(base)
    rows_now, legs_now = manifest_rows(None)
    additional = validate_additional_statements(spec, rows_base, rows_now)
    parametric_entries = parametric_statement_entries(spec)
    parametric = validate_parametric_statements(spec, rows_base, rows_now)
    enrolled = additional | parametric
    repository_sources = entry.get("repository_sources", {})
    INV.repository_source_records(ROOT, entry)
    expected_sources = migrated_registry_sources(entry)
    actual_sources = {obj["qualified"] for obj in spec["frozen"] if obj["kind"] == "source"}
    check(bool(entry) and actual_sources == expected_sources,
          "migrated source coverage matches the registry",
          f"missing={sorted(expected_sources - actual_sources)}; extra={sorted(actual_sources - expected_sources)}")
    check(spec["canonical_name"] == entry.get("canonical_name"), "canonical name matches the registry")
    frozen_modules = {obj["frozen"].split(".", 1)[0] for obj in spec["frozen"] if "." in obj["frozen"]}
    frozen_rows = []
    for obj in spec["frozen"]:
        check(obj["qualified"] == module_for_path(obj["path"], spec["namespaces"]) + "." + obj["name"],
              f"{obj['qualified']}: source identity matches its path and declaration")
        commit = obj.get("commit", base)
        src = source_at(commit, obj["path"])
        try:
            original = find_decl(src, obj["name"])
        except ValueError as exc:
            check(False, f"original {obj['path']}#{obj['name']} at {commit[:7]}", str(exc))
            continue
        cert_src = source_at(None, obj["frozen_path"])
        module, _, frozen_name = obj["frozen"].rpartition(".")
        try:
            frozen = find_decl(cert_src, frozen_name, module or None)
        except ValueError as exc:
            check(False, f"frozen {obj['frozen_path']}#{obj['frozen']}", str(exc))
            continue
        substitutions = dict(obj.get("substitutions", {}))
        expected = substitute(original["text"], substitutions)
        verbatim = expected == frozen["text"]
        check(verbatim, f"frozen copy {obj['frozen']} matches {obj['qualified']} at {commit[:7]}",
              "" if verbatim else f"expected: {expected} | frozen: {frozen['text']}")
        row = {
            "kind": obj["kind"],
            "qualified": obj["qualified"],
            "path": obj["path"],
            "line": original["line"],
            "commit": commit,
            "blob": blob_at(commit, obj["path"]),
            "declaration_sha256": sha256(original["text"]),
            "frozen": f"{obj['frozen_path']}#{obj['frozen']}",
            "frozen_sha256": sha256(frozen["text"]),
            "substitutions": substitutions,
            "verbatim_modulo_substitutions": verbatim,
            "certificate": obj.get("certificate"),
            "row": obj.get("row"),
        }
        if obj["kind"] == "source":
            pin = repository_sources.get(obj['qualified'])
            if pin:
                check(commit == pin['commit'] and obj['path'] == pin['path'],
                      f"{obj['qualified']}: repository source baseline agrees with pin")
                check(inventory_hash(commit, obj['qualified']) is None,
                      f"{obj['qualified']}: repository source cannot replace an inventory source")
                recorded = pin['declaration_hash']
            else:
                recorded = inventory_hash(commit, obj["qualified"])
            check(recorded == row["declaration_sha256"],
                  f"{obj['qualified']} hash equals the baseline {'repository source' if pin else 'inventory'} declaration_hash",
                  f"inventory={recorded}")
            live = find_decl(source_at(None, obj["path"]), obj["name"])
            row["live_text"] = live["text"]
            row["live_sha256"] = sha256(live["text"])
            want = obj.get("live_unfolds_to")
            if want:
                check(live["text"].endswith(f":= {want}."),
                      f"live {obj['qualified']} unfolds to {want}", live["text"])
        frozen_rows.append(row)

    # Certificate theorems are declared where the registry says.
    theorem_names = sorted({o["certificate"] for o in spec["frozen"] if o.get("certificate")}
                           | set(spec.get("extra_certificates", [])))
    cert_decls = {}
    for path in spec["certificate_files"]:
        module = path.split("/theories/", 1)[1][:-2].replace("/", ".")
        namespace = spec["namespaces"][path.split("/", 1)[0]]
        for decl in declarations(source_at(None, path)):
            if decl["module"] is None:
                cert_decls[f"{namespace}.{module}.{decl['name']}"] = decl["text"]
    for name in theorem_names:
        check(name in cert_decls, f"certificate theorem {name} is declared",
              "" if name in cert_decls else "missing")
    registered = {name for primitive in registry.values()
                  for name in primitive.get("api_theorems", []) + primitive.get("compatibility_theorems", [])}
    family_certificates = set(entry.get("compatibility_theorems", []))
    for obj in spec["frozen"]:
        name = obj.get("certificate")
        # Older-family snapshots must remain registered with their original
        # family; primary source/statement bridges belong to this family.
        allowed = family_certificates if obj["kind"] in {"source", "statement"} else registered
        if obj["kind"] != "m1-frozen":
            check(bool(name) and name in allowed, f"{obj['qualified']}: certificate is registered",
                  str(name))
        if name in cert_decls:
            check(certificate_endpoints(cert_decls[name], obj,
                                        module_for_path(obj["frozen_path"], spec["namespaces"])),
                  f"{obj['qualified']}: certificate text names its frozen and live endpoints",
                  "textual correspondence only; use --kernel for closed statement exact types")

    # The frozen chain of each statement covers every same-file declaration
    # through which the statement reaches a source helper.
    sources = [o for o in spec["frozen"] if o["kind"] == "source"]
    source_names = {o["name"] for o in sources}
    chain_names = {o["name"] for o in spec["frozen"] if o["kind"] == "chain"}
    statements = []
    computed_chain: set[str] = set()
    providers: dict[str, set[str]] = defaultdict(set)
    for obj in spec["frozen"]:
        if obj["kind"] in {"source", "chain", "statement"}:
            providers[obj["name"]].add(obj["path"])
    baseline_context, current_context = ProviderContext(base), ProviderContext(None)
    expected_statements, reaching = statement_dependencies(
        base, expected_sources, rows_base, include_public=bool(repository_sources),
        additional_statements=enrolled, provider_context=baseline_context)
    reaching_now: set[str] = set()
    if enrolled:
        _, reaching_now = statement_dependencies(None, expected_sources, rows_now,
                                                 include_public=bool(repository_sources),
                                                 additional_statements=enrolled,
                                                 provider_context=current_context)
    _, role_errors = statement_obligations(
        spec, expected_statements=expected_statements, rows_base=rows_base, rows_now=rows_now)
    for error in role_errors:
        check(False, error)
    supplied_statements = {obj["qualified"] for obj in spec["frozen"] if obj["kind"] == "statement"}
    check(expected_statements == supplied_statements,
          "affected statement coverage matches baseline dependencies",
          f"missing={sorted(expected_statements - supplied_statements)}; extra={sorted(supplied_statements - expected_statements)}")
    if repository_sources or enrolled:
        frozen_chain = {obj['qualified'] for obj in spec['frozen'] if obj['kind'] in {'source', 'chain'}}
        missing_chain = reaching - expected_statements - frozen_chain
        label = ("public source paths" if repository_sources else "additional statement paths")
        check(not missing_chain, label + " have complete frozen intermediary coverage",
              f"missing={sorted(missing_chain)}")
    if parametric:
        reach_errors = parametric_reach_errors(spec, parametric_entries, expected_sources,
                                               bool(repository_sources), reaching, reaching_now)
        for qualified in sorted(parametric):
            problems = [error for error in reach_errors if error.startswith(qualified + ":")]
            check(not problems, f"{qualified}: binding targets do not reach migrated sources at any pin",
                  "; ".join(problems))
        parametric_copy_checks(spec, parametric_entries, check)
    for obj in (o for o in spec["frozen"] if o["kind"] == "statement"):
        base_src, live_src = source_at(base, obj["path"]), source_at(None, obj["path"])
        decls = {d["name"]: d for d in declarations(base_src) if d["module"] is None}
        closure = local_closure(decls, obj["name"])
        reaches = {n for n in closure if local_closure(decls, n) & source_names}
        affected = sorted(reaches - {obj["name"]})
        computed_chain.update(affected)
        for name in affected:
            providers[name].add(obj["path"])
        frozen_here = {o["name"] for o in spec["frozen"]
                       if o["path"] == obj["path"] and o["kind"] in {"source", "chain"}
                       and o.get("commit", base) == base}
        check(set(affected) <= frozen_here,
              f"{obj['qualified']}: frozen chain covers {affected}",
              f"not frozen: {sorted(set(affected) - frozen_here)}")
        text_same = find_decl(base_src, obj["name"])["text"] == \
            find_decl(live_src, obj["name"])["text"]
        check(text_same, f"{obj['qualified']}: statement text unchanged since baseline")
        doc_same = doc_block(base_src, obj["name"]) == doc_block(live_src, obj["name"])
        check(doc_same and doc_block(live_src, obj["name"]) is not None,
              f"{obj['qualified']}: doc block unchanged since baseline")
        formal = obj["name"]
        base_rows, now_rows = rows_for_object(rows_base, obj), rows_for_object(rows_now, obj)
        non_corpus = obj.get("non_corpus", False)
        check(isinstance(non_corpus, bool)
              and ("corpus" not in obj or obj["corpus"] in ("opg", "v2"))
              and not (non_corpus and "corpus" in obj),
              f"{formal}: corpus selection is valid")
        if non_corpus:
            check(not rows_base.get(formal) and not rows_now.get(formal),
                  f"{formal}: explicitly non-corpus statement has no manifest row")
        else:
            check(len(now_rows) == 1 and base_rows == now_rows,
                  f"{formal}: manifest row unchanged since baseline",
                  f"{len(base_rows)} baseline / {len(now_rows)} current rows")
        row_now = now_rows[0] if now_rows else {}
        slug = row_now.get("slug")
        corpus = row_now.get("_corpus")
        if not non_corpus:
            before_legs, now_legs = legs_base.get(corpus, {}), legs_now.get(corpus, {})
            check(slug in before_legs and before_legs.get(slug) == now_legs.get(slug),
                  f"{formal}: leg-state entry unchanged since baseline")
        statements.append({
            "qualified": obj["qualified"],
            "row_id": row_now.get("row_id") or (f"opg:{slug}" if corpus == "opg" else "no corpus row"),
            "corpus": corpus,
            "non_corpus": non_corpus,
            "slug": slug,
            "phase": row_now.get("phase"),
            "status": row_now.get("status"),
            "legs": row_now.get("legs"),
            "chain": affected,
            "certificate": obj.get("certificate"),
            "original_certificate": obj.get("original_certificate"),
            "declaration_sha256": sha256(find_decl(base_src, obj["name"])["text"]),
            "doc_block_sha256": sha256(doc_block(live_src, obj["name"]) or ""),
            "doc_block_unchanged": doc_same,
            "statement_text_unchanged": text_same,
        })
        if obj["qualified"] in parametric_entries:
            parametric_entry = parametric_entries[obj["qualified"]]
            statements[-1].update({
                "section": parametric_entry["section"],
                "parameters": parametric_entry["parameters"],
                "variables_sha256": sha256("\n".join(parametric_entry["variables"])),
                "bindings": parametric_entry["bindings"],
                "live_shape": parametric_entry["live_shape"],
            })

    # Frozen bodies anywhere in the migration layer that still resolve through
    # a live helper or chain declaration of this family.
    # Computed chains, not only the spec's list, so a missing freeze cannot hide.
    # Enrolled parametric endpoints resolve through this family's helpers too;
    # an earlier family's frozen body that applies one of them live is stale.
    live_names = source_names | chain_names | computed_chain | {name.rsplit(".", 1)[1] for name in parametric}
    stale = []
    for path in sorted(ROOT.glob("*/theories/migration/*.v")):
        rel = path.relative_to(ROOT).as_posix()
        for decl in declarations(path.read_text()):
            if decl["module"] is None:
                continue
            hits = sorted(n for n in live_names if any(
                not frozen_reference(match.group(), frozen_modules)
                and current_context.reference(rel, match.group(), providers[n])
                for match in ref_re(n).finditer(body_after_name(decl))))
            if hits:
                stale.append({"frozen": f"{rel}#{decl['module']}.{decl['name']}",
                              "resolves_through_live": hits,
                              "documented": f"{rel}#{decl['module']}.{decl['name']}"
                              in spec.get("known_stale_snapshots", {})})
    for entry in stale:
        check(entry["documented"], f"{entry['frozen']} resolves through live "
              f"{entry['resolves_through_live']}", "documented limitation"
              if entry["documented"] else "undocumented stale snapshot")

    # Repository-wide references to the family's names, and canonical users.
    tracked = sorted(live_names | {o["name"] for o in spec["frozen"]
                                                   if o["kind"] == "statement"})
    patterns = {name: ref_re(name) for name in tracked}
    canonical = spec["canonical_short_name"]
    canonical_re = ref_re(canonical)
    consumers, canonical_users = [], []
    for path in theory_files():
        rel = path.relative_to(ROOT).as_posix()
        src = path.read_text()
        # Cheap raw prefilter: most files (e.g. digraph certificates) mention none.
        if not any(name in src for name in (*tracked, canonical)):
            continue
        clean = INV.strip_comments(src)
        decls = declarations(src)
        for name, pattern in patterns.items():
            declared_here = any(d["name"] == name and d["module"] is None for d in decls)
            for match in pattern.finditer(clean):
                if frozen_reference(match.group(), frozen_modules):
                    continue
                if not declared_here and not current_context.reference(rel, match.group(), providers[name]):
                    continue
                line = clean.count("\n", 0, match.start()) + 1
                owner = next((d for d in reversed(decls) if d["line"] <= line), None)
                owner_name = (f"{owner['module']}.{owner['name']}" if owner and owner["module"]
                              else owner["name"] if owner else None)
                if owner and owner["name"] == name and owner["line"] == line:
                    continue
                consumers.append({"name": name, "path": rel, "line": line, "in": owner_name,
                                  "declared_here": declared_here})
        if canonical_re.search(clean) and "/migration/" not in rel:
            try:
                before = INV.strip_comments(source_at(base, rel))
            except subprocess.CalledProcessError:
                before = ""
            canonical_users.append({"path": rel, "at_baseline": bool(canonical_re.search(before))})
    dedup = {(c["name"], c["path"], c["in"]): c for c in consumers}
    consumers = sorted(dedup.values(), key=lambda c: (c["path"], c["line"], c["name"]))
    for c in consumers:
        declared_here = c.pop("declared_here", False)
        c["class"] = ("migration certificate" if "/migration/" in c["path"]
                      else "same-file" if declared_here
                      else "cross-module")
    declared_cross = {(c["path"], c["name"]) for c in spec.get("cross_module_consumers", [])}
    for c in consumers:
        if c["class"] == "cross-module":
            check((c["path"], c["name"]) in declared_cross,
                  f"cross-module consumer {c['path']}:{c['line']} ({c['name']}) is declared")

    # Distinct name matches stay untouched.
    for item in spec.get("distinct_variants", []):
        base_text = find_decl(source_at(base, item["path"]), item["name"])["text"]
        live_text = find_decl(source_at(None, item["path"]), item["name"])["text"]
        check(base_text == live_text, f"distinct variant {item['qualified']} unchanged")
        item["declaration_sha256"] = sha256(live_text)

    return {
        "schema_version": 1,
        "family": spec["family"],
        "canonical_name": spec["canonical_name"],
        "relation": spec["relation"],
        "baseline_commit": base,
        "frozen": frozen_rows,
        "statements": statements,
        "stale_snapshots": stale,
        "known_stale_snapshots": spec.get("known_stale_snapshots", {}),
        "consumers": consumers,
        "cross_module_consumers": spec.get("cross_module_consumers", []),
        "canonical_users": sorted(canonical_users, key=lambda u: u["path"]),
        "distinct_variants": spec.get("distinct_variants", []),
        "provider_context_fallbacks": baseline_context.diagnostics() + current_context.diagnostics(),
        "checks": checks,
        "ok": all(c["ok"] for c in checks),
        "validation_limits": [
            "Default checks compare source text, registry coverage and conservative lexical dependencies; they do not prove theorem types.",
            "Bare provider attribution assumes repository namespaces come exclusively from declared project roots; external libraries must not inject or shadow them. Unknown loader/project contexts retain all lexical candidates; source auditing does not certify an ambient compiler installation.",
            "--kernel checks exact closed statement equivalences and assumptions of every named certificate/API theorem, using already-built modules.",
            ("Dependency discovery also scans build-listed public base/foundation declarations for explicitly enrolled repository sources; it does not resolve notation, constructor names, module aliases or Section context like Rocq."
             if repository_sources else
             "Dependency discovery scans build-listed conjecture declarations, including Inductive and Record bodies; it does not resolve notation, constructor names, module aliases or Section context like Rocq."),
            "Helper exact types, Section scaffolding and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.",
        ] + ([
            "Section-parametric endpoints: default checks pin the enclosing Section, its complete Variable scaffold, the parameter names, generated bindings, frozen-copy and live-shape placement and text; --kernel checks exact discharged types, the pointwise certificate and conversion of the live endpoint with its live-shape witness. Dependent scaffolds, other Section commands, frozen Section companions and Section-parametric chains are unsupported.",
        ] if parametric else []),
    }


def render_markdown(report: dict, spec: dict) -> str:
    """The only committed output: short summary plus per-row bridge index."""
    family = spec["report_name"]
    sources = [row for row in report["frozen"] if row["kind"] == "source"]
    lines = [
        f"# Migration report: {report['family']}", "",
        f"Inputs: `meta/migration_reports/{family}.spec.json` and "
        f"`meta/library_primitives/{report['family']}.json`.",
        f"Regenerate: `python3 meta/migration_report.py {family} --write`.",
        f"Full evidence: `python3 meta/migration_report.py {family} --details /tmp/migration-details`.", "",
        f"- Canonical: `{report['canonical_name']}`.",
        f"- Baseline: `{report['baseline_commit']}`.",
        f"- Scope: {len(sources)} helpers, {len(report['statements'])} statements, "
        f"{len(report['frozen'])} frozen objects, {len(report['consumers'])} recorded references.",
        f"- Source checks: {sum(c['ok'] for c in report['checks'])}/{len(report['checks'])} pass; "
        f"{'consistent' if report['ok'] else 'FAILED'}.", "",
        "| Statement / corpus row | Compatibility theorem |", "|---|---|",
    ]
    for statement in report["statements"]:
        lines.append(f"| `{statement['qualified']}` / {statement['row_id']} "
                     f"| `{statement['certificate']}` |")
    parametric = [statement for statement in report["statements"] if "parameters" in statement]
    if parametric:
        lines += ["", "Section-parametric endpoints (pointwise certificates over every discharged parameter): "
                  + ", ".join(f"`{statement['qualified']}` ("
                              + ", ".join(parameter["name"] for parameter in statement["parameters"]) + ")"
                              for statement in parametric) + "."]
    lines += ["", "Source checks compare frozen text, registry and statement coverage, "
              "bridge endpoints, and unchanged statement metadata. They do not prove theorem types.",
              f"`python3 meta/migration_report.py {family} --check --kernel` checks exact closed "
              "statement equivalences and all named theorem assumptions in already-built modules.",
              "Helper types, Section context, notation/constructor resolution and compiled dependency "
              "closure still require independent review and family-specific Section and kernel dependency evidence."]
    if report["distinct_variants"]:
        lines += ["", "Excluded distinct variants: " + ", ".join(
            f"`{item['qualified']}`" for item in report["distinct_variants"]) + "."]
    if report["known_stale_snapshots"]:
        lines += ["", "Prior snapshot limitations (explanations and replacement certificates in the inputs): "
                  + ", ".join(f"`{name}`" for name in report["known_stale_snapshots"]) + "."]
    for check in report["checks"]:
        if not check["ok"]:
            lines.append(f"- FAILED: {check['check']}: {check['detail']}")
    return "\n".join(lines) + "\n"


def render_details(report: dict, spec: dict) -> str:
    lines = [
        f"# Migration report: {report['family']}",
        "",
        "> Generated by `python3 meta/migration_report.py "
        f"{spec['report_name']} --details DIRECTORY` from "
        f"`meta/migration_reports/{spec['report_name']}.spec.json`; do not edit by hand.",
        "",
        f"- Canonical definition: `{report['canonical_name']}`",
        f"- Relation of every frozen helper to the canonical: {report['relation']}",
        f"- Baseline (frozen-from) commit: `{report['baseline_commit']}`",
        f"- Verification: {sum(c['ok'] for c in report['checks'])} of "
        f"{len(report['checks'])} checks pass" + ("" if report["ok"] else " (FAILED)"),
        "",
    ]
    lines += spec.get("summary", [])
    lines += ["", "## What these checks establish", ""]
    lines += ["- " + limitation for limitation in report["validation_limits"]]
    lines += ["", "## Source definitions", "",
              "| Source definition | Original (path:line) | Original declaration sha256 | "
              "Git blob at baseline | Frozen copy | Live body | Compatibility theorem |",
              "|---|---|---|---|---|---|---|"]
    for row in (r for r in report["frozen"] if r["kind"] == "source"):
        live = row["live_text"].split(":=", 1)[1].strip().rstrip(".")
        lines.append(
            f"| `{row['qualified']}` | {row['path']}:{row['line']} | `{row['declaration_sha256']}` "
            f"| `{row['blob']}` | `{row['frozen'].split('#', 1)[1]}` "
            f"{'(verbatim)' if row['verbatim_modulo_substitutions'] else '(MISMATCH)'} "
            f"| `{live}` | `{row['certificate']}` |")
    lines += ["", "## Affected statements (per-row certificates)", "",
              "| Row | Phase | Statement | Status | Statement leg | Frozen chain | "
              "Per-row equivalence theorem | Statement text and doc block |",
              "|---|---|---|---|---|---|---|---|"]
    for st in report["statements"]:
        chain = ", ".join(f"`{n}`" for n in st["chain"])
        cert = f"`{st['certificate']}`"
        if st.get("original_certificate"):
            cert += f"; end-to-end `{st['original_certificate']}`"
        lines.append(
            f"| {st['row_id']} | {st['phase']} | `{st['qualified']}` | {st['status']} "
            f"| {(st['legs'] or {}).get('statement')} | {chain} | {cert} "
            f"| {'unchanged' if st['statement_text_unchanged'] and st['doc_block_unchanged'] else 'CHANGED'} |")
    parametric = [st for st in report["statements"] if "parameters" in st]
    if parametric:
        lines += ["", "## Section-parametric endpoints", "",
                  "| Statement | Section | Discharged parameters (kernel types) | Generated bindings | Live-shape witness |",
                  "|---|---|---|---|---|"]
        for st in parametric:
            parameters = ", ".join(f"`{p['name']} : {p['kernel_type']}`" for p in st["parameters"])
            bindings = ", ".join(f"`{key}` ({' '.join(args) or 'none'})"
                                 for key, args in sorted(st["bindings"].items())) or "none"
            lines.append(f"| `{st['qualified']}` | `{st['section']}` | {parameters} | {bindings} "
                         f"| `{st['live_shape']}` |")
    lines += ["", "## Frozen objects", "",
              "Each frozen copy equals the original declaration after comment stripping, "
              "whitespace normalization and the listed identifier substitutions.", "",
              "| Kind | Original | Commit | Original sha256 | Frozen copy | Frozen sha256 | "
              "Substitutions | Certificate |",
              "|---|---|---|---|---|---|---|---|"]
    for row in report["frozen"]:
        subst = ", ".join(f"`{k}` → `{v}`" for k, v in sorted(row["substitutions"].items())) or "none"
        lines.append(
            f"| {row['kind']} | `{row['qualified']}` | `{row['commit'][:7]}` "
            f"| `{row['declaration_sha256'][:16]}…` | `{row['frozen']}` "
            f"| `{row['frozen_sha256'][:16]}…` | {subst} | "
            f"{'`' + row['certificate'] + '`' if row['certificate'] else '-'} |")
    lines += ["", "## Frozen snapshots that resolve through live helpers of this family", ""]
    if not report["stale_snapshots"]:
        lines.append("None.")
    for entry in report["stale_snapshots"]:
        note = report["known_stale_snapshots"].get(entry["frozen"], "UNDOCUMENTED")
        lines.append(f"- `{entry['frozen']}` resolves through live "
                     f"{', '.join('`' + n + '`' for n in entry['resolves_through_live'])}. {note}")
    lines += ["", "## Repository-wide consumers", "",
              "Every reference to a source helper, frozen chain declaration or affected "
              "statement outside its own declaration.", "",
              "| Name | File:line | Enclosing declaration | Class |", "|---|---|---|---|"]
    for c in report["consumers"]:
        lines.append(f"| `{c['name']}` | {c['path']}:{c['line']} | `{c['in']}` | {c['class']} |")
    lines += ["", "### Cross-module consumers", ""]
    for c in report["cross_module_consumers"]:
        lines.append(f"- {c['path']} (`{c['name']}`): {c['note']}")
    lines += ["", "## Direct users of the canonical definition", ""]
    lines += [f"- {u['path']}: " + ("user at the baseline" if u["at_baseline"]
              else "new user through its redirected alias") for u in report["canonical_users"]]
    lines += ["", "## Distinct name matches (not claimed, not redirected)", ""]
    for item in report["distinct_variants"]:
        lines.append(f"- `{item['qualified']}` (sha256 `{item['declaration_sha256'][:16]}…`, "
                     "unchanged)" + (f": {item['note']}" if "note" in item else ""))
    lines += ["", "## Checks", ""]
    lines += [f"- [{'x' if c['ok'] else ' '}] {c['check']}" + (f" ({c['detail']})" if c["detail"]
                                                              and not c["ok"] else "")
              for c in report["checks"]]
    return "\n".join(lines) + "\n"


def self_test(kernel: bool = False) -> int:
    src = ("(* c *)\nModule Legacy.\nDefinition f (G : sgraph) : Prop :=\n  g G. (* x. *)\n"
           "End Legacy.\nDefinition g (G : sgraph) : Prop := True.\n"
           "Lemma f_compat (G : sgraph) : Legacy.f G <-> g G.\nProof. by []. Qed.\n")
    decls = declarations(src)
    ok = [(d["module"], d["name"]) for d in decls] == [
        ("Legacy", "f"), (None, "g"), (None, "f_compat")]
    ok = ok and find_decl(src, "f", "Legacy")["text"] == \
        "Definition f (G : sgraph) : Prop := g G."
    ok = ok and substitute("h (g x) Legacy.g g'", {"g": "Legacy.g"}) == \
        "h (Legacy.g x) Legacy.g g'"
    ok = ok and substitute("a b", {"a": "b", "b": "c"}) == "b c"
    if not ok:
        print("migration-report parser self-test FAILED")
        return 1
    command = [sys.executable, str(ROOT / "meta/test_migration_report.py")]
    if kernel:
        command.append("--kernel")
    return subprocess.run(command, cwd=ROOT).returncode


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("family", nargs="?")
    parser.add_argument("--all", action="store_true", help="process all *.spec.json family specs")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--kernel", action="store_true", help="check exact statement types and assumptions in already-built modules")
    parser.add_argument("--details", type=Path, help="write full JSON and Markdown evidence here, outside the compact report")
    args = parser.parse_args(argv)
    if args.validate:
        return self_test(args.kernel)
    if bool(args.family) == bool(args.all):
        parser.error("choose FAMILY or --all")
    families = ([path.name.removesuffix(".spec.json") for path in sorted(REPORTS.glob("*.spec.json"))]
                if args.all else [args.family])
    if not families:
        parser.error("no migration report specs found")
    if args.all and args.check:
        verbose_json = sorted(path.relative_to(REPORTS).as_posix()
                              for path in REPORTS.rglob("*.json")
                              if not path.name.endswith(".spec.json"))
        if verbose_json:
            print("migration reports: unexpected non-specification JSON in compact report "
                  f"directory: {verbose_json}; keep --details output outside it", file=sys.stderr)
            return 1
    if args.all:
        try:
            registry = load_library_registry(ROOT, allow_missing_reports=args.write)["primitives"]
        except RegistryError as exc:
            print(f"migration registry: ERROR: {exc}", file=sys.stderr)
            return 1
        expected = {Path(entry["migration_report"]).stem for entry in registry.values()
                    if entry.get("migration_report", "").startswith("meta/migration_reports/")}
        missing = expected - set(families)
        if missing:
            print(f"migration report specs missing for registered reports: {sorted(missing)}", file=sys.stderr)
            return 1
    failed = False
    for family in families:
        try:
            failed = process_family(family, args) or failed
        except (KeyError, OSError, ValueError, RegistryError, subprocess.CalledProcessError) as exc:
            print(f"migration report {family}: ERROR: {exc}", file=sys.stderr)
            failed = True
    return int(failed)


def process_family(family: str, args: argparse.Namespace) -> bool:
    if args.details and args.details.resolve().is_relative_to(REPORTS.resolve()):
        raise ValueError("--details must be outside the report directory and its descendants; "
                         "committed reports stay compact")
    spec = json.loads((REPORTS / f"{family}.spec.json").read_text())
    spec["report_name"] = family
    report = build_report(spec, allow_missing_reports=args.write)
    rendered_md = render_markdown(report, spec)
    md_path = REPORTS / f"{family}.md"
    if args.write:
        md_path.write_text(rendered_md)
    if args.details:
        args.details.mkdir(parents=True, exist_ok=True)
        (args.details / f"{family}.json").write_text(
            json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
        (args.details / f"{family}.md").write_text(render_details(report, spec))
    failed = [c for c in report["checks"] if not c["ok"]]
    for c in failed:
        print(f"  FAILED: {c['check']} {c['detail']}".rstrip(), file=sys.stderr)
    if args.check:
        for path, rendered in ((md_path, rendered_md),):
            if not path.exists() or path.read_text() != rendered:
                print(f"  ERROR: {path.relative_to(ROOT)} has drifted; run "
                      f"python3 meta/migration_report.py {family} --write", file=sys.stderr)
                failed.append({"check": "drift"})
    if args.kernel:
        for error in check_kernel(spec):
            print(f"  ERROR: {error}", file=sys.stderr)
            failed.append({"check": "kernel"})
    passed = sum(check["ok"] for check in report["checks"])
    print(f"migration report {family}: {passed} of "
          f"{len(report['checks'])} checks pass; {len(report['frozen'])} frozen objects, "
          f"{len(report['statements'])} statements, {len(report['consumers'])} references; "
          f"{'FAILED' if failed else 'OK'}")
    return bool(failed)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
