#!/usr/bin/env python3
"""Retained aliases: the repository's static reference inventory (G-5).

An alias is a registered family's source definition that is still declared in
the tree. For each alias this computes, under the rules below, three consumer
sets and an implicit-use flag; library_inventory.py renders them as the
generated inventory's `alias_retention` section, so `--check` compares the
committed rows with the computed ones:

  same_file        declarations of the alias's own file that reference it, and
                   the manifest statements of that file whose same-file chain
                   (migration_report.local_closure) reaches it;
  cross_file       every other repository .v file that references it, with the
                   referencing declarations and the statements whose same-file
                   chain reaches one of them (own-certificate files excluded);
  own_certificate  the files of the alias's own family certificate;
  implicit_use     the alias is named in a Notation / Coercion / Hint /
                   Canonical / Instance / Existing Instance / Identity Coercion
                   sentence: it can be consumed without its name.

Rules, per occurrence of the alias's short name in the masked text (comments
and strings blanked, library_inventory.scope_mask) of every .v file under a
repository package's theories/ (grounding_ and implications_ files included):
  1. a Legacy / Original qualifier (migration_report.frozen_reference) is a
     frozen copy: not a consumer;
  2. any other dotted token is a consumer;
  3. a bare token is not a consumer only when it is SHADOWED: after the END of
     a same-named declaration of that file, inside that declaration's Module
     block (or to the end of the file at top level or in a Section);
  4. otherwise it is a consumer iff migration_report.ProviderContext.reference
     holds (always within one package).
Undecided cases count: a file whose scopes cannot be read counts every
occurrence (`undecided`); a file outside every _CoqProject is counted
textually (`unlisted`); so is every reference to an alias whose OWN file is
outside its package's _CoqProject (`provider_unlisted`: rule 4 is not asked).
A ProviderContext fallback is an ERROR of --check unless the data's
alias_retention_exceptions accepts its exact (path, reason) pair; acceptance
suppresses only the error, never a count, and an entry that no longer fires is
stale. A repository namespace without a regular <pkg>/_CoqProject is an error
unless the same data declares it (packages_without_project); the declared set
must equal the observed one. `require_chain` (yes / no / unknown: the file's
transitive Require closure reaches the alias's module) is reported only and
never lowers a count.

This is a static inventory under these rules, not a compiler resolution, and
it says nothing about clients outside this repository.
"""
from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import json
import re

import library_inventory as INV

ROOT = INV.ROOT
IMPLICIT_RE = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Export)\s+)?"
                         r"(?:Notation|Coercion|Hint|Canonical|Instance|Existing\s+Instance|Identity\s+Coercion)\b")
REQUIRE_RE = re.compile(r"(?:From\s+([A-Za-z_][\w'.]*)\s+)?Require\s+(?:(?:Import|Export)\s+)?([A-Za-z_][\w'.]*(?:\s+[A-Za-z_][\w'.]*)*)\s*\.")


def module_files() -> dict[str, str]:
    """Logical module name -> repository path, for every .v under a package's theories/."""
    namespaces = INV.repository_namespaces()
    out = {}
    for path in sorted(ROOT.glob("*/theories/**/*.v")):
        rel = path.relative_to(ROOT)
        package = rel.parts[0]
        if package not in namespaces:
            continue
        parts = (*rel.parts[2:-1], path.stem)
        out[".".join((namespaces[package], *parts))] = rel.as_posix()
    return out


def sentences(masked: str) -> list[tuple[int, int]]:
    spans, start = [], 0
    while start < len(masked):
        end = INV.sentence_end(masked, start)
        spans.append((start, end))
        start = end
    return spans


class FileScan:
    """One masked read of a file, its declarations with spans and modules, and its alias hits."""

    def __init__(self, rel: str, names: set[str]):
        import migration_report as MR
        self.rel = rel
        self.text = (ROOT / rel).read_text()
        try:
            self.masked = INV.scope_mask(self.text, rel)
            modules = [o for o in INV.scope_openers(self.masked) if o["kind"] == "Module"]
            self.undecided = None
        except ValueError as exc:
            self.masked = INV.strip_comments(self.text)
            modules = []
            self.undecided = str(exc)
        self.modules = modules
        self.hits = [(m.start(), m.group()) for m in MR.QUALIFIED_IDENT_RE.finditer(self.masked)
                     if m.group().rsplit(".", 1)[-1] in names]
        self.decls = []
        if self.hits:
            for match in MR.DECL_RE.finditer(self.masked):
                start = self.masked.rfind("\n", 0, match.start(1)) + 1
                end = INV.sentence_end(self.masked, start)
                block = [o for o in modules if o["body_start"] <= match.start(1) < o["close_start"]]
                self.decls.append({"name": match.group(1), "start": start, "name_at": match.start(1), "end": end,
                                   "module": ".".join(o["label"] for o in block) or None,
                                   "block_end": block[-1]["close_start"] if block else len(self.masked),
                                   "text": self.masked[start:end]})

    def enclosing(self, position: int) -> dict | None:
        for decl in self.decls:
            if decl["start"] <= position < decl["end"]:
                return decl
        return None

    def shadowed(self, name: str, position: int, own: int | None = None) -> bool:
        """Rocq resolves a bare name to its most recent visible declaration: among this file's same-named declarations
        that ENDED before `position` (S-1), in a scope still open there, the latest one. It shadows the alias unless it is
        the alias's own declaration (at offset `own`; the Mac 1032Z: a top-level or other-Module namesake earlier in the
        file does not hide a use that follows the alias's own definition)."""
        visible = [d for d in self.decls if d["name"] == name and d["end"] <= position < d["block_end"]]
        return bool(visible) and max(visible, key=lambda d: d["end"])["name_at"] != own

    def declaration_site(self, position: int) -> bool:
        return any(d["name_at"] == position for d in self.decls)

    def declaration_at(self, position: int) -> dict | None:
        return next((d for d in self.decls if d["name_at"] == position), None)

    def implicit(self, position: int) -> bool:
        start = self.masked.rfind(".", 0, position)
        while start > 0 and not (start + 1 >= len(self.masked) or self.masked[start + 1].isspace()):
            start = self.masked.rfind(".", 0, start)
        return bool(IMPLICIT_RE.match(self.masked[start + 1 if start >= 0 else 0:position]))


def module_split(qualified: str, modules: dict[str, str]) -> tuple[str | None, str | None]:
    """The repository file of a qualified name (its longest module prefix that is a file) and the Module path inside that
    file (None at top level), e.g. Pkg.conjectures.X.M.name -> (the file of Pkg.conjectures.X, "M")."""
    module = qualified.rpartition(".")[0]
    for prefix in (module.rsplit(".", i)[0] for i in range(module.count(".") + 1)):
        if prefix in modules:
            return modules[prefix], module[len(prefix) + 1:] or None
    return None, None


def module_file(qualified: str, modules: dict[str, str]) -> str | None:
    return module_split(qualified, modules)[0]


def certificate_files(spec: dict, modules: dict[str, str]) -> set[str]:
    """The family's OWN certificate: the files of its compatibility_theorems (Marcol C-3), not the spec's
    certificate_files, which may list the family's public foundation file."""
    return {f for name in spec.get("compatibility_theorems", []) if (f := module_file(name, modules))}


def requires_of(scan_text: str) -> list[tuple[str | None, str]]:
    out = []
    for match in REQUIRE_RE.finditer(scan_text):
        prefix, names = match.groups()
        out.extend((prefix, name) for name in names.split())
    return out


def suffix_index(modules: dict[str, str]) -> dict[str, set[str]]:
    """Every dotted suffix of a logical module name -> its repository paths (Require resolves suffixes)."""
    by_suffix = defaultdict(set)
    for logical, path in modules.items():
        parts = logical.split(".")
        for i in range(len(parts)):
            by_suffix[".".join(parts[i:])].add(path)
    return by_suffix


def require_chain(start: str, target: str, by_suffix: dict[str, set[str]], cache: dict[str, list]) -> str:
    """yes / no / unknown: does the transitive Require closure of `start` reach the file `target`? Report only."""
    namespaces = set(INV.repository_namespaces().values())
    seen, pending, unknown = set(), [start], False
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        if path == target:
            return "yes"
        if path not in cache:
            try:
                cache[path] = requires_of(INV.scope_mask((ROOT / path).read_text(), path))
            except (OSError, ValueError):
                cache[path] = None
        if cache[path] is None:
            unknown = True
            continue
        for prefix, name in cache[path]:
            full = f"{prefix}.{name}" if prefix else name
            hits = by_suffix.get(full, set())
            if not hits and full.split(".")[0] in namespaces:
                unknown = True
            pending.extend(sorted(hits))
    return "unknown" if unknown else "no"


EXCEPTIONS_KEY = "alias_retention_exceptions"
EXCEPTION_REASON_MIN = 20


def read_exceptions(data: object) -> tuple[dict[str, str], dict[tuple[str, str], str], list[str]]:
    """The declared packages without a _CoqProject and the accepted (path, reason) fallbacks; a malformed part is
    dropped with an error, so its fallbacks stay errors (fail closed)."""
    errors, packages, accepted = [], {}, {}
    where = EXCEPTIONS_KEY
    if data is None:
        return packages, accepted, errors
    if not isinstance(data, dict) or set(data) - {"packages_without_project", "accepted_fallbacks"}:
        return packages, accepted, [f"{where} must be an object with only packages_without_project and accepted_fallbacks"]
    declared = data.get("packages_without_project", {})
    if isinstance(declared, dict) and all(isinstance(k, str) and isinstance(v, str)
                                          and len(v.strip()) >= EXCEPTION_REASON_MIN for k, v in declared.items()):
        packages = dict(declared)
    else:
        errors.append(f"{where}: packages_without_project must map each package to a reason of at least "
                      f"{EXCEPTION_REASON_MIN} characters")
    entries = data.get("accepted_fallbacks", [])
    if not isinstance(entries, list):
        entries = [None]
    for i, entry in enumerate(entries):
        if not (isinstance(entry, dict) and set(entry) == {"path", "fallback", "reason"}
                and all(isinstance(v, str) and v.strip() for v in entry.values())
                and len(entry["reason"].strip()) >= EXCEPTION_REASON_MIN):
            errors.append(f"{where}: accepted_fallbacks[{i}] needs exactly path, fallback and a reason of at least "
                          f"{EXCEPTION_REASON_MIN} characters")
            continue
        key = (entry["path"], entry["fallback"])
        if key in accepted:
            errors.append(f"{where}: accepted_fallbacks[{i}] repeats {key[0]}: {key[1]}")
        accepted[key] = entry["reason"]
    return packages, accepted, errors


def alias_rows(registry: dict[str, dict], exceptions: object = None) -> tuple[list[dict], dict, list[str]]:
    """The rows (one per present alias), the counts, and the errors (unaccepted ProviderContext fallbacks, S-4;
    undeclared or stale exceptions). `exceptions`: the data's alias_retention_exceptions object."""
    import migration_report as MR
    declared_missing, accepted, errors = read_exceptions(exceptions)
    modules = module_files()
    aliases, aliases_without_file = [], []
    for family, spec in sorted(registry.items()):
        own = certificate_files(spec, modules)
        for qualified in spec.get("source_definitions", []):
            module, _, name = qualified.rpartition(".")
            path, inner = module_split(qualified, modules)
            if path is None:
                aliases_without_file.append(qualified)
                continue
            aliases.append({"alias": qualified, "family": family, "name": name, "module": module, "file": path, "inner": inner,
                            "own_certificate_files": own})
    names = {a["name"] for a in aliases}
    by_name = defaultdict(list)
    for a in aliases:
        by_name[a["name"]].append(a)
    statements = INV.manifest_statement_names()
    context = MR.ProviderContext(None)

    def has_project(package: str) -> bool:   # the shipped regular-source rule (ProviderContext.regular_text)
        try:
            context.regular_text(package + "/_CoqProject")
            return True
        except (OSError, UnicodeError, ValueError):
            return False

    namespaces = INV.repository_namespaces()
    members, read, skipped = {}, set(), []
    for package in namespaces:
        if package in declared_missing and not has_project(package):
            skipped.append(package)   # declared: no project to read, and no file of the package to scan
            members[package] = set()
            continue
        if not has_project(package):   # its own error, which no accepted fallback can suppress (the sets must be equal)
            errors.append(f"{EXCEPTIONS_KEY}: repository namespace {package} has no regular _CoqProject and is not "
                          "declared in packages_without_project")
        project = context.project(package)   # ... and an undeclared missing _CoqProject stays a fallback too
        members[package] = project[0] if project else set()
        if project:
            read.add(package)
    for package in sorted(declared_missing):
        if package not in namespaces:
            errors.append(f"{EXCEPTIONS_KEY}: packages_without_project {package} is not a repository namespace (stale)")
        elif package not in skipped:
            errors.append(f"{EXCEPTIONS_KEY}: packages_without_project {package} has a regular _CoqProject (stale)")
    for a in aliases:
        # (b): the alias's own file is outside its (read) package project: ProviderContext is not asked, every
        # reference that rules 1-3 keep counts (never fewer than the fallback's), and the row says so
        package, relative = a["file"].split("/", 1)
        a["provider_unlisted"] = package in read and relative not in members[package]
    certificates = {f: family for family, spec in registry.items() for f in certificate_files(spec, modules)}
    rows = {a["alias"]: {"alias": a["alias"], "family": a["family"], "file": a["file"],
                         "same_file": {"declarations": set(), "statements": set()},
                         "cross_file": {"files": set(), "declarations": set(), "statements": set(),
                                        "certificates_of": set(), "undecided": set(), "unlisted": set()},
                         "own_certificate": {"files": set(), "declarations": set()},
                         "implicit_use": False, "frozen_references": 0, "provider_unlisted": a["provider_unlisted"],
                         "require_chain": {}} for a in aliases}
    present, own_at = set(), {}
    req_cache: dict[str, list] = {}
    by_suffix = suffix_index(modules)
    for path in sorted(set(modules.values())):
        scan = FileScan(path, names)
        if not scan.hits:
            continue
        package = path.split("/", 1)[0]
        listed = path.split("/", 1)[1] in members.get(package, set())
        local = {}
        for decl in scan.decls:
            local[decl["name"]] = {"text": local.get(decl["name"], {"text": ""})["text"] + " " + decl["text"]}
        consumer_decls = defaultdict(set)
        for position, token in scan.hits:
            short = token.rsplit(".", 1)[-1]
            for a in by_name[short]:
                row = rows[a["alias"]]
                decl = scan.enclosing(position)
                if scan.declaration_site(position):   # a declaration's own name is not a reference
                    own = scan.declaration_at(position)
                    # the alias's OWN declaration: its file and its Module path there (Marcol G5-1), not merely the first namesake
                    if path == a["file"] and own_at.get(a["alias"]) is None and own["module"] == a["inner"]:
                        own_at[a["alias"]] = position
                        present.add(a["alias"])
                    continue
                if "." in token and MR.frozen_reference(token):
                    row["frozen_references"] += 1
                    continue
                if "." not in token:
                    if scan.undecided is None and scan.shadowed(short, position, own_at.get(a["alias"]) if path == a["file"] else None):
                        continue
                    if scan.undecided is None and listed and not a["provider_unlisted"] \
                            and not context.reference(path, short, {a["file"]}):
                        continue
                if scan.implicit(position):
                    row["implicit_use"] = True
                where = f"{path}:{decl['name']}" if decl else f"{path}:<line {scan.masked.count(chr(10), 0, position) + 1}>"
                if path == a["file"]:
                    row["same_file"]["declarations"].add(decl["name"] if decl else where)
                elif path in a["own_certificate_files"]:
                    row["own_certificate"]["files"].add(path)
                    row["own_certificate"]["declarations"].add(where)
                else:
                    cross = row["cross_file"]
                    cross["files"].add(path)
                    cross["declarations"].add(where)
                    if path in certificates:
                        cross["certificates_of"].add(certificates[path])
                    if scan.undecided is not None:
                        cross["undecided"].add(path)
                    if not listed:
                        cross["unlisted"].add(path)
                    if decl is not None:
                        consumer_decls[a["alias"]].add(decl["name"])
                    if path not in row["require_chain"]:
                        row["require_chain"][path] = require_chain(path, a["file"], by_suffix, req_cache)
        for decl in scan.decls:
            if decl["name"] not in statements:
                continue
            closure = MR.local_closure(local, decl["name"])
            for a in aliases:
                if a["name"] in closure and path == a["file"]:
                    rows[a["alias"]]["same_file"]["statements"].add(decl["name"])
                elif consumer_decls.get(a["alias"]) and (closure & consumer_decls[a["alias"]]):
                    rows[a["alias"]]["cross_file"]["statements"].add(f"{path}:{decl['name']}")
    # (c1): an accepted (path, reason) suppresses only its error; observed, accepted and unaccepted stay distinct
    observed = [(d["path"], d["reason"]) for d in context.diagnostics()]
    errors += [f"ProviderContext fallback at {p}: {r}" for p, r in observed if (p, r) not in accepted]
    errors += [f"{EXCEPTIONS_KEY}: accepted fallback at {p}: {r} no longer fires (stale)"
               for p, r in sorted(set(accepted) - set(observed))]
    errors += [f"alias {q}: no repository file holds its module" for q in aliases_without_file]
    out = []
    for qualified in sorted(rows):
        if qualified not in present:
            continue
        row = rows[qualified]
        for key in ("same_file", "cross_file", "own_certificate"):
            row[key] = {k: sorted(v) for k, v in row[key].items()}
        row["require_chain"] = dict(sorted(row["require_chain"].items()))
        out.append(row)
    counts = {"aliases": len(out), "absent": len(rows) - len(out),
              "with_same_file": sum(bool(r["same_file"]["declarations"] or r["same_file"]["statements"]) for r in out),
              "with_cross_file": sum(bool(r["cross_file"]["files"]) for r in out),
              "cross_file_files": sum(len(r["cross_file"]["files"]) for r in out),
              "cross_file_declarations": sum(len(r["cross_file"]["declarations"]) for r in out),
              "with_own_certificate": sum(bool(r["own_certificate"]["files"]) for r in out),
              "implicit_use": sum(r["implicit_use"] for r in out),
              "undecided_files": len({f for r in out for f in r["cross_file"]["undecided"]}),
              "unlisted_files": len({f for r in out for f in r["cross_file"]["unlisted"]}),
              "provider_unlisted_files": sorted({r["file"] for r in out if r["provider_unlisted"]}),
              "provider_unlisted_aliases": sum(r["provider_unlisted"] for r in out),
              "packages_without_project": sorted(skipped),
              "provider_fallbacks": len(observed),
              # the exact reviewed exceptions, by their (path, reason) pairs (Marcol N-1: two at one path stay distinct)
              "accepted_fallbacks": sorted(f"{p}: {r}" for p, r in observed if (p, r) in accepted)}
    return out, counts, errors


MILESTONE_RE = re.compile(r"(retain:frozen-statement|retain:certificate|removable-now|remove-after:([a-z0-9][a-z0-9-]*))")


def validate_milestones(rows: list[dict], authored: object, milestones: dict, inventory: dict) -> tuple[list[str], set[str]]:
    """The authored alias milestones against the computed rows; also S-4. Returns errors and the cited table ids."""
    errors, cited = [], set()
    if not isinstance(authored, dict):
        return ["alias_milestones must be an object"], cited
    by_alias = {r["alias"]: r for r in rows}
    for alias in sorted(set(by_alias) - set(authored)):
        errors.append(f"alias_milestones: {alias} has no milestone")
    for alias in sorted(set(authored) - set(by_alias)):
        errors.append(f"alias_milestones: stale alias {alias}")
    helpers = {h["qualified_name"]: h for h in inventory["helpers"]}
    for alias in sorted(set(by_alias) & set(authored)):
        row, value = by_alias[alias], authored[alias]
        match = MILESTONE_RE.fullmatch(value) if isinstance(value, str) else None
        if match is None:
            errors.append(f"alias_milestones: {alias}: {value!r} is not in the vocabulary")
            continue
        same, cross, own = row["same_file"], row["cross_file"], row["own_certificate"]
        if (same["statements"] or cross["statements"]) and value != "retain:frozen-statement":
            errors.append(f"alias_milestones: {alias}: a frozen statement consumes it, so only retain:frozen-statement is "
                          "allowed (a removal needs a separate statement re-audit)")
        if value == "retain:frozen-statement" and not (same["statements"] or cross["statements"]):
            errors.append(f"alias_milestones: {alias}: retain:frozen-statement without a statement consumer")
        if value == "retain:certificate" and not (set(cross["certificates_of"]) - {row["family"]}):
            errors.append(f"alias_milestones: {alias}: retain:certificate without another family's certificate")
        if value == "removable-now" and (same["declarations"] or same["statements"] or cross["files"]
                                         or own["files"] or row["implicit_use"]):
            errors.append(f"alias_milestones: {alias}: removable-now with consumers or implicit use")
        if match.group(2):
            if match.group(2) not in milestones:
                errors.append(f"alias_milestones: {alias}: milestone {match.group(2)} is not in the table")
            cited.add(match.group(2))
        helper = helpers.get(alias)
        if helper is not None:
            module = alias.rpartition(".")[0]
            missing = sorted(set(helper["direct_consumers"]) - {f"{module}.{d}" for d in same["declarations"]})
            if missing:
                errors.append(f"alias_retention: {alias}: same-file set lacks the inventory's direct consumers {missing}")
    return errors, cited


RETIREMENT = "post-rc-alias-retirement"


def suggest_milestones(rows: list[dict]) -> dict[str, str]:
    """The rule-derived milestone of each alias, for authoring (`--suggest-milestones`; never in --write / --check)."""
    out = {}
    for row in rows:
        same, cross, own = row["same_file"], row["cross_file"], row["own_certificate"]
        if same["statements"] or cross["statements"]:
            out[row["alias"]] = "retain:frozen-statement"
        elif set(cross["certificates_of"]) - {row["family"]}:
            out[row["alias"]] = "retain:certificate"
        elif not (same["declarations"] or cross["files"] or own["files"] or row["implicit_use"]):
            out[row["alias"]] = "removable-now"
        else:
            out[row["alias"]] = f"remove-after:{RETIREMENT}"
    return out


def counts_line(counts: dict, authored: object) -> str:
    milestones = defaultdict(int)
    for value in (authored or {}).values() if isinstance(authored, dict) else ():
        milestones[str(value).split(":")[0] if not str(value).startswith("retain:") else value] += 1
    def shown(value: object) -> str:   # a named set prints its size and its members
        return f"{len(value)} ({', '.join(value)})" if isinstance(value, list) else str(value)
    return ("alias retention: " + ", ".join(f"{key} {shown(counts[key])}" for key in (
        "aliases", "absent", "with_same_file", "with_cross_file", "cross_file_files", "cross_file_declarations",
        "with_own_certificate", "implicit_use", "undecided_files", "unlisted_files", "provider_unlisted_files",
        "provider_unlisted_aliases", "packages_without_project", "provider_fallbacks", "accepted_fallbacks"))
        + "; milestones " + ", ".join(f"{k} {v}" for k, v in sorted(milestones.items())))
