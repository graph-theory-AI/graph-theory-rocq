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
body, complete-iff and zero-assumption checks still required.
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
import re
import shlex
import subprocess
import sys
import tempfile
from collections import defaultdict
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
    rf"(?:{DECL_KEYWORDS})\s+({IDENT})\b",
    re.M,
)
MODULE_RE = re.compile(rf"^\s*Module\s+({IDENT})\s*\.", re.M)
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


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout


def source_at(commit: str | None, path: str) -> str:
    """File text at a commit, or in the working tree when commit is None."""
    if commit is None:
        return (ROOT / path).read_text()
    return git("show", f"{commit}:{path}")


def blob_at(commit: str, path: str) -> str:
    return git("rev-parse", f"{commit}:{path}").strip()


def ref_re(name: str) -> re.Pattern[str]:
    # Match from the beginning of a qualified name; callers can distinguish a
    # live module reference from Legacy.foo without losing either reference.
    return re.compile(rf"(?<![A-Za-z0-9_'.])(?:{IDENT}\.)*{re.escape(name)}(?![A-Za-z0-9_'])")


def frozen_reference(name: str, modules: set[str] = frozenset()) -> bool:
    return any(part in modules or part == "Legacy" or part.endswith(("Legacy", "Original"))
               for part in name.split(".")[:-1])


def live_reference(text: str, name: str, modules: set[str] = frozenset()) -> bool:
    return any(not frozen_reference(m.group(), modules) for m in ref_re(name).finditer(text))


def module_spans(clean: str) -> list[tuple[str, int, int]]:
    """(name, start, end) of every non-nested `Module M. ... End M.` block."""
    spans = []
    for match in MODULE_RE.finditer(clean):
        name = match.group(1)
        end = re.compile(rf"^\s*End\s+{re.escape(name)}\s*\.", re.M).search(clean, match.end())
        if end:
            spans.append((name, match.start(), end.end()))
    return spans


def declarations(src: str) -> list[dict]:
    """Every declaration of a file: name, enclosing module, normalized text, line."""
    clean = INV.strip_comments(src)
    spans = module_spans(clean)
    out = []
    for match in DECL_RE.finditer(clean):
        start = clean.rfind("\n", 0, match.start(1)) + 1
        module = next((n for n, s, e in spans if s <= match.start() < e), None)
        text = INV.normalize_space(clean[start:INV.sentence_end(clean, start)])
        out.append({
            "name": match.group(1),
            "module": module,
            "text": text,
            "line": clean.count("\n", 0, match.start(1)) + 1,
        })
    return out


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


def inventory_hash(commit: str, qualified: str) -> str | None:
    data = json.loads(source_at(commit, "meta/library_helper_inventory.json"))
    for helper in data.get("helpers", []):
        if helper["qualified_name"] == qualified:
            return helper["declaration_hash"]
    return None


def doc_block(src: str, name: str) -> str | None:
    """Raw text of the comment that immediately precedes `Definition name`."""
    match = re.search(rf"^Definition\s+{re.escape(name)}\b", src, re.M)
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

    This narrow enrollment lexer intentionally does not change ordinary family
    parsing. Joint scanning matters: comment delimiters inside strings must not
    hide real scope commands, and scope words in strings must not close scopes.
    """
    result = list(source)
    depth, quoted, index = 0, False, 0
    while index < len(source):
        width = 1
        if depth:
            if source.startswith("(*", index):
                depth += 1
                width = 2
            elif source.startswith("*)", index):
                depth -= 1
                width = 2
        elif quoted:
            if source.startswith('""', index):
                width = 2
            elif source[index] == '"':
                quoted = False
        elif source.startswith("(*", index):
            depth = 1
            width = 2
        elif source[index] == '"':
            quoted = True
        elif source.startswith("*)", index):
            raise ValueError("additional statement has an unmatched comment delimiter")
        else:
            index += 1
            continue
        for offset in range(index, index + width):
            if source[offset] != "\n":
                result[offset] = " "
        index += width
    if depth or quoted:
        raise ValueError("additional statement has an unterminated comment or string")
    return "".join(result)


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
    owners = {namespace: package for package, namespace in INV.repository_namespaces().items()}
    # corpus_registry also retains the historic graph-theory-base alias.
    owners.update(GTBase="base", Atlas="atlas", ClassicalLemmas="classical-lemmas")
    for qualified in sorted(names):
        namespace, *parts, name = qualified.split(".")
        package = owners.get(namespace)
        if package is None or not parts or parts[0] != "conjectures":
            raise ValueError(f"{qualified}: additional statement needs a known conjecture module")
        path = package + "/theories/" + "/".join(parts) + ".v"
        project_path = package + "/_CoqProject"
        if rows_base.get(name) or rows_now.get(name):
            raise ValueError(f"{qualified}: additional statement must be outside both corpus manifests")
        objects = [obj for obj in spec["frozen"] if obj.get("qualified") == qualified]
        if (len(objects) != 1 or objects[0].get("kind") != "statement"
                or objects[0].get("non_corpus") is not True or "corpus" in objects[0]
                or objects[0].get("path") != path or objects[0].get("name") != name
                or objects[0].get("commit", base) != base
                or not objects[0].get("certificate")):
            raise ValueError(f"{qualified}: additional statement needs one exact non_corpus statement mapping")
        for commit in (base, None):
            if commit is not None:
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
            scopes = re.compile(rf"(Module(?:\s+Type)?(?:\s+(?:Import|Export))?|Section|End)\s+({IDENT})(?![\w'])")
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


def statement_dependencies(base: str | None, sources: set[str], rows: dict, *,
                           include_public: bool = False,
                           additional_statements: set[str] = frozenset()) -> tuple[set[str], set[str]]:
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
    paths = (git("ls-tree", "-r", "--name-only", base).splitlines() if base is not None
             else sorted(set(git("ls-files", "--cached", "--others", "--exclude-standard").splitlines())))
    projects, nodes, node_packages, short_names = {}, {}, {}, defaultdict(set)
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
                short_names[decl["name"]].add(qualified)
    if include_public and sources - set(nodes):
        raise RegistryError(f"source declarations missing from baseline dependency index: {sorted(sources - set(nodes))}")
    reverse, forward = defaultdict(set), defaultdict(set)
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
    reached, pending = set(sources), list(sources)
    while pending:
        for consumer in reverse[pending.pop()] - reached:
            reached.add(consumer)
            pending.append(consumer)
    if additional_statements & sources or additional_statements - (reached & set(nodes)):
        raise ValueError("additional statements must be reached from migrated sources and cannot be source helpers")
    statements = {name for name in reached if name in nodes and
            (name.rsplit(".", 1)[-1].endswith("_statement") or
             any(row.get("repo") == node_packages[name]
                 for row in rows.get(name.rsplit(".", 1)[-1], [])))}
    statements.update(additional_statements)
    ancestors, pending = set(statements), list(statements)
    while pending:
        for dependency in forward[pending.pop()] - ancestors:
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
    if expected_statements is None:
        entry = load_library_registry(ROOT)["primitives"].get(spec["family"], {})
        sources = migrated_registry_sources(entry)
        expected_statements, _ = statement_dependencies(
            base, sources, rows_base,
            include_public=bool(entry.get("repository_sources")),
            additional_statements=additional)
        if additional:
            statement_dependencies(None, sources, rows_now,
                                   include_public=bool(entry.get("repository_sources")),
                                   additional_statements=additional)
    objects, errors = [], []
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
        imports = sorted({module_for_path(obj["frozen_path"], spec["namespaces"])
                          for obj in objects} | {name.rsplit(".", 1)[0]
                                                for name in certificates[package]})
        body = ["Require " + module + "." for module in imports]
        for obj in objects:
            frozen = module_for_path(obj["frozen_path"], spec["namespaces"]) + "." + obj["frozen"]
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
    expected_statements, reaching = statement_dependencies(
        base, expected_sources, rows_base, include_public=bool(repository_sources),
        additional_statements=additional)
    if additional:
        statement_dependencies(None, expected_sources, rows_now,
                               include_public=bool(repository_sources),
                               additional_statements=additional)
    _, role_errors = statement_obligations(
        spec, expected_statements=expected_statements, rows_base=rows_base, rows_now=rows_now)
    for error in role_errors:
        check(False, error)
    supplied_statements = {obj["qualified"] for obj in spec["frozen"] if obj["kind"] == "statement"}
    check(expected_statements == supplied_statements,
          "affected statement coverage matches baseline dependencies",
          f"missing={sorted(expected_statements - supplied_statements)}; extra={sorted(supplied_statements - expected_statements)}")
    if repository_sources or additional:
        frozen_chain = {obj['qualified'] for obj in spec['frozen'] if obj['kind'] in {'source', 'chain'}}
        missing_chain = reaching - expected_statements - frozen_chain
        label = ("public source paths" if repository_sources else "additional statement paths")
        check(not missing_chain, label + " have complete frozen intermediary coverage",
              f"missing={sorted(missing_chain)}")
    for obj in (o for o in spec["frozen"] if o["kind"] == "statement"):
        base_src, live_src = source_at(base, obj["path"]), source_at(None, obj["path"])
        decls = {d["name"]: d for d in declarations(base_src) if d["module"] is None}
        closure = local_closure(decls, obj["name"])
        reaches = {n for n in closure if local_closure(decls, n) & source_names}
        affected = sorted(reaches - {obj["name"]})
        computed_chain.update(affected)
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

    # Frozen bodies anywhere in the migration layer that still resolve through
    # a live helper or chain declaration of this family.
    # Computed chains, not only the spec's list, so a missing freeze cannot hide.
    live_names = source_names | chain_names | computed_chain
    stale = []
    for path in sorted(ROOT.glob("*/theories/migration/*.v")):
        rel = path.relative_to(ROOT).as_posix()
        for decl in declarations(path.read_text()):
            if decl["module"] is None:
                continue
            hits = sorted(n for n in live_names if live_reference(body_after_name(decl), n, frozen_modules))
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
            for match in pattern.finditer(clean):
                if frozen_reference(match.group(), frozen_modules):
                    continue
                line = clean.count("\n", 0, match.start()) + 1
                owner = next((d for d in reversed(decls) if d["line"] <= line), None)
                owner_name = (f"{owner['module']}.{owner['name']}" if owner and owner["module"]
                              else owner["name"] if owner else None)
                if owner and owner["name"] == name and owner["line"] == line:
                    continue
                consumers.append({"name": name, "path": rel, "line": line, "in": owner_name,
                                  "declared_here": any(d["name"] == name and d["module"] is None
                                                       for d in decls)})
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
        "checks": checks,
        "ok": all(c["ok"] for c in checks),
        "validation_limits": [
            "Default checks compare source text, registry coverage and conservative lexical dependencies; they do not prove theorem types.",
            "--kernel checks exact closed statement equivalences and assumptions of every named certificate/API theorem, using already-built modules.",
            ("Dependency discovery also scans build-listed public base/foundation declarations for explicitly enrolled repository sources; it does not resolve notation, constructor names, module aliases or Section context like Rocq."
             if repository_sources else
             "Dependency discovery scans build-listed conjecture declarations, including Inductive and Record bodies; it does not resolve notation, constructor names, module aliases or Section context like Rocq."),
            "Helper exact types, Section scaffolding and compiled dependency closure still require independent review and family-specific Section and kernel dependency evidence.",
        ],
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
                     f"unchanged): {item['note']}")
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
