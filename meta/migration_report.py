#!/usr/bin/env python3
"""Generate and check the migration report of one library-migration family.

Usage:
    python3 meta/migration_report.py FAMILY [--write | --check]
    python3 meta/migration_report.py --validate

FAMILY names a spec file meta/migration_reports/FAMILY.spec.json.  The spec lists
every frozen object of the family's certificates: the original declaration (path,
name and the commit it is frozen from), the frozen copy (certificate path, module
and name), the identifier substitutions that turn the original text into the
frozen one, and the certificate theorem relating the frozen body to the live one.

The generator is toolchain-free (it reads sources and git history, it never runs
Rocq; the certificates themselves are checked by check_library_migration.py).
It verifies that

  * each frozen copy equals its original declaration, after comment stripping,
    whitespace normalization and the listed substitutions, and records the
    original declaration hash (the inventory's declaration_hash) and git blob;
  * each source helper's recorded hash matches the baseline helper inventory;
  * each affected statement's frozen chain covers every same-file declaration
    through which the statement reaches a source helper;
  * no frozen body in any migration certificate still resolves through a live
    helper or chain declaration of this family (reported, not hidden, when an
    earlier family's certificate does);
  * statement texts, their doc blocks, manifest rows and leg states are unchanged
    since the baseline, and the listed distinct name matches are untouched;
  * every certificate theorem is declared in its certificate file.

It also lists every repository-wide reference to the family's helpers, chains and
statements, and every direct user of the canonical definition.  --write refreshes
meta/migration_reports/FAMILY.{json,md}; --check fails on any failed verification
or drift of those files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import library_inventory as INV


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
    return re.compile(rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'])")


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
    manifest = json.loads(source_at(commit, "meta/v2_corpus_manifest.json"))
    legs = json.loads(source_at(commit, "meta/v2_legs_state.json"))
    rows: dict[str, list[dict]] = {}
    for row in manifest["rows"]:
        if row.get("formal_name"):
            rows.setdefault(row["formal_name"], []).append(row)
    return rows, legs.get("entries", {})


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


def build_report(spec: dict) -> dict:
    base = spec["baseline_commit"]
    checks: list[dict] = []

    def check(ok: bool, what: str, detail: str = "") -> None:
        checks.append({"ok": bool(ok), "check": what, "detail": detail})

    frozen_rows = []
    for obj in spec["frozen"]:
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
            recorded = inventory_hash(commit, obj["qualified"])
            check(recorded == row["declaration_sha256"],
                  f"{obj['qualified']} hash equals the baseline inventory declaration_hash",
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

    # The frozen chain of each statement covers every same-file declaration
    # through which the statement reaches a source helper.
    sources = [o for o in spec["frozen"] if o["kind"] == "source"]
    source_names = {o["name"] for o in sources}
    chain_names = {o["name"] for o in spec["frozen"] if o["kind"] == "chain"}
    statements = []
    computed_chain: set[str] = set()
    rows_base, legs_base = manifest_rows(base)
    rows_now, legs_now = manifest_rows(None)
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
        base_rows, now_rows = rows_base.get(formal, []), rows_now.get(formal, [])
        check(len(now_rows) == 1 and base_rows == now_rows,
              f"{formal}: manifest row unchanged since baseline",
              f"{len(base_rows)} baseline / {len(now_rows)} current rows")
        row_now = now_rows[0] if now_rows else {}
        slug = row_now.get("slug")
        check(slug in legs_base and legs_base.get(slug) == legs_now.get(slug),
              f"{formal}: leg-state entry unchanged since baseline")
        statements.append({
            "qualified": obj["qualified"],
            "row_id": row_now.get("row_id"),
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
            hits = sorted(n for n in live_names if ref_re(n).search(body_after_name(decl)))
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
    canonical_re = re.compile(rf"(?<![A-Za-z0-9_'.]){re.escape(canonical)}(?![A-Za-z0-9_'])")
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
    }


def render_markdown(report: dict, spec: dict) -> str:
    lines = [
        f"# Migration report: {report['family']}",
        "",
        "> Generated by `python3 meta/migration_report.py "
        f"{spec['report_name']} --write` from "
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


def self_test() -> int:
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
    print(f"migration-report self-test {'OK' if ok else 'FAILED'}")
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("family", nargs="?")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args(argv)
    if args.validate:
        return self_test()
    if not args.family:
        parser.error("FAMILY is required")
    spec = json.loads((REPORTS / f"{args.family}.spec.json").read_text())
    spec["report_name"] = args.family
    report = build_report(spec)
    rendered_json = json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    rendered_md = render_markdown(report, spec)
    json_path, md_path = REPORTS / f"{args.family}.json", REPORTS / f"{args.family}.md"
    if args.write:
        json_path.write_text(rendered_json)
        md_path.write_text(rendered_md)
    failed = [c for c in report["checks"] if not c["ok"]]
    for c in failed:
        print(f"  FAILED: {c['check']} {c['detail']}".rstrip(), file=sys.stderr)
    if args.check:
        for path, rendered in ((json_path, rendered_json), (md_path, rendered_md)):
            if not path.exists() or path.read_text() != rendered:
                print(f"  ERROR: {path.relative_to(ROOT)} has drifted; run "
                      f"python3 meta/migration_report.py {args.family} --write", file=sys.stderr)
                failed.append({"check": "drift"})
    print(f"migration report {args.family}: {len(report['checks']) - len(failed)} of "
          f"{len(report['checks'])} checks pass; {len(report['frozen'])} frozen objects, "
          f"{len(report['statements'])} statements, {len(report['consumers'])} references")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
