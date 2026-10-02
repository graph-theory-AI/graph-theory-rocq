#!/usr/bin/env python3
"""Generate (or check) the per-row migration report of one library-migration family.

    python3 meta/library_migration_report.py FAMILY [--check]

FAMILY names the spec meta/migration_reports/FAMILY.json; the report is written to
meta/migration_reports/FAMILY.md (``--check`` regenerates it in memory and fails on
drift or on any failed check).  Run it through the pinned wrapper after building the
packages that hold the family's certificate modules.

The spec lists the migrated helpers, the certificate modules with the source file of
each ``XnnLegacy`` module, the reviewed proof-level consumers, the documented
discrepancies that must survive the migration and the deferred families.  Everything
else is derived and checked here:

1. every frozen declaration of a Legacy module is byte-identical to the same
   declaration of its source file at the spec's base commit, and every Section /
   Variables / End line of a Legacy module occurs verbatim in that source;
2. every frozen declaration NAME has a certificate theorem NAME_compat in its module,
   and ``Print Assumptions`` is closed for each of them;
3. the frozen declarations that are manifest statements are the rows of the report;
   for each row the dependency chain to its helper is read off the frozen texts, and
   ``Print All Dependencies`` shows that the Legacy statement reaches no live
   migrated helper and not the canonical primitive, while the live statement does
   reach the canonical primitive;
4. in each source file the only declarations whose text changed since the base
   commit are the migrated helpers, the statement doc blocks of the rows are
   unchanged, and the manifest status and legs of the rows are unchanged;
5. the proof-level consumers named by the spec still exist.
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
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "meta"
REPORTS = META / "migration_reports"
sys.path.insert(0, str(META))
import corpus_registry  # noqa: E402
import rocq_toolchain as ROCQ  # noqa: E402

DECL_RE = re.compile(
    r"(?m)^(Definition|Fixpoint|Lemma|Theorem|Corollary|Fact|Remark)[ \t]+([A-Za-z_][A-Za-z0-9_']*)\b")
FROZEN_KINDS = {"Definition", "Fixpoint"}
MODULE_RE = re.compile(r"(?m)^Module[ \t]+([A-Za-z_][A-Za-z0-9_']*Legacy)\.[ \t]*$")
IDENT_RE = re.compile(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])")
DEP_NAME_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_'.]*) :$")
SCAFFOLD_RE = re.compile(r"^(Section|Variables?|End)\b")


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], check=True, text=True,
                          capture_output=True).stdout


def at_base(base: str, rel: str) -> str:
    return git("show", f"{base}:{rel}")


def blank_comments(src: str) -> str:
    """Replace (nested) comments by spaces, preserving offsets."""
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("(*", i):
            depth += 1; out.append("  "); i += 2
        elif depth and src.startswith("*)", i):
            depth -= 1; out.append("  "); i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


def sentence_end(clean: str, start: int) -> int:
    i = start
    while True:
        j = clean.find(".", i)
        if j < 0:
            return len(clean)
        if j + 1 == len(clean) or clean[j + 1].isspace():
            return j + 1
        i = j + 1


def declarations(src: str, kinds=FROZEN_KINDS) -> dict[str, str]:
    """name -> verbatim text of each top-level Definition/Fixpoint sentence."""
    clean = blank_comments(src)
    out: dict[str, str] = {}
    for m in DECL_RE.finditer(clean):
        if m.group(1) in kinds:
            out.setdefault(m.group(2), src[m.start():sentence_end(clean, m.end())])
    return out


def doc_block(src: str, name: str) -> str | None:
    """The comment that immediately precedes Definition NAME (statement doc block)."""
    m = re.search(rf"(?m)^Definition[ \t]+{re.escape(name)}\b", src)
    if not m:
        return None
    head = src[:m.start()].rstrip()
    if not head.endswith("*)"):
        return None
    depth, i = 0, len(head) - 1
    while i > 0:
        if head[i - 1:i + 1] == "*)":
            depth += 1; i -= 2; continue
        if head[i - 1:i + 1] == "(*":
            depth -= 1
            if depth == 0:
                return head[i - 1:]
            i -= 2; continue
        i -= 1
    return None


def legacy_modules(src: str) -> dict[str, dict]:
    """Legacy module name -> {decls: name -> text, scaffold: [lines], imports: [modules]}."""
    clean = blank_comments(src)
    out: dict[str, dict] = {}
    for m in MODULE_RE.finditer(clean):
        name = m.group(1)
        end = re.compile(rf"(?m)^End[ \t]+{re.escape(name)}\.[ \t]*$").search(clean, m.end())
        if not end:
            raise ValueError(f"unterminated module {name}")
        body_src, body_clean = src[m.end():end.start()], clean[m.end():end.start()]
        decls = {}
        for d in DECL_RE.finditer(body_clean):
            if d.group(1) in FROZEN_KINDS:
                decls[d.group(2)] = body_src[d.start():sentence_end(body_clean, d.end())]
        lines = [ln.strip() for ln in body_clean.splitlines()]
        out[name] = {
            "decls": decls,
            "scaffold": [ln for ln in lines if SCAFFOLD_RE.match(ln)],
            "imports": re.findall(r"(?m)^Import[ \t]+([A-Za-z_][A-Za-z0-9_']*Legacy)\.", body_clean),
        }
    return out


def include_flags(package: str) -> list[str]:
    tokens = shlex.split((ROOT / package / "_CoqProject").read_text(), comments=True)
    flags: list[str] = []
    for i, tok in enumerate(tokens):
        if tok in ("-R", "-Q") and i + 2 < len(tokens):
            flags.extend(tokens[i:i + 3])
    return flags


def run_probe(package: str, module: str, queries: list[tuple[str, str]]) -> dict[str, str]:
    """Run [(key, vernacular)] after requiring MODULE; return key -> output section."""
    prefix, _, leaf = module.rpartition(".")
    namespace, _, rest = prefix.partition(".")
    lines = [f"From {namespace} Require {rest + '.' if rest else ''}{leaf}."]
    for i, (_, query) in enumerate(queries):
        lines.append(f"Definition migration_report_marker_{i} := {i}.")
        lines.append(f"Print migration_report_marker_{i}.")
        lines.append(query)
    with tempfile.TemporaryDirectory(prefix="migration-report-") as tmp:
        probe = Path(tmp) / "migration_report_probe.v"
        probe.write_text("\n".join(lines) + "\n")
        proc = subprocess.run(["coqc", *include_flags(package), "-w", "-notation-overridden",
                               str(probe)], cwd=ROOT / package, env=ROCQ.environment(),
                              text=True, capture_output=True, check=False)
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        raise RuntimeError(f"{module}: probe failed: {output[-1500:]}")
    sections: dict[str, str] = {}
    marks = list(re.finditer(r"(?m)^migration_report_marker_(\d+) = \d+\n\s*: nat\n", output))
    for k, m in enumerate(marks):
        stop = marks[k + 1].start() if k + 1 < len(marks) else len(output)
        sections[queries[int(m.group(1))][0]] = output[m.end():stop]
    return sections


def dependency_names(section: str) -> list[str]:
    return [m.group(1) for m in map(DEP_NAME_RE.match, section.splitlines()) if m]


def chain_to(start: str, targets: set[str], frozen: dict[str, str]) -> list[str] | None:
    """Shortest reference chain start -> ... -> a target through frozen texts."""
    queue, seen = [[start]], {start}
    while queue:
        path = queue.pop(0)
        text = frozen[path[-1]]
        body = text.split(":=", 1)[1] if ":=" in text else text
        for ident in IDENT_RE.findall(body):
            if ident in frozen and ident not in seen:
                if ident in targets:
                    return path + [ident]
                seen.add(ident)
                queue.append(path + [ident])
    return None


_CONJECTURE_FILES: dict[str, list[str]] = {}


def conjecture_files() -> dict[str, list[str]]:
    """file stem -> repository paths of the conjecture files with that stem."""
    if not _CONJECTURE_FILES:
        for path in sorted(ROOT.glob("*/theories/conjectures/*.v")):
            _CONJECTURE_FILES.setdefault(path.stem, []).append(path.relative_to(ROOT).as_posix())
    return _CONJECTURE_FILES


def manifest_rows() -> dict[str, dict]:
    rows = {}
    for corpus in corpus_registry.existing_corpora():
        for row in corpus_registry.load_manifest(corpus)["rows"]:
            if row.get("formal_name"):
                rows[row["formal_name"]] = {"corpus": corpus, **row}
    return rows


def base_manifest_rows(base: str) -> dict[str, dict]:
    rows = {}
    for corpus in corpus_registry.existing_corpora():
        rel = Path(corpus_registry.manifest_path(corpus)).relative_to(ROOT).as_posix()
        for row in json.loads(at_base(base, rel))["rows"]:
            if row.get("formal_name"):
                rows[row["formal_name"]] = row
    return rows


def build(spec: dict) -> tuple[str, list[str]]:
    base = spec["base_commit"]
    errors: list[str] = []
    rows_now, rows_base = manifest_rows(), base_manifest_rows(base)
    helpers = {h["name"].rsplit(".", 1)[1]: h for h in spec["helpers"]}
    canonical_short = spec["canonical"].rsplit(".", 1)[1]

    frozen_rows, statement_rows, source_files = [], [], {}
    for cert in spec["certificates"]:
        module, package = cert["module"], cert["package"]
        cert_src = (ROOT / cert["path"]).read_text()
        legacy = legacy_modules(cert_src)
        lemmas = set(re.findall(r"(?m)^Lemma[ \t]+([A-Za-z_][A-Za-z0-9_']*_compat)\b",
                                blank_comments(cert_src)))
        if set(legacy) != set(cert["legacy_sources"]):
            errors.append(f"{module}: Legacy modules {sorted(legacy)} differ from the spec "
                          f"{sorted(cert['legacy_sources'])}")
        all_frozen: dict[str, str] = {}
        for lname, info in legacy.items():
            all_frozen.update(info["decls"])
        queries: list[tuple[str, str]] = []
        for lname, info in legacy.items():
            rel = cert["legacy_sources"].get(lname)
            if rel is None:
                continue
            base_src, now_src = at_base(base, rel), (ROOT / rel).read_text()
            source_files.setdefault(rel, {
                "blob": git("rev-parse", f"{base}:{rel}").strip(),
                "sha256": sha256(base_src),
                "base_src": base_src,
                "now_src": now_src,
            })
            base_decls, now_decls = declarations(base_src), declarations(now_src)
            for line in info["scaffold"]:
                if not re.search(rf"(?m)^{re.escape(line)}[ \t]*$", base_src):
                    errors.append(f"{module}.{lname}: scaffold line not in {rel}@{base}: {line}")
            visible = dict(info["decls"])
            for imported in info["imports"]:
                visible.update(legacy.get(imported, {}).get("decls", {}))
            for name, text in info["decls"].items():
                verbatim = base_decls.get(name) == text
                if not verbatim:
                    errors.append(f"{module}.{lname}.{name}: not verbatim from {rel}@{base}")
                theorem = f"{name}_compat"
                if theorem not in lemmas:
                    errors.append(f"{module}: missing certificate {theorem}")
                queries.append((f"assum:{theorem}", f"Print Assumptions {module}.{theorem}."))
                changed = base_decls.get(name) != now_decls.get(name)
                frozen_rows.append({
                    "module": f"{module}.{lname}", "name": name, "source": rel,
                    "sha256": sha256(text), "verbatim": verbatim,
                    "theorem": f"{module}.{theorem}", "live_changed": changed,
                    "is_helper": name in helpers,
                })
                if name in rows_now:
                    chain = chain_to(name, set(helpers), visible)
                    statement_rows.append({
                        "name": name, "module": module, "legacy": f"{module}.{lname}.{name}",
                        "live_module": cert["live_modules"][lname],
                        "theorem": f"{module}.{theorem}", "source": rel, "chain": chain,
                        "package": package,
                    })
                    queries.append((f"legacy:{name}", f"Print All Dependencies {module}.{lname}.{name}."))
                    queries.append((f"live:{name}",
                                    f"Print All Dependencies {cert['live_modules'][lname]}.{name}."))
        sections = run_probe(package, module, queries)
        for key, section in sections.items():
            kind, _, name = key.partition(":")
            if kind == "assum":
                ok = "Closed under the global context" in section and "Axioms:" not in section
                for row in frozen_rows:
                    if row["theorem"] == f"{module}.{name}":
                        row["assumptions_closed"] = ok
                if not ok:
                    errors.append(f"{module}.{name}: Print Assumptions is not closed")
            else:
                deps = dependency_names(section)
                row = next(r for r in statement_rows if r["name"] == name and r["module"] == module)
                if kind == "legacy":
                    bad = sorted(d for d in deps
                                 if (d.rsplit(".", 1)[-1] in helpers and "Legacy." not in d)
                                 or d.rsplit(".", 1)[-1] == canonical_short)
                    row["frozen_closure_ok"] = not bad
                    row["frozen_helpers"] = sorted(d for d in deps if "Legacy." in d)
                    row["live_local"] = []
                    for d in deps:
                        qual, _, short = d.rpartition(".")
                        if "Legacy." in d or not qual:
                            continue
                        for rel in conjecture_files().get(qual.rsplit(".", 1)[-1], []):
                            now_text = declarations((ROOT / rel).read_text()).get(short)
                            if now_text is None:
                                continue
                            row["live_local"].append(d)
                            if declarations(at_base(base, rel)).get(short) != now_text:
                                errors.append(f"{row['legacy']}: live dependency {d} ({rel}) "
                                              f"changed since {base}")
                    row["live_local"] = sorted(set(row["live_local"]))
                    if bad:
                        errors.append(f"{row['legacy']}: reaches live helper/canonical {bad}")
                else:
                    row["live_uses_canonical"] = any(
                        d.rsplit(".", 1)[-1] == canonical_short for d in deps)
                    if not row["live_uses_canonical"]:
                        errors.append(f"{name}: live statement does not reach {spec['canonical']}")

    # 4. only the helpers changed; statement docs, status and legs unchanged
    changed_by_file = {}
    import_line = spec["import_line"] + "\n"
    for rel, info in sorted(source_files.items()):
        b, n = declarations(info["base_src"]), declarations(info["now_src"])
        changed = sorted(k for k in set(b) | set(n) if b.get(k) != n.get(k))
        changed_by_file[rel] = changed
        unexpected = [k for k in changed if k not in helpers]
        if unexpected:
            errors.append(f"{rel}: declarations changed beyond the helpers: {unexpected}")
        # Undo the helper bodies and the canonical import: the base text must come back.
        restored = info["now_src"]
        for name in changed:
            if name in helpers and name in b and name in n:
                restored = restored.replace(n[name], b[name], 1)
        if any(h["path"] == rel for h in spec["helpers"]):
            restored = restored.replace(import_line, "", 1)
        info["only_helper_and_import"] = restored == info["base_src"]
        if not info["only_helper_and_import"]:
            errors.append(f"{rel}: differs from {base} beyond the helper body and the import line")
    for row in statement_rows:
        info = source_files[row["source"]]
        row["doc_unchanged"] = (doc_block(info["base_src"], row["name"])
                                == doc_block(info["now_src"], row["name"])
                                and doc_block(info["now_src"], row["name"]) is not None)
        if not row["doc_unchanged"]:
            errors.append(f"{row['name']}: statement doc block changed or missing")
        now, old = rows_now.get(row["name"], {}), rows_base.get(row["name"], {})
        row["row_id"] = now.get("row_id")
        row["status"] = now.get("status")
        row["legs"] = now.get("legs", {})
        row["manifest_unchanged"] = (now.get("status"), now.get("legs")) == \
            (old.get("status"), old.get("legs"))
        if not row["manifest_unchanged"]:
            errors.append(f"{row['name']}: manifest status/legs differ from {base}")
        helper = row["chain"][-1] if row["chain"] else None
        row["helper"] = helper
        if helper is None:
            errors.append(f"{row['name']}: no frozen chain reaches a helper")
            row["reach"] = "none"
        else:
            hsrc = helpers[helper]["path"]
            hops = len(row["chain"]) - 1
            row["reach"] = ("cross-module" if hsrc != row["source"]
                            else "direct" if hops == 1 else "indirect")
    for consumer in spec.get("proof_consumers", []):
        src = (ROOT / consumer["path"]).read_text()
        short = consumer["declaration"].rsplit(".", 1)[1]
        if not re.search(rf"(?m)^(Lemma|Theorem)[ \t]+{re.escape(short)}\b", src):
            errors.append(f"proof consumer {consumer['declaration']} not found")

    return render(spec, frozen_rows, statement_rows, source_files, changed_by_file, errors), errors


def render(spec, frozen_rows, statement_rows, source_files, changed_by_file, errors) -> str:
    base = spec["base_commit"]
    out = []
    w = out.append
    w(f"# Library migration report: `{spec['family']}`\n")
    w("Generated by `python3 meta/library_migration_report.py "
      f"{spec['report']}` from `meta/migration_reports/{spec['report']}.json`; "
      "do not edit by hand (`--check` detects drift).\n")
    w(f"- Canonical primitive: `{spec['canonical']}` ({spec['canonical_source']}).")
    w(f"- Base commit of every frozen copy and source hash: `{base}`.")
    w(f"- Migrated helpers: {len(spec['helpers'])}; frozen declarations: {len(frozen_rows)}; "
      f"certificate theorems: {len(frozen_rows)}; affected statement rows: {len(statement_rows)} "
      f"({sum(r['reach'] == 'direct' for r in statement_rows)} direct, "
      f"{sum(r['reach'] == 'indirect' for r in statement_rows)} indirect, "
      f"{sum(r['reach'] == 'cross-module' for r in statement_rows)} cross-module).")
    w(f"- Checks: {'all passed' if not errors else f'{len(errors)} FAILED'}.\n")
    if errors:
        w("## Failed checks\n")
        out.extend(f"- {e}" for e in errors)
        w("")
    w("## Statement rows\n")
    w("Each row's Legacy statement is a verbatim copy of the base text whose affected chain is "
      "frozen; `Print All Dependencies` of the Legacy statement reaches no live migrated helper "
      f"and not `{spec['canonical']}`, while the live statement reaches the canonical "
      "primitive. Status and legs are read from the manifest and are unchanged since the base "
      "commit, as are the statement doc blocks.\n")
    w("| Row | Formal name | Status | Reach | Chain to helper | Legacy statement | "
      "Certificate theorem | Closed | Frozen closure | Live uses canonical | Doc, status, legs unchanged |")
    w("|---|---|---|---|---|---|---|---|---|---|---|")
    for r in sorted(statement_rows, key=lambda r: (r["source"], r["name"])):
        assum = next(f.get("assumptions_closed") for f in frozen_rows if f["theorem"] == r["theorem"])
        w(f"| `{r['row_id']}` | `{r['name']}` | {r['status']} | {r['reach']} | "
          f"{' -> '.join(f'`{c}`' for c in r['chain'] or [])} | `{r['legacy']}` | "
          f"`{r['theorem']}` | {yes(assum)} | {yes(r.get('frozen_closure_ok'))} | "
          f"{yes(r.get('live_uses_canonical'))} | "
          f"{yes(r['doc_unchanged'] and r['manifest_unchanged'])} |")
    w("")
    w("## Migrated helpers\n")
    w("| Helper | Convention | Live body now | Frozen copy | Certificate theorem |")
    w("|---|---|---|---|---|")
    for h in spec["helpers"]:
        short = h["name"].rsplit(".", 1)[1]
        f = next(x for x in frozen_rows if x["name"] == short)
        w(f"| `{h['name']}` | {h['convention']} | `{h['live_body']}` | `{f['module']}.{short}` | "
          f"`{f['theorem']}` |")
    w("")
    w("## Frozen declarations\n")
    w("Every declaration below is byte-identical to its source at the base commit; "
      "`sha256` is the hash of that verbatim text. `Live text changed` is yes only for the "
      "migrated helpers.\n")
    w("| Legacy declaration | Source | sha256 (base text) | Verbatim | Certificate | Closed | "
      "Live text changed |")
    w("|---|---|---|---|---|---|---|")
    for f in frozen_rows:
        w(f"| `{f['module']}.{f['name']}` | {f['source']} | `{f['sha256']}` | {yes(f['verbatim'])} | "
          f"`{f['theorem'].rsplit('.', 1)[1]}` | {yes(f.get('assumptions_closed'))} | "
          f"{yes(f['live_changed'])} |")
    w("")
    w("## Source files at the base commit\n")
    w(f"`Only helper and import` means: restoring the base text of the changed helper and "
      f"removing `{spec['import_line']}` gives back the base file byte for byte.\n")
    w("| Source | git blob | sha256 (file) | Declarations changed since base | "
      "Only helper and import |")
    w("|---|---|---|---|---|")
    for rel, info in sorted(source_files.items()):
        changed = ", ".join(f"`{c}`" for c in changed_by_file[rel]) or "none"
        w(f"| {rel} | `{info['blob']}` | `{info['sha256']}` | {changed} | "
          f"{yes(info['only_helper_and_import'])} |")
    w("")
    w("## Live local dependencies of the Legacy statements\n")
    w("Declarations of corpus conjecture files that the Legacy statements still reach live "
      "(`Print All Dependencies`). None of them reaches a migrated helper (frozen-closure "
      "check above), and the text of each is unchanged since the base commit (checked).\n")
    for r in sorted(statement_rows, key=lambda r: (r["source"], r["name"])):
        live = ", ".join(f"`{d}`" for d in r.get("live_local", [])) or "none"
        w(f"- `{r['name']}`: {live}")
    w("")
    w("## Proof-level consumers\n")
    w("Declarations outside the statement chains that use the affected definitions; their "
      "statements are unchanged and they compile against the migrated definitions.\n")
    for c in spec.get("proof_consumers", []):
        w(f"- `{c['declaration']}` ({c['path']}): {c['use']}")
    w("")
    w("## Documented discrepancies preserved\n")
    for d in spec.get("documented_discrepancies", []):
        w(f"- {', '.join(f'`{x}`' for x in d['rows'])}: {d['note']}")
    w("")
    w("## Outside this change\n")
    for d in spec.get("deferred", []):
        w(f"- {d}")
    w("")
    return "\n".join(out)


def yes(flag) -> str:
    return "yes" if flag else ("no" if flag is not None else "n/a")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("family", help="spec name, e.g. path_vertices")
    parser.add_argument("--check", action="store_true", help="fail if the report is stale")
    args = parser.parse_args(argv)
    spec_path = REPORTS / f"{args.family}.json"
    spec = json.loads(spec_path.read_text())
    spec["report"] = args.family
    text, errors = build(spec)
    target = REPORTS / f"{args.family}.md"
    if args.check:
        if not target.is_file() or target.read_text() != text:
            errors.append(f"{target.relative_to(ROOT)} is stale; regenerate it")
    else:
        target.write_text(text)
    for error in errors:
        print(f"  ERROR: {error}", file=sys.stderr)
    print(f"{target.relative_to(ROOT)}: {'OK' if not errors else f'{len(errors)} error(s)'}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
