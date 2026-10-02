#!/usr/bin/env python3
"""Generate and verify the migration report of one library-migration family.

    python3 meta/library_migration_report.py FAMILY           # write meta/LIBRARY_MIGRATION_<FAMILY>.md
    python3 meta/library_migration_report.py FAMILY --check   # verify only; exit 1 on any mismatch
    python3 meta/library_migration_report.py --hash-stdin NAME [NAME ...]
        # print the snapshot hashes of the declarations NAME found in the Rocq text read on stdin
        # (e.g. `git show REV:path | python3 meta/library_migration_report.py --hash-stdin x15_matching`)

The family's entry in meta/library_primitives.json carries the migration record:

  legacy_snapshots: one object per frozen declaration (helper or statement):
      source            qualified name of the original declaration
      source_path       repository path of the original file
      source_lines      "a-b", the lines frozen (documentation only)
      legacy            qualified name of the frozen copy (inside a `Module Legacy`)
      body_hash         sha256 of the normalized body of the ORIGINAL declaration at freeze time
      declaration_hash  sha256 of the normalized original declaration (as library_inventory.py)
      base_rev          git revision of the frozen text
      verbatim_of       optional: the snapshot repeats, under the local name, the BODY of this
                        other frozen declaration (used for re-frozen pre-M1 edge sets); only the
                        body hash is compared then
  helper_certificates:    [{"source": qualified helper, "theorem": qualified compat theorem}]
  statement_certificates: [{"statement": qualified live statement, "legacy": qualified frozen copy,
                            "theorem": qualified compat theorem, "row": corpus row or "no corpus
                            row", "status": the documented row/leg status}]
  semantic_classes:       as in the M1 record: {name: {members, verdict, state, certificates, ...}}
  unchanged_live_helpers: [{"source": qualified live helper a frozen statement still uses as it is,
                            "declaration_hash", "body_hash": its hashes at freeze time}]

Checks performed (all are also printed in the report):
  1. every frozen copy hashes exactly as the recorded original (declaration hash, or body hash
     for verbatim_of snapshots), i.e. the Legacy text is verbatim;
  2. if `git` can show base_rev, the recorded hashes are re-derived from that revision;
  3. every helper/statement certificate theorem exists in its module and its statement mentions
     both the frozen and the live name;
  4. consumers of every migrated source: direct (same file, from the regenerated inventory),
     chain (declarations of the Legacy modules), and cross-module (repository-wide references
     outside the defining file and the migration certificates).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import library_inventory as INV  # noqa: E402

ROOT = INV.ROOT
META = INV.META
NAMESPACES = {
    "GTBase": "base", "Chromatic": "chromatic-theory", "Hamilton": "hamiltonicity-theory",
    "Hom": "homomorphism-theory", "Cycle": "cycle-theory", "Minor": "minor-theory",
    "Packing": "packing-theory", "Reconstruction": "reconstruction-theory",
    "Hypergraph": "hypergraph-theory", "Topological": "topological-graph-theory",
    "GTMisc": "graph-theory-misc", "Spectral": "spectral-graph-theory",
    "Extremal": "extremal-graph-theory", "Infinite": "infinite-graph-theory",
    "Digraph": "digraph-theory",
}
MODULE_RE = re.compile(r"^\s*Module\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.", re.M)
END_RE = re.compile(r"^\s*End\s+([A-Za-z_][A-Za-z0-9_']*)\s*\.", re.M)


def module_path(qualified: str) -> tuple[Path, list[str]]:
    """Resolve `Ns.dir.file.Mod.name` to (file path, [Mod..., name])."""
    parts = qualified.split(".")
    package = NAMESPACES.get(parts[0])
    if package is None:
        raise ValueError(f"unknown namespace in {qualified}")
    for cut in range(len(parts) - 1, 1, -1):
        candidate = ROOT / package / "theories" / Path(*parts[1:cut]).with_suffix(".v")
        if candidate.is_file():
            return candidate, parts[cut:]
    raise FileNotFoundError(f"no source file for {qualified}")


def declarations(text: str) -> dict[str, tuple[str, str]]:
    """Map name -> (kind, normalized declaration command) at top level of `text`."""
    clean = INV.strip_comments(text)
    out: dict[str, tuple[str, str]] = {}
    for match in INV.DECL_RE.finditer(clean):
        kind, name = match.groups()
        command = clean[match.start():INV.sentence_end(clean, match.start())]
        out.setdefault(name, (kind, command))
    return out


def module_region(text: str, modules: list[str]) -> str:
    """Return the text of nested `Module A. ... End A.` regions."""
    region = INV.strip_comments(text)
    for module in modules:
        start = None
        for match in MODULE_RE.finditer(region):
            if match.group(1) == module:
                start = match.end()
                break
        if start is None:
            raise ValueError(f"module {module} not found")
        end = None
        for match in END_RE.finditer(region, start):
            if match.group(1) == module:
                end = match.start()
                break
        region = region[start:end]
    return region


def split_body(command: str, name: str) -> str:
    after = command[command.index(name) + len(name):]
    body = after.split(":=", 1)[1] if ":=" in after else ""
    return INV.normalize_space(body.rstrip("."))


def hashes_of(command: str, name: str) -> dict[str, str]:
    return {
        "declaration_hash": INV.sha256(INV.normalize_space(command)),
        "body_hash": INV.sha256(split_body(command, name)),
    }


def find_declaration(qualified: str) -> tuple[str, str]:
    path, inner = module_path(qualified)
    name = inner[-1]
    text = path.read_text()
    region = module_region(text, inner[:-1]) if len(inner) > 1 else INV.strip_comments(text)
    decls = declarations(region)
    if name not in decls:
        raise ValueError(f"{qualified}: declaration {name} not found in {path.relative_to(ROOT)}")
    return decls[name]


def git_show(rev: str, path: str) -> str | None:
    try:
        proc = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, text=True,
                              capture_output=True, check=False)
    except OSError:
        return None
    return proc.stdout if proc.returncode == 0 else None


def references(name: str, skip: set[Path]) -> list[str]:
    """Repository-wide textual references to the short name, comments stripped; a file that
    declares its own `name` (a distinct, same-named declaration) is flagged as such."""
    pattern = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])")
    hits: list[str] = []
    for path in sorted(ROOT.glob("*/theories/**/*.v")):
        if path in skip:
            continue
        clean = INV.strip_comments(path.read_text())
        own = name in declarations(clean)
        for line_no, line in enumerate(clean.splitlines(), 1):
            if pattern.search(line):
                hits.append(f"{path.relative_to(ROOT)}:{line_no}"
                            + (" (declares its own, distinct `" + name + "`)" if own else ""))
    return hits


def check_theorem(theorem: str, frozen: str, live: str) -> tuple[bool, str]:
    try:
        kind, command = find_declaration(theorem)
    except (ValueError, FileNotFoundError) as exc:
        return False, str(exc)
    head = command.split(":=", 1)[0]
    frozen_short = ".".join(frozen.split(".")[-2:])  # Legacy.name
    live_short = live.split(".")[-1]
    ok = kind in {"Lemma", "Theorem", "Corollary", "Proposition", "Fact"} \
        and frozen_short in head and re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(live_short)}(?![A-Za-z0-9_'])", head) is not None
    return ok, "" if ok else f"{theorem}: statement does not relate {frozen_short} and {live_short}"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("family", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--registry", default=str(INV.REGISTRY))
    parser.add_argument("--out")
    parser.add_argument("--hash-stdin", nargs="+", metavar="NAME")
    args = parser.parse_args(argv)

    if args.hash_stdin:
        decls = declarations(sys.stdin.read())
        for name in args.hash_stdin:
            if name not in decls:
                print(json.dumps({"name": name, "error": "not found"}))
                continue
            print(json.dumps({"name": name, **hashes_of(decls[name][1], name)}))
        return 0
    if not args.family:
        parser.error("FAMILY is required")

    registry = json.loads(Path(args.registry).read_text())
    spec = registry["primitives"][args.family]
    errors: list[str] = []
    lines: list[str] = []
    add = lines.append

    add(f"# Library migration record: family `{args.family}`")
    add("")
    add(f"> Generated by `python3 meta/library_migration_report.py {args.family}`; "
        f"`--check` re-verifies every table below. Registry status: `{spec.get('status')}`, "
        f"fidelity `{spec.get('fidelity')}`, canonical `{spec.get('canonical_name')}` "
        f"(owner `{spec.get('owner')}`), reviewed_by `{spec.get('reviewed_by')}`.")
    add("")
    if spec.get("migration_notes"):
        add("## Scope")
        add("")
        add(spec["migration_notes"])
        add("")

    add("## Source definitions and classification")
    add("")
    add("| Qualified definition | Semantic class | State | Verdict |")
    add("|---|---|---|---|")
    classes = spec.get("semantic_classes", {})
    for source in spec.get("source_definitions", []):
        owner = next((k for k, v in classes.items() if source in v.get("members", [])), "(unclassified)")
        cls = classes.get(owner, {})
        if owner == "(unclassified)":
            errors.append(f"{source}: not in any semantic class")
        add(f"| `{source}` | {owner} | {cls.get('state', '')} | {cls.get('verdict', '')} |")
    add("")
    for name, cls in classes.items():
        add(f"- **{name}** ({len(cls.get('members', []))}): {cls.get('note', '')}")
    add("")

    add("## Frozen legacy snapshots (verbatim check)")
    add("")
    add("| Original (base rev) | Lines | Frozen copy | Declaration hash | Body hash | Verbatim |")
    add("|---|---|---|---|---|---|")
    for snap in spec.get("legacy_snapshots", []):
        try:
            _, legacy_cmd = find_declaration(snap["legacy"])
        except (ValueError, FileNotFoundError) as exc:
            errors.append(str(exc))
            add(f"| `{snap['source']}` | {snap.get('source_lines', '')} | `{snap['legacy']}` | | | MISSING |")
            continue
        legacy_name = snap["legacy"].split(".")[-1]
        got = hashes_of(legacy_cmd, legacy_name)
        if snap.get("verbatim_of"):
            ok = got["body_hash"] == snap["body_hash"]
            how = f"body of `{snap['verbatim_of']}`"
        else:
            ok = got["declaration_hash"] == snap["declaration_hash"] and got["body_hash"] == snap["body_hash"]
            how = "declaration"
        verdict = f"yes ({how})" if ok else "NO"
        if not ok:
            errors.append(f"{snap['legacy']}: frozen text differs from the recorded original "
                          f"({got} vs recorded {snap.get('declaration_hash')}/{snap.get('body_hash')})")
        rev = snap.get("base_rev")
        original = git_show(rev, snap["source_path"]) if rev and not snap.get("verbatim_of") else None
        if original is not None:
            decls = declarations(original)
            source_name = snap["source"].split(".")[-1]
            if source_name in decls:
                base = hashes_of(decls[source_name][1], source_name)
                if base != {"declaration_hash": snap["declaration_hash"], "body_hash": snap["body_hash"]}:
                    errors.append(f"{snap['source']}: recorded hashes are not those of {rev}")
                    verdict += "; base-rev hash MISMATCH"
                else:
                    verdict += f"; re-derived from {rev}"
            else:
                errors.append(f"{snap['source']}: not found at {rev}")
        add(f"| `{snap['source']}` | {snap.get('source_lines', '')} | `{snap['legacy']}` | "
            f"`{snap['declaration_hash'][:12]}…` | `{snap['body_hash'][:12]}…` | {verdict} |")
    add("")

    unchanged = spec.get("unchanged_live_helpers", [])
    if unchanged:
        add("## Unaffected live helpers used by frozen statements (text unchanged)")
        add("")
        add("| Live helper | Declaration hash | Body hash | Unchanged |")
        add("|---|---|---|---|")
        for item in unchanged:
            try:
                _, cmd = find_declaration(item["source"])
                got = hashes_of(cmd, item["source"].split(".")[-1])
                ok = got["declaration_hash"] == item["declaration_hash"] and got["body_hash"] == item["body_hash"]
            except (ValueError, FileNotFoundError) as exc:
                errors.append(str(exc))
                ok = False
            if not ok:
                errors.append(f"{item['source']}: live text differs from the recorded original")
            add(f"| `{item['source']}` | `{item['declaration_hash'][:12]}…` | `{item['body_hash'][:12]}…` | {'yes' if ok else 'NO'} |")
        add("")

    add("## Helper certificates")
    add("")
    add("| Source helper | Frozen copy | Theorem | Found |")
    add("|---|---|---|---|")
    legacy_by_source = {s["source"]: s["legacy"] for s in spec.get("legacy_snapshots", [])}
    for cert in spec.get("helper_certificates", []):
        frozen = legacy_by_source.get(cert["source"], cert.get("legacy", ""))
        ok, msg = check_theorem(cert["theorem"], frozen, cert["source"])
        if not ok:
            errors.append(msg)
        add(f"| `{cert['source']}` | `{frozen}` | `{cert['theorem']}` | {'yes' if ok else 'NO'} |")
    add("")

    add("## Statement certificates (one per affected row)")
    add("")
    add("| Statement | Corpus row | Documented status | Frozen copy | Theorem | Found |")
    add("|---|---|---|---|---|---|")
    for cert in spec.get("statement_certificates", []):
        ok, msg = check_theorem(cert["theorem"], cert["legacy"], cert["statement"])
        if not ok:
            errors.append(msg)
        add(f"| `{cert['statement']}` | {cert.get('row', '')} | {cert.get('status', '')} | "
            f"`{cert['legacy']}` | `{cert['theorem']}` | {'yes' if ok else 'NO'} |")
    add("")

    add("## Consumers of the migrated sources")
    add("")
    inventory = INV.build_inventory()
    helpers = {h["qualified_name"]: h for h in inventory["helpers"]}
    migrated = [m for cls in classes.values() if cls.get("state", "").startswith("migrated")
                for m in cls.get("members", [])]
    certificate_files = {module_path(c["theorem"])[0] for c in spec.get("statement_certificates", [])}
    for source in migrated:
        helper = helpers.get(source)
        add(f"### `{source}`")
        add("")
        if helper is None:
            errors.append(f"{source}: missing from the inventory")
            add("- missing from the inventory")
            add("")
            continue
        add(f"- live body now: `{split_body(find_declaration(source)[1], source.split('.')[-1])}`")
        add(f"- direct same-file consumers (inventory): "
            + (", ".join(f"`{c}`" for c in helper["direct_consumers"]) or "none"))
        path, _ = module_path(source)
        hits = references(source.split(".")[-1], {path} | certificate_files)
        add("- cross-module references (comments stripped, certificates excluded): "
            + (", ".join(f"`{h}`" for h in hits) or "none"))
        add("")

    add("## Compatibility and API theorems registered")
    add("")
    for name in spec.get("compatibility_theorems", []):
        try:
            find_declaration(name)
            add(f"- `{name}`")
        except (ValueError, FileNotFoundError) as exc:
            errors.append(str(exc))
            add(f"- `{name}` MISSING")
    add("")
    for name in spec.get("api_theorems", []):
        try:
            find_declaration(name)
            add(f"- API `{name}`")
        except (ValueError, FileNotFoundError) as exc:
            errors.append(str(exc))
            add(f"- API `{name}` MISSING")
    add("")

    add("## Verification summary")
    add("")
    add(f"- checks failed: {len(errors)}")
    for error in errors:
        add(f"  - {error}")
    rendered = "\n".join(lines) + "\n"
    if args.check:
        for error in errors:
            print(f"  ERROR: {error}", file=sys.stderr)
        print(f"migration report check for {args.family}: {'OK' if not errors else 'FAILED'}")
        return 1 if errors else 0
    out = Path(args.out) if args.out else META / f"LIBRARY_MIGRATION_{args.family.upper().replace('-', '_')}.md"
    out.write_text(rendered)
    print(f"wrote {out.relative_to(ROOT) if out.is_relative_to(ROOT) else out}; "
          f"{len(errors)} check(s) failed")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
