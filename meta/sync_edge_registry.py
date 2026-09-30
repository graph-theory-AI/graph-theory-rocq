#!/usr/bin/env python3
"""Reconcile meta/edge_waves.json (the human-curated edge registry) with the
machine-harvested edge graph meta/dependency_graph.json.

The graph (harvested from the `(*@EDGE ...*)` annotations next to the theorems) is
the source of truth for the STATE of an edge; the registry adds provenance
(wave, tier, prover, reviewer) and the reasons of documented non-edges.

    python3 meta/sync_edge_registry.py            # dry run: print the changes
    python3 meta/sync_edge_registry.py --write    # apply them
    python3 meta/sync_edge_registry.py --check    # exit 1 on any pending change

Rules (per graph edge, keyed "<from>-><to>:<kind>"):
  * status verified/conditional/refuted-direction  -> registry state, proof, external
  * status candidate with a note starting "BLOCKED" -> state blocked (reason = note)
  * status candidate otherwise                      -> state candidate
  * a note is copied into `reason` for refuted-direction/blocked entries when the
    registry reason is empty; `note` is refreshed from the annotation note.
  * `proved_by` is filled with "--proved-by <text>" (default: the registry's wave)
    when an entry becomes verified/conditional and has no prover yet.
Registry entries without a graph edge are left untouched (planned or absorbed edges).
"""
import json
import sys
from pathlib import Path

META = Path(__file__).resolve().parent
GRAPH = META / "dependency_graph.json"
REG = META / "edge_waves.json"


def main() -> int:
    argv = sys.argv[1:]
    write = "--write" in argv
    check = "--check" in argv
    proved_by = None
    if "--proved-by" in argv:
        proved_by = argv[argv.index("--proved-by") + 1]
    graph = json.loads(GRAPH.read_text())
    reg = json.loads(REG.read_text())
    entries = reg["edges"]
    changes = []
    for e in graph["edges"]:
        key = f"{e['from']}->{e['to']}:{e['kind']}"
        st = e["status"]
        note = e.get("note", "") or ""
        if st == "candidate":
            state = "blocked" if note.upper().startswith("BLOCKED") else "candidate"
        else:
            state = st
        ent = entries.get(key)
        if ent is None:
            ent = {"gc": None, "tier": "", "wave": "", "host": e.get("package", ""),
                   "state": state, "proof": None, "external": [], "reason": "",
                   "proved_by": None, "reviewed_by": None, "reviewed_at": None, "note": ""}
            cite = e.get("cite", "") or ""
            if cite.startswith("gc:"):
                ent["gc"] = cite[3:].split(";")[0].split(",")[0].strip()
            entries[key] = ent
            changes.append((key, "NEW", state))
        upd = {}
        if ent.get("state") != state:
            upd["state"] = state
        if e.get("proof") and ent.get("proof") != e["proof"]:
            upd["proof"] = e["proof"]
        ext = e.get("external", []) or []
        if ext and ent.get("external") != ext:
            upd["external"] = ext
        if state in ("refuted-direction", "blocked") and note and not ent.get("reason"):
            upd["reason"] = note
        if note and ent.get("note") != note:
            upd["note"] = note
        if state in ("verified", "conditional") and not ent.get("proved_by"):
            upd["proved_by"] = proved_by or (f"wave {ent.get('wave')} agent (Claude Opus 5), 2026-09-24"
                                              if ent.get("wave") else "Claude Opus 5 subagent, 2026-09-24")
        if not ent.get("host") and e.get("package"):
            upd["host"] = e["package"]
        if upd:
            changes.append((key, "UPDATE", ", ".join(f"{k}={str(v)[:40]!r}" for k, v in upd.items())))
            ent.update(upd)
    for key, kind, what in changes:
        print(f"{kind:6} {key}: {what}")
    print(f"{len(changes)} change(s)")
    if write and changes:
        REG.write_text(json.dumps(reg, indent=1, ensure_ascii=False) + "\n")
        print(f"wrote {REG}")
    if check and changes:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
