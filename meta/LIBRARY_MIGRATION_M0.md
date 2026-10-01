# Library Migration M0 Implementation Record

> Implemented 2026-07-22 on branch `codex/library-migration-m0`.

## Scope

M0 establishes the inventory, registry, upstream audit, and prospective debt
freeze required by `meta/LIBRARY_MIGRATION_PLAN.md`. It does not rewrite any
conjecture or select a new canonical implementation.

## Deterministic Inventory

`meta/library_inventory.py` scans top-level declarations in non-grounding
`*/theories/conjectures/*.v` files. It excludes statement definitions and records:

- qualified and local names;
- declaration kind, source path, and line;
- normalized wave-independent name;
- signature, body, and declaration hashes;
- normalized signature and body-shape hashes;
- dependencies on declarations in the same file;
- repeated normalized-name, signature-shape, and body-shape groups.

The committed `meta/library_helper_inventory.json` baseline contains:

| Measure | Count |
|---|---:|
| Conjecture source files | 291 |
| Non-statement helper declarations | 1,950 |
| Wave-prefixed helpers | 1,111 |
| Repeated normalized-name families | 167 |

This baseline is smaller than the earlier raw grep count because grounding,
implication, transient probe files, and `_statement` declarations are excluded.
`python3 meta/library_inventory.py --check` rejects any unrefreshed drift.

## Seeded Migration Registry

`meta/library_primitives.json` initially tracks nine families:

| Family | Local definitions | Initial upstream result |
|---|---:|---|
| simple graph edge set | 31 | `GraphTheory.sgraph.sg_edge_set` candidate |
| stable set | 10 | `GraphTheory.dom.stable` candidate |
| induced-free | 9 | induced-subgraph building blocks only |
| minimum degree at least | 9 | no direct candidate found |
| path vertices | 9 | `GraphTheory.digraph.nodes` candidate with representation checks |
| uniform hypergraph | 6 | no matching upstream hypergraph API |
| matching | 5 | `GraphTheory.connectivity.matching`, but family must split by representation |
| proper colouring | 4 | upstream partition representation differs from local colour functions |
| tree decomposition | 4 | `GraphTheory.treewidth.sdecomp` candidate |

All remain `PENDING` and `proposed` or `auditing`. An upstream name is a candidate,
not a fidelity verdict. M1 must prove compatibility before any status becomes
`canonical` or `migrating`.

The validator checks registry schema, ownership, status, fidelity state, source
declaration existence, normalized-family coverage, measured direct consumer
count, and upstream-audit evidence. Public or migrating entries require a
canonical name and a non-pending fidelity verdict.

## X211+ Ownership Contract

Every non-statement declaration in a prospective wave's statement file must have
an entry in the wave-level `helper_ownership` object:

```json
{
  "helper_ownership": {
    "x211_exceptional_family": {
      "classification": "paper_specific",
      "reason": "Encodes the exceptional family named only in this source row."
    },
    "x211_edges": {
      "classification": "compatibility_alias",
      "primitive": "simple-graph-edge-set",
      "compatibility_theorem": "Chromatic.migration.simple_edges.x211_edges_compat",
      "reason": "Temporary proved alias retained during the edge migration."
    }
  }
}
```

The gate rejects missing entries, stale entries, unknown classifications, short
or absent reasons, and aliases that are not listed in the selected primitive's
`source_definitions`, do not match its normalized family, or lack a registered
compatibility theorem. Lemma/Theorem/Instance helpers are inventoried, and only
manifest-owned formal names receive the statement exemption. A local
reusable implementation is not an allowed classification: it must move to its
owner module or be a temporary registered compatibility alias.

The policy is prospective. X1-X210 duplicate families remain warning-only until
their concept family enters a migration batch.

## Gate Integration

- `make audit` validates inventory drift and the registry, then reports the
  legacy duplicate-family backlog.
- `make gate` additionally enforces ownership metadata for every X211+ wave.
- `check_milestone.py` invokes the same ownership check for a prospective phase,
  preventing direct milestone acceptance from bypassing the repository gate.
- `make mutation` runs the inventory and ownership-parser self-test.

## Known Limits

- Declaration parsing is syntax-aware for comments and command boundaries but is
  not a Rocq AST parser; checker scratch prefixes are excluded from both inventory
  and repository-declaration scans.
- Name and body-shape grouping discovers candidates; it does not assert semantic
  equivalence.
- The initial matching family intentionally mixes representations and is marked
  for splitting before migration.
- Reverse dependency CI for changes to canonical foundations was deferred to
  M1 and is now implemented by `meta/changed_milestones.py`.
- No helper or statement has been rewritten in M0.

## M0 Exit Status

- Complete helper inventory: done.
- Initial upstream audit: done for the nine seeded families.
- Registry and drift checker: done.
- Prospective ownership classification: enforced.
- Legacy duplicate report: warning-only and wired into `make audit`.
- First migration family selected: simple graph edge sets, pending M1.
