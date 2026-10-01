# Library Migration M1: Simple Edge Vocabulary

> Implementation status: complete on 2026-07-23
>
> Registry status: `deprecated` because the 31 historical names remain as
> transparent compatibility aliases for one migration cycle.

## Scope

M1 promotes the repeated simple-graph edge vocabulary into
`GTBase.simple_edges` without changing any conjecture statement, manifest row,
leg status, provenance record, or accepted assumption.

The M0 inventory found 31 local definitions, rather than the earlier estimate
of 27. All 31 are now classified and migrated:

| Frozen representation | Count | Verdict | Machine certificate |
|---|---:|---|---|
| existential adjacent endpoints | 29 | equivalent | `simple_edge_setE` plus alias-specific compatibility lemmas |
| cardinality two and `cliqueb` | 2 | equivalent | `simple_edge_set_cliqueE` plus X100/X102 transport lemmas |

There are no non-equivalent variants in this family.

## Canonical API

`base/theories/simple_edges.v` owns the stable adapter:

- `simple_edge_set`
- `simple_edge_incident`
- `simple_edge_count`
- `delete_edges_rel` and `delete_edges_graph`
- `delete_edge_graph`

The edge set is proved extensionally equal to upstream
`GraphTheory.sgraph.sg_edge_set`. The adapter retains the corpus's useful
`{set {set G}}` representation and exposes upstream-compatible membership
lemmas.

`GTBase.graph_metric.graph_edge_set` remains available as a transparent
compatibility name. New code should use `simple_edge_set`.

## Faithfulness Evidence

The migration checks the semantic points that name matching alone could not:

1. `adjacent_neq` proves that the omitted `x != y` guard follows from simple
   graph irreflexivity.
2. `simple_edge_set_cliqueE` proves that cardinality-two cliques are exactly the
   same edge sets. This discharges the X100 and X102 representation mismatch.
3. `simple_edge_incidentE` identifies incidence with endpoint membership for a
   valid edge.
4. `delete_edge_graphE`, `delete_edge_removes`, and
   `delete_edge_preserves_other` prove that deletion removes exactly the named
   undirected edge and preserves every other adjacency.
5. `simple_edge_count_K0`, `simple_edge_count_K1`,
   `simple_edge_count_K2`, and `simple_edge_count_K3` ground the empty,
   singleton, one-edge, and triangle cases.

Frozen pre-migration bodies live in non-reexported
`*/theories/migration/simple_edges.v` modules. Every historical helper has an
alias-specific equality theorem. X25, X64, and X142 have direct frozen
old/new statement equivalences. X100 and X102 have explicit transport proofs
because their frozen bodies are extensionally, but not definitionally, equal
to the canonical adapter.

## Gate Integration

`meta/check_library_migration.py` reads the registry, resolves the same pinned
Rocq environment as milestone acceptance, force-builds the registry-owned source
targets through each package `_CoqProject`, and rejects:

- a missing canonical declaration;
- a missing API or compatibility theorem;
- a theorem with non-empty `Print Assumptions`;
- a theorem module that cannot be compiled through its package `_CoqProject`.

The current assumptions gate checks 46 theorems across eight modules.
`meta/library_inventory.py` also resolves all public declarations named by the
registry instead of accepting non-empty strings.

Changed-wave CI now treats any `base/theories/*.v` edit as a reverse-dependency
change: it runs the root `make all` package topology and the migration
assumptions gate, rather than compiling only `base`.

## Compatibility Debt

The 31 historical helper names have 48 direct declaration consumers. They are
intentionally retained as transparent aliases so existing import paths and
formal names remain stable. Their registry state is `deprecated`, not
`complete`.

Removing those aliases is a separate compatibility-cycle change. It requires
rewriting the 48 consumers, proving any additional statement-level
certificates exposed by that rewrite, and deciding whether external users need
a release-level deprecation window.

## Review Status

The implementation has a complete kernel-checked equivalence and assumptions
audit. `reviewed_by` remains unset in `meta/library_primitives.json` until a
distinct reader records an API and semantic review; this is not inferred from
the author-side machine checks.
