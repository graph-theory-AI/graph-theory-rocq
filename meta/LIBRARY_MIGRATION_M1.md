# Library Migration M1: Simple Edge Vocabulary

> Implementation status: complete on 2026-07-23; reworked on 2026-10-02 to target the
> upstream edge set directly after `GTBase.common` (WP4b) landed on main.
>
> Registry status: `deprecated` because the 31 historical names remain as
> transparent compatibility aliases for one migration cycle.

## Scope

M1 retires the repeated simple-graph edge vocabulary in favour of the upstream
`GraphTheory.sgraph.sg_edge_set` (`E(G)`) without changing any conjecture statement, manifest row,
leg status, provenance record, or accepted assumption.

The M0 inventory found 31 local definitions, rather than the earlier estimate
of 27. All 31 are now classified and migrated:

| Frozen representation | Count | Verdict | Machine certificate |
|---|---:|---|---|
| existential adjacent endpoints | 29 | equivalent | `GTBase.common.sg_edge_setE` plus alias-specific compatibility lemmas |
| cardinality two and `cliqueb` | 2 | equivalent | `GTBase.common.sg_edge_set_cliqueE` plus X100/X102 transport lemmas |

There are no non-equivalent variants in this family.

## Canonical API

There is no adapter module. Each of the 31 local definitions now unfolds to
`sg_edge_set G`, the upstream edge set written `E(G)`, and the shared lemmas
live in `GTBase.common`:

- `sg_edge_setE`: `E(G)` equals the adjacent-endpoint comprehension used by
  29 local copies;
- `in_sg_edge_set`: membership in `E(G)` in that comprehension form;
- `sg_edge_set_cliqueE`: `E(G)` equals the two-element-clique comprehension
  used by X100 and X102.

The historical `xNN_edge_set` names remain as transparent aliases for one
migration cycle. `GTBase.graph_metric.graph_edge_set` is untouched by this
milestone. New code should write `E(G)`.

## Faithfulness Evidence

The migration checks the semantic points that name matching alone could not:

1. `GTBase.common.sg_edge_setE` proves that the adjacent-endpoint comprehension
   used by 29 local copies is exactly `E(G)`; the omitted `x != y` guard follows
   from simple-graph irreflexivity inside that proof.
2. `GTBase.common.sg_edge_set_cliqueE` proves that cardinality-two cliques are
   exactly the edges. This discharges the X100 and X102 representation mismatch.
3. Each package's `theories/migration/simple_edges.v` freezes the historical
   definitions verbatim (`Legacy.*`) and proves every alias equal to its frozen
   form (`*_edge_set_compat`), by unfolding the alias and rewriting with the
   certificate above.
4. Statement-level compatibility is proved for the rows whose vocabulary was
   rebuilt from the frozen definitions: X64, X100 and X142 (chromatic), X102
   (misc) and X25 (packing).
5. The `xNN_edge_setE` bridging lemmas that the 2026-09-24 re-sync added for
   the misc, packing and topological copies now hold by reflexivity and were
   reduced to `by []`.

`Packing.conjectures.X15alone.x15_edge_set`, a scratch duplicate kept outside
the package build, is registered but neither retargeted nor certified.

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
