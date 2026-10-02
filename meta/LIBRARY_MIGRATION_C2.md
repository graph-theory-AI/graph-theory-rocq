# Library Migration C2: Perfect Matchings

> Batch C, second family (meta/LIBRARY_MIGRATION_PLAN.md section 15), implemented
> 2026-10-02 on top of the C1 follow-up (base `baad954`).
>
> Registry status: `deprecated`, because all three historical names remain as
> transparent compatibility aliases for one migration cycle (the M1 convention).
> `reviewed_by` stays unset until the step-10 review is recorded.

The generated report `meta/migration_reports/perfect_matching.md` (from
`meta/migration_reports/perfect_matching.spec.json`, via `meta/migration_report.py`)
is a compact summary. The spec records the inventory body hash of every frozen
declaration and regenerates the full hashes, git blobs, per-row theorem names,
consumer list and checks on demand with `--details DIR`. This record explains
the decisions.

## Scope

| Group | Definitions | Treatment |
|---|---|---|
| exact-one incidence | `Cycle.conjectures.X24.x24_perfect_matching`, `Packing.conjectures.X18.x18_perfect_matching`, `Packing.conjectures.X25.x25_perfect_matching` | migrated: each now unfolds to `GTBase.common.perfect_matching M` |
| name match only | `Cycle.conjectures.U10.is_perfect_matching`, `Cycle.conjectures.U10.perfect_matching_cover` | distinct: U10's multigraph edge type (`{set edge G}`, `subdeg`), a different carrier; untouched |

Edge partitions (`x15_edge_partition`, X18) and edge families are the next family.

## Protocol (section 9)

1. **Discover.** Three source definitions, one affected row each: X24 through
   `x24_one_factorization`, X18 directly (`knn_fair_perfect_matching_statement`),
   X25 through `x25_perfect_one_factorization`. Cross-module consumers:
   `vocabulary_packing.v` only. X18's chain was frozen by C1
   (`Packing.migration.matching.X18Legacy`), X25's by M1
   (`Packing.migration.simple_edges.X25Legacy`).
2. **Compare.** All three bodies read "every member is an edge and every vertex lies
   in exactly one member" (X18 states the edge clause through `x15_matching`, C1's
   alias of `connectivity.matching`). The canonical is `matching M /\ cover M = [set: G]`.
   Exactly one = at most one (the matching clause) and at least one (the cover
   clause), so the two readings are logically equivalent with no guard
   (`perfect_matching_exactly_oneP`); they are not convertible. Corner cases agree:
   on the empty graph `set0` is a perfect matching in both; a family with a
   non-edge member (a loop, `set0`, a non-adjacent pair) is rejected by both. No body
   is defective.
3. **Specify.** The contract is the doc comment of `GTBase.common.perfect_matching`:
   a matching covering every vertex; degenerate cases listed there (empty graph,
   nonempty graph with `set0`, loop members, odd order, `K_2`, `K_3`).
4. **Audit upstream.** coq-graph-theory 0.9.7 has `connectivity.matching` and no
   perfect-matching predicate. The existing `GTBase.common.perfect_matching` (WP4b,
   with `perfect_matching_K2` and `not_perfect_matching0`) is kept unchanged as the
   canonical.
5. **Implement.** common.v's perfect-matching section gains `perfect_matching_matching`,
   `perfect_matching_cover`, `perfect_matching_edge` and the presentation lemma
   `perfect_matching_exactly_oneP` (narrow edit; A2's deletion block is separate).
6. **Ground.** Same section: `perfect_matching0_K0` (the empty graph),
   `not_perfect_matching_loop`, `card_perfect_matching` (`#|G| = 2 * #|M|`),
   `not_perfect_matching_odd`, `not_perfect_matching_K3`, next to the existing
   `perfect_matching_K2` and `not_perfect_matching0`. `meta/foundation_fidelity/perfect-matching.json`
   enrols `perfect_matching` in `GTBase.common` (override, FAITHFUL) with these
   lemmas as machine evidence. The public client
   `base/theories/examples/perfect_matching.v` (plan section 11) imports `GTBase.base`
   only and exercises the positive and negative API.
7. **Freeze.** `Cycle.migration.perfect_matching` holds `Legacy` (the X24 helper
   verbatim and the pre-M1 comprehension of `x24_edge_set`, checked against 061154c)
   and `X24Legacy` (the chain and the statement, `Legacy.`-qualified and prefix-stripped).
   The X18 and X25 frozen bodies of C1 and M1 are preserved verbatim; the report
   checks all of them against the source text at their commits modulo the listed
   substitutions and records the baseline declaration hashes and git blobs.
8. **Bridge.** `x24_perfect_matching_compat` (cycle), and C1's
   `x18_perfect_matching_compat` and M1's `x25_perfect_matching_compat` (re-proved
   through the presentation lemma) prove each frozen helper equivalent to its alias.
   The per-area entry point `Packing.migration.perfect_matching` states this family's
   two helper certificates and two row certificates over the same frozen bodies,
   proved from those adapted theorems, so no snapshot is duplicated. Chain lemmas:
   `x24_edge_set_compat`, `x24_one_factorization_compat`,
   `x25_perfect_one_factorization_compat` (M1).
9. **Re-encode.** The three alias bodies now read `perfect_matching M`. Statement texts,
   doc blocks, manifest rows and leg states are unchanged; the report checks this. Per-row
   theorems: `Cycle.migration.perfect_matching.one_factorization_long_rainbow_cycle_statement_compat`,
   `Packing.migration.perfect_matching.knn_fair_perfect_matching_statement_compat` and
   `Packing.migration.perfect_matching.kotzig_perfect_one_factorization_statement_compat`
   (the last two over C1's and M1's frozen statements, from their unchanged certificates). Proof-only knock-on edit:
   `vocabulary_packing.x18_perfect_matching_equiv_x25_perfect_matching` is reflexive.
10. **Independently review.** Pending: arthur (cross-review), coordinator (final
    statement-level theorem check).
11. **Gate.** See the board announcement for the gate results of the commit.
12. **Deprecate.** The aliases stay; `consumers_remaining` counts their 3 same-file
    direct consumers.

## Preserved statuses and discrepancies

- X24: open question row encoded in its affirmative form; the parity hypothesis note.
- X18: partial row (m = 2, 3 in the source).
- X25: open; `col` typed on all vertex sets, only its restriction to edges matters.

## Interaction with M1 and C1

X24's chain reaches the M1 alias `x24_edge_set`: its pre-M1 comprehension is re-frozen as
`Legacy.x24_edge_set` (the text M1 froze as `Cycle.migration.simple_edges.Legacy.edge_set`),
so the X24 certificate is end-to-end over both migrations. X18's statement is frozen by C1
over `Legacy.x15_matching` and the pre-M1 `Legacy.x15_edge_set`; X25's by M1 over
`Legacy.edge_set`. Both stay as they are; only the two helper certificates that unfolded
the exact-one incidence are re-proved, so no statement-level certificate changes.

## Tooling and registry

The family document is `meta/library_primitives/perfect-matching.json`; its fidelity
fragment `meta/foundation_fidelity/perfect-matching.json` enrols `perfect_matching`
in `GTBase.common` (FAITHFUL) with the API and grounding lemmas as machine evidence.
The public client also constructs the two disjoint edges `{0,1}` and `{2,3}`
as a perfect matching of `K_4`, alongside the `K_0`, `K_2` and negative `K_3` cases.

The compact report is generated by `meta/migration_report.py perfect_matching --write`
(`--details DIR` for the full evidence, `--check --kernel` against built modules); the
spec records the inventory body hash of every frozen declaration and the hashes of the
two unchanged live X24 helpers.

## Evidence kept outside the report

`Print All Dependencies` of the three frozen and three live statements and `Print
Assumptions` of every certificate, run through the pinned image, under
`/srv/graph-theory-rocq/coordination/evidence/C2-perfect_matching/` (outside the
repository).
