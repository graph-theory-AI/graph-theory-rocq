# Library Migration C1: Matchings

> Batch C, first family (meta/LIBRARY_MIGRATION_PLAN.md section 15), implemented
> 2026-10-02 against `work/coordinator` at 9e03072, re-laid out onto A1's
> certificate convention after the merge 03742d1.
>
> Registry status: `migrating`, because only the compiled simple-graph subgroup of
> the six name-matched definitions is migrated; the three historical names remain
> as transparent compatibility aliases for one migration cycle (the M1 convention).
> Arthur approved exact commit `23ee661548f0f31878e31de20add0ede2bc0e076`
> at protocol step 10; see `meta/migration_reviews/matching.md`.

The compact generated report `meta/migration_reports/matching.md` (from
`meta/migration_reports/matching.spec.json`, via `meta/migration_report.py`)
records the scope and check result. The spec records the per-definition
declaration and inventory body hashes, per-row theorem names and repository-wide
consumers; `--details` emits the full evidence outside the compact report.
This record explains the decisions.

## Scope

| Group | Definitions | Treatment |
|---|---|---|
| simple-graph edge family, compiled | `Packing.conjectures.X15.x15_matching` (at most one member through each vertex), `GTMisc.conjectures.X14.x14_matching` (pairwise-disjoint distinct members), `Extremal.conjectures.X180.x180_matching` (empty pairwise intersections, over `fg_edges G`) | migrated: each now unfolds to upstream `GraphTheory.connectivity.matching M` |
| simple-graph edge family, excluded from the build | `Packing.conjectures.X15alone.x15_matching` | deferred: the X15 body declaration for declaration in a self-contained file absent from `_CoqProject`; not built, not retargeted, not repaired; its documented stronger statement constant (c <= 32 (m+1)^3 under the corpus name) is preserved |
| hypergraph edge family | `Hypergraph.conjectures.X6.x6_matching` | deferred to the hypergraph foundation (batch D) together with `U12.hg_matching`, whose body it repeats |
| whole-graph predicate | `Digraph.conjectures.path_fas.matching` | deferred, distinct representation: a forest with every degree at most one; the bridge to `connectivity.matching E(G)` needs its own comparison and a digraph build |

Perfect matchings (`x18_perfect_matching`, X24, X25), edge partitions and edge
families are separate families; X15's and X18's are frozen here only as chain
dependencies of the affected rows.

## Protocol (section 9)

1. **Discover.** Six exact inventory definitions, classified above. Nine affected
   statements: five in X15 (rows #02, #03 and the three LLM-proof variants, which
   have no manifest row), two in X18 (through `x18_perfect_matching`, a cross-file
   chain helper), one in X14, one in X180 (through `x180_induced_matching`,
   `x180_multitasker_capacity_at_least`, `x180_multitasker_capacity_positive`).
   Cross-module consumers: X18.v, `vocabulary_packing.v`, `vocabulary_misc.v` and
   `foundations/fair_matching.v` (which proves row #03 and the three variants).
2. **Compare.** All three migrated bodies are "a set of edges whose members are
   pairwise vertex-disjoint", spelled differently. The canonical body is
   `{subset M <= E(G)} /\ {in M &, forall e1 e2 x, x \in e1 -> x \in e2 -> e1 = e2}`.
   The three spellings are logically equivalent to it, not convertible
   (`matching_at_most_oneP`, `matching_pairwise_disjointP`, `matching_setI_eq0P`);
   X180's `fg_edges G` equals `E(G)` (`Extremal.migration.matching.fg_edgesE`,
   the explicit `x != y` guard being implied by irreflexivity). No body is defective.
3. **Specify.** The contract is the doc comment of
   `packing-theory/theories/foundations/matching.v`: members are edges of `G`
   (2-sets of adjacent vertices), two members sharing a vertex are equal; the empty
   family is a matching of every graph, the empty graph included; a loop `[set x]` or
   `set0` is never a member; closed under subfamilies.
4. **Audit upstream.** coq-graph-theory 0.9.7 defines `connectivity.matching` with
   exactly this meaning. `GTBase.common` re-exports it, defines
   `perfect_matching_K2`, and bridges `E(G)` (`sg_edge_setE`, `in_sg_edge_set`).
   The upstream definition is the canonical; no adapter is introduced.
5. **Implement.** `Packing.foundations.matching` holds the API: `matching_subset`,
   `matching_card_edge`, `matching_sub`, and the three presentation lemmas
   `matching_at_most_oneP`, `matching_pairwise_disjointP`, `matching_setI_eq0P`.
6. **Ground.** Same module: `matching0`, `matching_edge1`, `matching_K2`,
   `matching_K3_edge` (positive), `not_matching_loop`,
   `not_matching_set0_member`, `not_matching_K3_adjacent` (negative); all
   `Print Assumptions` clean. The public client
   `packing-theory/theories/examples/matching.v` (plan section 11) imports only
   `GTBase` and this module and exercises the positive and negative API, including
   two disjoint edges of `K_4`; the package build compiles it.
7. **Freeze.** Each area's `theories/migration/matching.v` holds a `Legacy` module
   with the migrated helper verbatim under its original name (X15 and X14 together
   with the pre-M1 comprehension body of their edge set, checked against 061154c),
   and one `XnnLegacy` module per phase that freezes the whole affected chain with
   `Legacy.`-qualified references and prefix-stripped chain names, so that no
   frozen text contains a live name of the family. The report checks every frozen
   copy against the source text at its commit modulo the listed substitutions and
   records the baseline declaration hash (equal to the inventory's) and git blob.
8. **Bridge.** `x15_matching_compat`, `x14_matching_compat`, `x180_matching_compat`
   prove each frozen helper equivalent to its alias; the chain lemmas are
   `x15_edge_set_compat`, `x15_edge_partition_compat`, `x15_edge_family_compat`,
   `x18_perfect_matching_compat`, `x14_edge_set_compat`,
   `x180_induced_matching_compat`, `x180_multitasker_capacity_at_least_compat`,
   `x180_multitasker_capacity_positive_compat`.
9. **Re-encode.** The three alias bodies now read `matching M`. Statement texts, doc
   blocks, manifest rows and leg states are unchanged; the report checks this. Each
   of the nine statements has `<formal_name>_compat : XnnLegacy.<formal_name> <->
   <formal_name>`. Proof-only knock-on edits: `fair_matching.v` (`matching_x15` by
   reflexivity), `vocabulary_packing.v` (`x15_matching_equiv_matching` by
   reflexivity, `x18_perfect_matching_equiv_x25_perfect_matching` through the API),
   `vocabulary_misc.v` (`x14_matching_equiv_matching` by reflexivity).
10. **Independently review.** Arthur approved exact commit `23ee661` on
    2026-10-02; the coordinator approved the final statement-level theorem check.
    The record is `meta/migration_reviews/matching.md`. Integration gates remain
    a separate obligation.
11. **Gate.** See the board announcements for the gate results of each commit.
12. **Deprecate.** The aliases stay. `consumers_remaining` counts their 13 same-file
    direct consumers; the cross-module consumers are listed in the report.

## Preserved statuses and discrepancies

- X15 row #02 is REFUTED and row #03 PROVED (`foundations/fair_matching.v`,
  formal resolution); the three LLM-proof variants are proved there too and are
  marked `non_corpus` in the spec (no manifest row).
- X18 row #01 is partial (m = 2, 3 in the source); the Brualdi-Stein row is open.
- X180's row is BLOCKED (per-graph quantification of the capacity ratio and the
  degree constants, 2026-07-17 audit). `log_degree_multitasker_exists_statement_compat`
  proves the frozen and the live statement equivalent, so the defect is neither
  repaired nor worsened; it is a quantifier issue of the statement, not of the
  matching helper.
- `X15alone.v` keeps its stronger constant and stays outside the build.

## Interaction with M1

The X15 and X14 chains reach the M1 aliases `x15_edge_set` and `x14_edge_set`.
Their pre-M1 comprehension bodies are re-frozen as `Legacy.x15_edge_set` and
`Legacy.x14_edge_set` (the same text M1 froze as `simple_edges.Legacy.edge_set`
and `simple_edges.Legacy.exists_edge_set`; the report checks them against
061154c), so every per-row certificate of X15, X18 and X14 is end-to-end over both
migrations, and no C1 snapshot resolves through a live helper of either family.
M1's frozen X25 statement in `Packing.migration.simple_edges` does not reach this
family.

## Fidelity of the upstream-owned canonical

`meta/foundation_fidelity.json` enrols repository-declared primitives only (its
checker requires an in-repository `path` and names declared in that file), so
`GraphTheory.connectivity.matching` is not enrolled there and no `GTBase.common`
or `Packing.foundations.matching` entry is added, which would enrol nothing or
unrelated names. As for M1's `sg_edge_set`, the verdict is the registry entry:
`fidelity = FAITHFUL` with the contract in `upstream_audit.note`, and the thirteen
API and grounding theorems above as machine evidence (compiled and
`Print Assumptions`-checked by `meta/check_library_migration.py`).

## Evidence kept outside the report

`Print All Dependencies` of every frozen and live statement and `Print Assumptions`
of every certificate, run through the pinned image after the re-layout, are kept
under `/srv/graph-theory-rocq/coordination/evidence/C1-matching/` (outside the
repository): no frozen statement reaches a live migrated helper, and every live
statement reaches `connectivity.matching`.

## Tooling

C1 uses the generic `meta/migration_report.py`. The spec records the inventory
body hash of every frozen declaration, the hashes of the three unchanged live
helpers and `corpus`/`non_corpus` marks on the statement objects. The three
explicit `non_corpus` variants retain all source, documentation, closure and
certificate checks; only the inapplicable manifest-row and leg-state checks are
skipped. The matching registry is `meta/library_primitives/matching.json`.
