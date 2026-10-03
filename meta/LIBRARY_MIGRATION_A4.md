# Library Migration A4: U11 Single-Edge Deletion

> Batch A, family A4: U11's cross-name single-edge deletion `sde_rel`/`sdel_edge`, the
> companion deferred by A3, stacked on the A3 series (`892bc96` + `dde0199`) on
> 2026-10-02. Registry document `meta/library_primitives/single-edge-deletion-u11.json`,
> status `deprecated` (both names stay as transparent aliases for one cycle). Fidelity
> reuses A2's enrollment of `del_edge_set` and `del_es_rel`
> (`meta/foundation_fidelity/edge-set-deletion.json`); A4 owns no fragment and adds no
> API. `reviewed_by` stays unset until marcol's step-10 cross-review and the
> coordinator's statement-theorem check are recorded.
>
> Compact report `meta/migration_reports/sdel_edge.md`, regenerated from
> `meta/migration_reports/sdel_edge.spec.json`.

## Sources

| Definition | Now unfolds to | Helper certificates |
|---|---|---|
| `Reconstruction.conjectures.U11.sde_rel` | `@del_es_rel G [set e]` | `sde_rel_compat` |
| `Reconstruction.conjectures.U11.sdel_edge` | `del_edge_set G [set e]` | `sdel_edge_compat`, `sdel_edge_diso`, `sdel_edge_proofs_compat` |

Both live in U11's `Section DelEdge` (`Variables (G : sgraph) (e : {set G})`). The
re-encoded Section keeps its Variables, so the discharged arguments and implicit
status are unchanged (`Arguments sde_rel [G] e`, `sdel_edge [G] e`, `sde_sym [G] e x y`,
`sde_irrefl [G] e x`, checked with `About`). `sde_sym`/`sde_irrefl` keep their statements
and are re-proved from `del_es_sym`/`del_es_irrefl`.

The old relation `(x -- y) && ([set x; y] != e)` equals `del_es_rel G [set e]` pointwise
for every vertex set `e` (`GTBase.common.del_edge_set1`), including invalid `e`. Upstream
`del_edges e` agrees only on genuine edges; `grounding_U11.sde_del_edges_rel` keeps that
hypothesis. Upstream `digraph.del_edge` deletes one directed arc and is unrelated.

## Frozen Section and chain

The Section is frozen as it stood at 9e03072; reconstruction-theory is unchanged through
`dde0199`. It sits in dependency-ordered modules, B1's convention for Section copies:
- `Legacy.sde_rel`;
- `ProofsLegacy.sde_sym`/`sde_irrefl` with their full proofs;
- `GraphLegacy.sdel_edge`, the `SGraph` built from them.

Each declaration sits in a verbatim copy of the Section scaffolding, so its discharged
arguments are the original's. References to earlier frozen names are module-qualified:
`sde_rel` becomes `(Legacy.sde_rel e)`, the same term once the Section closes. The spec
lists these exact substitutions.

| Frozen | Original | Certificate |
|---|---|---|
| `U11Legacy.same_edge_deck` | `U11.same_edge_deck` | `same_edge_deck_compat` |
| `U11Legacy.edge_reconstructible` | `U11.edge_reconstructible` | `edge_reconstructible_compat` |
| `U11Legacy.edge_reconstruction_statement` | opg:edge_reconstruction_conjecture | `edge_reconstruction_statement_compat` |
| `KellyLegacy.whitney_line_inversion_premise` | `kelly.whitney_line_inversion_premise` | `whitney_line_inversion_premise_compat` |
| `ImplicationsU11Legacy.external_whitney_line_inversion_statement` | non-corpus external theorem | `external_whitney_line_inversion_statement_compat` |

`same_edge_deck_compat` keeps the SAME bijection `f` of edge indices. Each card
isomorphism is composed with the identity isomorphisms of its two cards
(`sdel_edge_diso`), so every card keeps its multiplicity; no card is replaced by a set
equality. The Kelly premise and the external statement keep the four-edge guard on `G`
and the same-edge-deck hypothesis; the premise is not weakened to order equality plus
line-graph isomorphism (the sources record the `K_3 + K_1 + K_2` / `K_{1,3} + K_2`
counterexample). The external theorem stays registered in `meta/external_theorems.json`,
and Greenwell's implication stays conditional.
`legacy_reconstruction_implies_edge_reconstruction` only transports that conditional
implication to the frozen encodings, with no new hypothesis.

## Consumers rebuilt

Statements unchanged, proofs adapted where they unfolded the old relation:
- the eight U11 grounding lemmas: `sdel_edge_sub` (view up to conversion),
  `sdel_edge_set0` and `sdel_edge_removes` (`change` to the unfolded test),
  `sde_del_edges_rel` (unfolds `del_es_rel`), `sde_del_edges_adj` (`change`, then the
  relation lemma), plus `sdel_edge_diso_del_edges`, `same_edge_deck_refl` and
  `same_edge_deck_card`, which are unchanged;
- Kelly: `sdel_adjE` now follows from `del_edge_set1`; `in_edge_set_sdel`,
  `edge_set_sdel`, the `LineCard` section, `vdel_card_sline`, `same_edge_deck_line`,
  `same_edge_deck_card_edge`, `same_edge_deck_card_vertex`, `reconstruction_line_diso`
  and `whitney_reconstruction_edge_reconstruction` are unchanged;
- implications_U11: `external_whitney_line_inversion_statement` and
  `reconstruction_implies_edge_reconstruction` are unchanged.

No migration snapshot at the base references this chain; the report's stale-snapshot
scan confirms it.

## Kernel dependency evidence

`Print All Dependencies` on the compiled certificate, with probe and outputs in
`/srv/graph-theory-rocq/coordination/evidence/A4-sdel_edge/print_all_dependencies_{probe.sh,summary.txt,full.txt.gz}`:
- The frozen statement, premise, external statement and deck closures contain no live
  U11 helper or chain name and no `del_edge_set`/`del_es_*`. They reach only the
  `Legacy`/`ProofsLegacy`/`GraphLegacy`/`U11Legacy` copies and the unmigrated
  `sline_graph`.
- The live ones reach `del_edge_set` and `del_es_{rel,sym,irrefl}`.

All ten certificates and the ten rebuilt Kelly/implication theorems print "Closed under
the global context".

## Effects on the A2 and A3 reports

A2's spec listed U11's `sdel_edge`, and A3's spec listed `sde_rel`/`sdel_edge`, as untouched
distinct variants. A4 migrates them, so they leave both lists, and both summaries record the
hand-over. The deferred-variant notes in the A2 and A3 registry documents now point to
the migrating family. Compact reports regenerated: A2 216/216, A3 145/145.
