# Library Migration A6: Ordinary Graph Complement

> Batch A, family A6 (normalized `complement_rel` / `complement_graph`), implemented
> 2026-10-03 on top of the final A5 pin (`f9542f3`). Registry document
> `meta/library_primitives/complement.json`, status `deprecated` (the ten names stay as
> transparent aliases for one cycle). The canonical is upstream `GraphTheory.core.sgraph.compl` /
> `compl_rel` (owner `upstream`, no fidelity fragment, as C1's upstream `matching`); the reusable
> lemmas A6 adds live in `GTBase.common`. `reviewed_by` stays unset until the independent step-10
> review and the coordinator's sixteen-row statement check are recorded.
>
> Compact report `meta/migration_reports/complement.md`, regenerated from
> `meta/migration_reports/complement.spec.json` (baseline `49ddc033`).

## Sources

Five relation/constructor pairs, all `(x != y) && ~~ (x -- y)` on the same carrier with an
`SGraph` of their own symmetry/irreflexivity proofs: X3 (`x3_complement_rel`/`_graph`), chromatic
XE2 (`xe2_`), X56 (`x56_complement_rel`/`x56_complement`), extremal XE1 (`xe1_`) and X29
(`x29_complement_rel`/`x29_complement`). They now unfold to `@compl_rel G` and `compl G`; the ten
`*_sym`/`*_irrefl` lemmas keep their statements and are re-proved from upstream
`compl_rel_sym`/`compl_rel_irrefl`.

The relations agree by conversion. The graphs do not: upstream `compl` packages the relation with
upstream's own opaque proofs, so the frozen and live graphs are related by the identity
isomorphism (`compl_eq_diso`), never by equality of proof terms. All ten original proof scripts
are frozen verbatim (`Legacy.`-qualified; X29's symmetry proof keeps `sg_sym`, the others `sgP`),
and `*_proofs_compat` relates the `SGraph` built from them to the live one.

## Canonical API and grounding (GTBase.common)

`compl_adjE` (same vertices, distinct vertices swap adjacency, no loops), `compl_eq_diso`,
`compl_adj_offdiag`, `compl_noloop`, `compl_Kn_edgeless` (empty, one-vertex and complete graphs),
`compl_compl_diso` (upstream `diso_compl`), and `has_subgraph_host_diso` (host isomorphism carries
an ordinary subgraph, used by the Ramsey chain). Upstream `maxstabsets_compl`/`alpha_compl` are
aborted upstream and are not used. The public client `base/theories/examples/complement.v` imports
`GTBase.base` only. It covers off-diagonal negation, loop exclusion and double complement, a
hand-built complement, edgeless `K_0`/`K_1`/`K_3` complements, and the complement of two isolated
vertices, which has their edge.

## Rows and transports (sixteen statements)

| Row | Where the complement sits | Transport |
|---|---|---|
| X3 `gyarfas_complementation_chi_bounded_statement` | `x3_complement_image C G = exists H, C H /\ G ≃ compl H` | same witness `H`, composed isomorphisms; lifted through `chi_bounded` (no isomorphism-invariance of `C` assumed) |
| chromatic XE2 `erdos_753_statement` | `is_choice_number (complement G)` | conversion: choosability uses only the carrier and adjacency |
| X56 `c8_complement_c8_erdos_hajnal_statement` | forbidden PATTERN of `induced_free` | A1's `induced_free_diso` |
| X29 `no_c5_c7_complement_c7_normal_graph_statement` | HOST of an induced cycle | `induced_copy_host_diso` (cardinality kept) |
| extremal XE1 (8) and XE2 (4) Ramsey rows | HOST of the second subgraph alternative of `xe1_graph_ramsey` | `has_subgraph_host_diso`, then the Ramsey-number and diagonal wrappers |

Every guard is untouched: choice-number minimality, positivity and natural subtraction, #549 (no
added `k > 0`), #567's literal graph equalities and #812's two bounds. The frozen statements are
checked verbatim modulo the listed substitutions, and their texts, doc blocks, manifest rows and
leg states are unchanged.

## History and combined originals

- A1's `Extremal.migration.induced_free.X56Legacy.statement` still calls the live `x56_complement`.
  `X56Original` combines A1's frozen induced-free helper (pre-A1, `9e03072`) with the frozen
  complement.
- A5's `XE1Legacy.graph_ramsey` still calls the live `xe1_complement_graph`. `XE1Original` and
  `XE2Original` freeze the Ramsey chain over A5's frozen subgraph helper (module alias `A5`) and the
  frozen complement, for all twelve Ramsey rows.
- B4's `erdos_567` snapshot calls the live Ramsey-number chain. `XE1Original.erdos_567_statement`
  also uses B4's frozen `h5_graph`, so that row is frozen before A5, A6 and B4.
- A6's own per-row copies keep other families' live helpers by design (`x56_induced_free`,
  `xe1_subgraph_of`, `xe1_h5_graph`). They are documented in A1's, A5's and B4's specs.

Other live helpers in these rows (for instance `x4_edge_count`, A7's scope) are not migrated, so no
row is claimed to be a pre-M1 original.

## Distinct variants

`Chromatic.conjectures.U8.local_complement` (local complement at a vertex) and
`GTMisc.conjectures.X94.x94_bicomplement` (bipartite complement) are different operations and stay
untouched.

## Kernel evidence

`Print All Dependencies` of the frozen and live statements and `Print Assumptions` of every
certificate are kept outside the repository in
`/srv/graph-theory-rocq/coordination/evidence/A6-complement/`.
