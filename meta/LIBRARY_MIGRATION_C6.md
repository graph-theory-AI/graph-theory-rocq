# Library Migration C6: Supplied Proper Edge Colourings

> Batch C, sixth family (meta/LIBRARY_MIGRATION_PLAN.md section 15), implemented
> 2026-10-03 on the C5 pin `3011c28` (coordinator `work/c5-colourings`), in a
> private worktree; one family commit on `work/lancelot-c6`.
>
> Registry status: `deprecated`, because all five historical names remain as
> transparent compatibility aliases for one migration cycle (the public foundation
> name `proper_ecolouring` stays public as an adapter). `reviewed_by` stays unset
> until the step-10 review is recorded.

The compact report `meta/migration_reports/proper_edge_colouring.md` (from
`meta/migration_reports/proper_edge_colouring.spec.json`, via
`meta/migration_report.py`) holds the per-definition hashes and git blobs, the
per-row theorem names, the repository-wide consumer list and the machine checks;
the spec also records the inventory body hash of every frozen declaration. This
record explains the decisions.

## Scope

| Group | Definitions | Treatment |
|---|---|---|
| set maps `{set G} -> C`, endpoint form | `Extremal.foundations.edge_colourings.proper_ecolouring` (`C : eqType`, public) | adapter: unfolds to `GTBase.edge_colourings.proper_edge_colouring`, same type, name kept public |
| set maps, edge-pair forms | `Chromatic.conjectures.X142.x142_proper_edge_colouring` (`'I_k`; distinct intersecting edges), `GTMisc.conjectures.X14.x14_proper_edge_colouring` (`finType`; distinct non-disjoint edges) | migrated: unfold to `proper_edge_colouring`, certified by `proper_edge_colouring_edgesP` / `proper_edge_colouring_meetP` |
| pair maps `G -> G -> C`, symmetric on all pairs | `Chromatic.conjectures.X213.x213_proper_edge_colouring` (`'I_k`), `Extremal.conjectures.D2chr.proper_ec` (`finType`) | migrated: unfold to `proper_pair_edge_colouring` (conversions) |
| distinct, not claimed | U5 `acyclic_edge_colouring` / `star_edge_colouring`, the strong (distance-two) colourings of U5/X43/XE1, X219 list choosability, X9 sequence-incident colouring, X100 modular colouring | untouched; listed as `distinct_variants` |

Seven rows: X142 Flandrin, X213 one-factorization (partial) and Vizing interchange
(solved), X14 Andersen, X62 rainbow-path cover, D2chr star chromatic index (OPG),
X229 expander palettes. All statement texts, doc blocks, manifest rows, leg states,
guards and documented discrepancies are unchanged.

## Protocol (section 9)

1. **Discover.** The matching_scope discovery (coordination evidence
   `C6-discovery-by-matching-scope`) lists the five sources, their hashes, five
   intermediate chains and ten proof consumers; the conjecture-only inventory
   carries three of the sources, `proper_ec` is a cross-name match and the public
   foundation source is registered through the `repository_sources` descriptor.
2. **Compare.** Set-map sources read only the doubletons of actual edges: the
   endpoint form and the two edge-pair forms are logically equivalent for the same
   supplied map (two distinct meeting edges are two edges at a common endpoint,
   `edges_meet_endpoint`). Pair-map sources are the same contract modulo names and
   palette specialisation: symmetry on ALL ordered pairs, adjacent or not, and
   different colours on two distinct neighbours of a vertex. The two interfaces are
   not unified: their domains differ (`{set G}` is inhabited for every graph, `G * G`
   is empty exactly for the empty graph), so empty-palette behaviour differs and no
   map on the subtype of actual edges may replace either domain. No body is defective.
3. **Specify.** The contract is the doc comment of `GTBase.edge_colourings`: both
   interfaces, their degenerate cases, the explicit bridge `fun x y => col [set x; y]`,
   relabelling and off-edge extensionality. Palettes stay `eqType`; the supplied map
   and its labels are kept (X142 sums `val (col e) + 1`, X213 compares whole
   functions in Kempe states, D2chr takes a least index).
4. **Audit upstream.** coq-graph-theory 0.9.7 has no supplied proper-edge-colouring
   predicate; `mgraph.line_graph` is directed and `GTBase.base.line_graph` lives on
   multigraph edge identities with a count-only `edge_colourable`. Neither is used; a
   line-graph correspondence would need an explicit incidence bridge and is left out.
   C5's `GTBase.colourings.proper_colouring` takes `finType` palettes and is not used
   so as not to narrow the foundation's `eqType` generality.
5. **Implement.** New focused module `base/theories/edge_colourings.v`
   (`GTBase.edge_colourings`, no conjecture import, no base re-export): the two
   definitions, `proper_edge_colouring_edgesP`, `proper_edge_colouring_meetP`,
   `eq_proper_edge_colouring`, `proper_edge_colouring_comp` / `_relabel`,
   `proper_pair_edge_colouring_sym` / `_neighbours` / `_comp` / `_relabel`,
   `proper_edge_colouring_pairP`.
6. **Ground.** `proper_edge_colouring_K2`, `proper_pair_edge_colouring_K2` (one
   edge), `not_proper_edge_colouring_K3`, `not_proper_pair_edge_colouring_K3` (two
   edges at a vertex), `no_set_map_into_empty_palette`, `proper_pair_edge_colouring_K0`
   (empty graph, empty palette), `no_pair_map_into_empty_palette` and
   `proper_pair_edge_colouring_K1` (the `K_1 = 1` convention of D2chr). The fidelity
   fragment `meta/foundation_fidelity/proper-edge-colouring.json` enrols both
   canonical predicates and the public adapter. The public client
   `base/theories/examples/edge_colourings.v` imports `GTBase` only.
7. **Freeze.** X142: M1's complete frozen chain `Chromatic.migration.simple_edges.X142Legacy`
   over the pre-M1 edge comprehension is reused verbatim (bodies and theorem types
   byte-identical; only M1's helper certificate proof now goes through
   `proper_edge_colouring_edgesP`). X213: `Legacy.x213_proper_edge_colouring` and the
   chain/rows in `X213Legacy` (A1 convention). X14/X62: `Legacy.x14_edge_set` (pre-M1,
   checked against 061154c), `Legacy.x14_proper_edge_colouring`, `X14Legacy`, `X62Legacy`.
   D2chr: `Legacy.proper_ec`, the chain copied as `D2chrLegacy.d2chr_*` and the row.
   Foundation: `Legacy.proper_ecolouring` and `X229Legacy`. The report checks every
   copy against the source text at its commit modulo the listed substitutions.
8. **Bridge.** Helper certificates: `x142_proper_edge_colouring_compat` (M1's,
   re-proved; restated by the chromatic entry point), `x213_proper_edge_colouring_compat`,
   `x14_proper_edge_colouring_compat`, `proper_ec_compat`, `proper_ecolouring_compat`.
   Chain certificates: X142's (M1) and `x142_neighbour_sum_edge_colourable_compat`
   (restated), `x213_edge_colourable_compat`, `x14_edge_set_compat`,
   `star_edge_colouring_compat`, `star_edge_k_colourable_compat`,
   `is_star_chromatic_index_compat`.
9. **Re-encode.** The five alias bodies now read `proper_edge_colouring col` or
   `proper_pair_edge_colouring col`. Per-row theorems: `flandrin_..._statement_compat`
   (over M1's frozen row), `one_factorization_conjecture_statement_compat`,
   `vizing_kempe_interchange_statement_compat`, `andersen_rainbow_path_statement_compat`,
   `rainbow_paths_linear_edge_cover_statement_compat`,
   `star_chromatic_index_of_complete_graphs_statement_compat`,
   `expander_proper_colouring_two_connected_palettes_statement_compat`. The ten proof
   consumers (grounding_X213, grounding_D2chr, grounding_X229 and M1's three X142
   theorems) keep their statements; their scripts compile over the converted aliases.
10. **Independently review.** Pending: the coordinator-assigned reviewer; coordinator
    final seven-statement check.
11. **Gate.** See the board announcement for the gate results of the commit.
12. **Deprecate.** The aliases stay; `consumers_remaining` counts their 6 same-file
    direct consumers (X142: 1, X213: 2, X14: 1, D2chr: 1, foundation: 1,
    including the public adapter's `proper_ecolouringE` theorem).

## Preserved discrepancies and statuses

- X213.v's introductory prose says only the values on adjacent pairs are
  constrained, while the body (and hence the canonical pair-map predicate) requires
  symmetry on every ordered pair. Recorded here as a prose/body discrepancy; neither
  the prose, the body nor the two rows (bm-057 partial, bm-060 solved) is changed.
- D2chr's `is_star_chromatic_index (complete 1) 1` (a total pair map colours the pair
  `(ord0, ord0)`) is a property of the pair-map domain and is grounded in the API.
- X142 keeps its shifted numeric labels and incident sums, Andersen its `n.-1`
  vertices, X62 its uniform constant, X229 its robust-expander hypotheses.

## Interaction with earlier families

M1 froze the whole X142 chain and row; those bodies stay and are the frozen objects
of this family for X142 (no duplicate original). C1's `GTMisc.migration.matching`
freezes the X14 matching chain, which does not reach the colouring helper; the X14
pre-M1 edge set is re-frozen here (the same text C1 froze). The raw-path vocabulary
of Andersen/X62 (`x14_rainbow_path`, `x14_genuine_path`, `x14_path_edges`) is family
B6's and is used live here; if B6 precedes integration, its history refresh composes
with these frozen rows.

## Tooling dependency

The public foundation source is absent from the conjecture-only helper inventory.
The family document registers it through the `repository_sources` descriptor (path,
pinned commit `3011c28`, blob, declaration hash) supported by the repository-sources
tooling pin `2f15093` (matching_scope), on which this family's private baseline
`e2a49d3` (= C5 `3011c28` + `2f15093`) is built; the spec lists it as an ordinary
`kind: source` and X229 as an ordinary corpus row discovered through it.

## Evidence kept outside the report

`Print All Dependencies` of the seven frozen and seven live statements and `Print
Assumptions` of every certificate, run through the pinned image, under
`/srv/graph-theory-rocq/coordination/evidence/C6-proper_edge_colouring/`.

## Additive B6 history composition

The initial C6 pin `e7fd30a` and reviewed B6 pin `632e0b1` retain all their
previous frozen bodies and certificates. The follow-up appends `X14Original`
and `X62Original` to `GTMisc.migration.edge_colourings`: it composes C6's frozen
properness and raw pre-M1 edge set with B6's frozen genuine-path predicate, and
freezes the unchanged path-edge list, rainbow-path conjunction and edge-cover
predicate. Neither complete original reaches either family's live aliases.
Five added certificates relate the three frozen helper chains and the two whole
statements to their current forms, preserving every guard, witness and quantifier.
This proves logical equivalence of the full statements; it makes no claim that
old and new proof terms are identical.

Both family specifications record these originals and reciprocal notes for the
older partial snapshots. Existing frozen declarations, certificate types, live
statement text, doc blocks, row statuses and earlier review fields are unchanged.
Focused exact-type, assumptions and compiled dependency evidence is archived in
`coordination/evidence/C6-finalization-by-matching-scope/` outside committed meta.
