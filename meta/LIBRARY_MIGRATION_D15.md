# Library Migration D15 (directed-neighbourhood, first stage): Directed Neighbourhoods and In-Degrees

Family `directed-neighbourhood` (option C), first stage, on the A28 main `761e776c`. Contract
`master-directed-neighbourhood-contract.md` (86b00148) with addendum 1 (ed04e65a); scope decision
`master-directed-neighbourhood-scope-decision.md` (6d6d2b8d). Registry `meta/library_primitives/directed-neighbourhood.json`;
spec, hashes and per-row certificates `meta/migration_reports/directed_neighbourhood.{spec.json,md}`; fidelity
`meta/foundation_fidelity/directed-neighbourhood.json`; certificates `digraph-theory/theories/migration/directed_neighbourhood.v`.

- **Contract.** No new degree: B16's `Digraph.foundations.degree_balance.indeg` and core `oriented.outdeg` stay canonical.
  - New focused public module `Digraph.foundations.neighbourhoods` (imports `prelude` and `core/digraph` only):
    `Nout v := [set w | v --> w]`, `Nin v := [set u | u --> v]` and `Nout2 v` (directed distance exactly two: `w != v`,
    `w \notin Nout v`, a common out-neighbour), verbatim, with membership views, the distance-two exclusion, the loop, digon
    and arcless corners and the converse swaps; public client `digraph-theory/theories/examples/neighbourhoods.v`.
  - `degree_balance` gains the Boolean `diregular d := [forall v : D, (outdeg v == d) && (indeg v == d)]` (out-degree
    conjunct first; vacuous on the empty carrier), the bridges `indeg v = #|Nin v|`, `outdeg v = #|Nout v|` (conversion) and
    the tournament equalities.
- **Endpoints of this stage (6).** classic_core `Nout`, `Nin`, `Nout2` alias the module; classic_core `indeg` and
  colouring_variants' file-local `indeg` alias B16's `indeg`; classic_core `diregular` aliases `degree_balance.diregular`.
  Names, declared types, implicit arguments and transparency are unchanged.
- **Rows of this stage (11).** Frozen verbatim at `761e776c` with their own chains, every guard in its order: classic_core
  Seymour, long dicycle and Jackson (non-corpus; its corpus row is P9's alias); P9's Hamilton alias, antidirected trees,
  arc-disjoint cycles and `decomposing_an_even_tournament_in_directed_paths_statement` (the 14th row of the full scope, a count
  correction); X19; X2's Mader delta-zero and semidegree rows; X17. Each certificate is `iff_refl` (conversion).
- **Lexical-only enrollment (decision X-a).** X107's `x107_total_degree_at_most` binds a local `let indeg`, which shadows
  every imported `indeg`; the migration tool's lexical discovery resolves it to classic_core's `indeg` anyway, while the
  kernel closure shows no dependency. Its chain and row are frozen verbatim with `iff_refl` certificates and explicit notes;
  nothing in X107 changes.
- **STAGED (decision T = C).** core/tournament's `N_out`/`N_in`, the three rows that reach the family only through them (X2's
  two tournament out-neighbourhood rows, X93's row) and the X93 chain `x93_t_local_tournament` are a later stage of this
  family: the migration tools admit no public source under `core/`. They are untouched here (`core/tournament.v` keeps its
  parent text). The measured finding for that stage is kept: the `N_in` alias must take no `{set T}` ascription (About and
  `Set Printing All` parity), unlike `N_out`.
- **History.** B16's per-row snapshots `Legacy.x221_eulerian`, `Legacy.cv_eulerian`, `Legacy.Eulerian` and B1/B2's
  `X2BoundsLegacy.mader_delta_zero_bound` keep this family's live in-degree (keyed, with notes, in this family's spec). Their
  complete Originals over the raw in-degrees are frozen here: B16's five rows (the X221 row also over poset-unavoidability's
  frozen `contains_subdigraph`; the whole Props `conj_9_2_glued`/`_e` as non-corpus Originals) and X2's Mader delta-zero row
  over B1's raw subdivision chain.
- **Proof-only adaptations** (theorem types unchanged): `grounding_classic_core.v`, `grounding_X2.v`, `glue_eul_subtype.v`.
- **Kept distinct / deferred.** `reals_growth.indeg` (B16's legacy-axiom class, deferred); D11's `rel_indegree` (reciprocal
  listing), Alon–Tarsi `at_indegree`, P9 `arcset_indeg`/`arcset_outdeg`, packing `selindeg`, X86 `x86_sel_indeg`,
  path_fas `sdeg`, twinwidth `red_deg`, Infinite D4 `i_neighbourhood`; upstream `open_neigh` is a bridge only.
- **Reproduction.** Build `digraph-theory` (the reverse closure of the changed files) and Atlas `implications_A2`, then run
  `python3 meta/migration_report.py directed_neighbourhood --check --kernel`, `--all --check`, `library_inventory.py --check`
  (after `--write`) and `foundation_fidelity.py --check`.
