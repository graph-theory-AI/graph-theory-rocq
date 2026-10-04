# Library Migration A25: Simple Line Graphs

Batch A family A25, on the private prerequisite `2bec753` (A24 pin `897a7d3` plus four reviewed tool files, unchanged
here). Registry `meta/library_primitives/simple-line-graph.json`; spec, hashes and per-row certificates
`meta/migration_reports/simple_line_graphs.{spec.json,md}`; fidelity `meta/foundation_fidelity/simple-line-graph.json`;
full evidence `coordination/evidence/A25-line-graphs/`.

- **Contract.** `GTBase.simple_line_graphs.simple_line_graph : sgraph -> sgraph`, on `{e : {set G} | e \in E(G)}`
  with `(val e != val f) && (val e :&: val f != set0)`. API: the adjacency view and edge count, functoriality on
  isomorphisms (promoted from Kelly), complete line graphs when any two edges meet, and graph-power and chromatic
  transport. X43's `x43_line_vertex`/`x43_line_rel`/`x43_line_graph` and the Section `SLine` of U11 and Minor
  containment (`sline_rel`/`sline_graph`; the containment pair as public repository sources) are aliases. Their six
  constructor proofs are one-line uses of the public ones, related by `eq_diso`, never by proof-field equality.
- **Rows.** Frozen verbatim at `897a7d3`: the seven sources, the six proofs with their scripts, X43's strong edge
  colouring and six complete Props. These are X43, X220's two rows, U11's Graham row (every iterate, zero included),
  Kelly's Whitney premise (`additional_statements`) and implications_U11's external statement. The last two are
  non-corpus and stay conditional.
- **Originals.** X43 at `061154c`, over M1's raw edge comprehension and A1's raw induced-free; both Whitney Props at
  A4's `9e03072`, over A4's raw edge deck. Nine whole iffs, 36 mappings (20 current, 16 historical). The combined C19
  X220 Original remains coordinator-owned.
- **Consumers.** Kelly's `LineDiso` block becomes wrappers with unchanged headers. The 37-file closure (774
  declarations, including Atlas implications_A1's 15 headers) is type-identical; the sources keep their `Arguments`.
  M1's `consumers_remaining` drops from 40 to 39: X43's vertex alias no longer names `x43_edge_set`.
- **Kept distinct.** Hamilton U2's four enum-ranked helpers form a deferred class of this family; GTBase.base's
  multigraph `line_graph`, X102's defective `x102_line_graph_of` and Infinite D4legacy's ordered-edge line graph are
  unchanged distinct variants.
- **History.** A1's X43 row and A4's two Whitney snapshots keep the live line construction; A25's copies keep the live
  `x43_induced_free` and `same_edge_deck`. All carry reciprocal notes.
- **Reproduction.** Build the packages, then run `python3 meta/migration_report.py simple_line_graphs --check --kernel`,
  the milestones (Chromatic X43; Reconstruction U11; Minor X214, X220, X228, X27, X42) and the kernel probes.
