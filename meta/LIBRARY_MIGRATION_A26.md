# Library Migration A26: Undirected Cayley Graphs

Batch A family A26, on Arthur's A25 pin `5832ba9`. Registry `meta/library_primitives/cayley-graph.json`; spec,
hashes and per-row certificates `meta/migration_reports/cayley_graphs.{spec.json,md}`; fidelity
`meta/foundation_fidelity/cayley-graph.json`; full evidence `coordination/evidence/A26-cayley-graphs/`.

- **Contract.** `GTBase.cayley_graphs.undirected_cayley_graph S : sgraph` for any finite group `gT` and any
  `S : {set gT}`, on the carrier `gT` with `(x != y) && ((x^-1 * y \in S) || (y^-1 * x \in S))`. It is loopless also
  when `1 \in S` and symmetric for every `S`; no inverse closure, generation, abelianity or order condition, and
  nonabelian groups are allowed. API: the adjacency view, `#|gT|` vertices, edges along right multiplication by `S`
  and by its inverses, the inverse-closed specialisation, and the empty, identity and full sets.
- **Sources.** D2ram's `cayley_adj`/`cayley_graph` and U2's `cayley_rel`/`cayley_graph` are aliases with their Section
  arguments. U2's `group_scope` and D2ram's explicit `%g` elaborate to the same relation. The four constructor proofs
  are one-line uses of the public ones, related by `eq_diso`, never by proof-field equality.
- **Rows.** Frozen verbatim at `5832ba9`: the four sources, the four proofs with their scripts and Section scaffolding,
  U2's `hamiltonian_cycle` (with its `Arguments`), `is_hamiltonian` and `symmetric_set`, and two complete rows:
  - D2ram Ramsey: one positive `c` before every finite abelian group of order > 1, one inverse-closed `S`, both
    `2^omega` and `2^alpha` bounds;
  - U2 Hamiltonicity: order > 2, `S` inverse-closed and generating, then a Hamiltonian cycle.

  Thirteen mappings and two whole iffs; no Original exists on this parent.
- **Consumers.** grounding_D2ram's `cayley_adj_set0`/`cayley_adj_setT` and grounding_U2's `cayley_full` add one unfold of
  the public relation; headers unchanged. `D2ram_nodes_in_scope` and the rest of the closure recompile unchanged.
  Five files that use `GTBase.common.hamiltonian_cycle` match only lexically and are declared as such.
- **Kept distinct.** The directed `Digraph.constructions.cayley.cayley` (loops kept, no symmetrisation).
- **Reproduction.** Build the packages, then run `python3 meta/migration_report.py cayley_graphs --check --kernel`,
  the milestones D2ram (extremal-graph-theory) and U2 (hamiltonicity-theory), and the kernel probes.
