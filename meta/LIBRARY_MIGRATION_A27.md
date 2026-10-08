# Library Migration A27: Complete Multipartite Graphs

Batch A family A27, on Arthur's A26 pin `9e3f1ef`. Registry `meta/library_primitives/complete-multipartite.json`; spec,
hashes and per-row certificates `meta/migration_reports/complete_multipartite_graphs.{spec.json,md}`; fidelity
`meta/foundation_fidelity/complete-multipartite.json`; full evidence `coordination/evidence/A27-complete-multipartite/`
(discovery and approved scope: `coordination/evidence/A27-multipartite-discovery/`).

- **Contract.** `GTBase.complete_multipartite_graphs.complete_multipartite_graph k m : sgraph` on `'I_k * 'I_m`, with
  parts first, part size second, and adjacency `x.1 != y.1`. The argument status matches the sources and there is no
  positivity premise. API:
  - the adjacency view and `k * m` vertices;
  - same part non-adjacent, different parts adjacent;
  - `k = 0` or `m = 0` empty, `k = 1` edgeless;
  - `m = 1` complete, and isomorphic (not convertible) to `'K_k`.
- **Sources.** U4's `cmp_rel`/`complete_multipartite` and X218's `x218_multipartite_rel`/`x218_complete_multipartite`
  are aliases. Their four constructor proofs are one-line uses of the public ones, related by `eq_diso`, never by
  proof-field equality.
- **Rows.** Frozen verbatim at `9e3f1ef`: the four sources, the four proofs with their scripts, X218's
  `x218_multibounding` and two complete rows:
  - U4 choice number: `chi(G) = k`, at most `m * k` vertices, both relational choice-number assumptions,
    `chG <= chK`; zero `k`/`m` allowed;
  - X218 forest row: whole functions `c, e` chosen before `d >= 1`, `t >= 1` and `G`, induced-`H` and
    ordinary-subgraph `K_d(t)` exclusions, `chi <= c d * t ^ e d`.

  Eleven mappings and two whole iffs; no Original exists on this parent.
- **Consumers.** grounding_U4's `cmp_same_part` and grounding_X218's `x218_multipartite_1_edgeless` add one unfold of
  the public relation; headers unchanged. implications_X218 (whose unfolding proofs compile unchanged), the grounding
  `x218_multibounding_pointwise` and the rest of the closure recompile unchanged.
- **Kept distinct.** Extremal XE1's arbitrary-size partition predicate and Digraph X221's oriented predicate.
- **Reproduction.** Build the packages, then run
  `python3 meta/migration_report.py complete_multipartite_graphs --check --kernel`, the milestones U4 and X218
  (chromatic-theory), and the kernel probes.
