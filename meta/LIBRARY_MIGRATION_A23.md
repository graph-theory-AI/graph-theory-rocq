# Library Migration A23: Hypercubes

Batch A family A23, on the fixed A22 pin `f5d2d3a` (no private union). Registry
`meta/library_primitives/hypercube.json`; spec, hashes and per-row certificates
`meta/migration_reports/hypercubes.{spec.json,md}`; fidelity `meta/foundation_fidelity/hypercube.json`; full evidence
`coordination/evidence/A23-hypercubes/`.

- **Contract.** `GTBase.hypercubes` names two views of Q_d:
  - `product_hypercube` is the iterated `'K_2 □` product with `Q_0 = 'K_1`: one vertex and no edge, not K_0.
  - `tuple_hypercube` uses the `d.-tuple bool` vertices, adjacent iff exactly one coordinate differs.

  `product_tuple_hypercube_diso` relates them for every d, through the inverse maps `product_to_tuple` and
  `tuple_to_product`; there is no positive-dimension guard. XE1's and D3cr's Fixpoints now unfold to the product view
  (the same graph record). U9's hypercube unfolds to the tuple view: same carrier and adjacency, identity isomorphism,
  with `hc_rel`/`hc_sym`/`hc_irrefl` unchanged. Isomorphism is not equality: #567's literal `G = Q_3` and X226's
  `tnth` coordinates keep their carriers.
- **Rows.** Frozen verbatim at `f5d2d3a`: the three sources (U9 with its complete Section and proofs), ten chains and
  six rows (Erdős #1035/#567, U9 matching and weak-saturation proxy, X226, D3cr). Quantifier orders, guards,
  proxies and the partial D3cr status are unchanged.
- **Complete rows.** Three more at `9e03072`, for nine whole iffs: #1035 over A5's subgraph, #567 extending A11's
  complete row, and U9 over the actual C25 raw matching/B11 cycle edges plus A23 frozen cube. The latter reuses
  C25's proved whole iff by carrier/adjacency conversion, never equality of opaque graph records.
- **History.** The ten older A5/A6/A7/B4/A11 #567/#1035 snapshots keep the live cube and are documented in the spec.
  A23's per-row copies keep their names, with reciprocal notes. Three older U9 snapshots also remain exact;
  the complete U9Original is their combined replacement. The spec has 29 bindings, preserving all 26 worker objects.
- **Consumers.** grounding_U9/X226/D3cr and implications_U9/X226/D3cr compile unchanged, with no proof adaptation.
  The 32-file reverse closure (972 declarations) is type-identical to the baseline.
- **Distinct.** These stay separate: `base.graph_power` (the distance power), `xe2_cube_square_floor` and X226's
  `x226_subcube_dim`.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py hypercubes --check --kernel` and the
  milestones Extremal XE1, Packing U9/X226 and Topological D3cr.
