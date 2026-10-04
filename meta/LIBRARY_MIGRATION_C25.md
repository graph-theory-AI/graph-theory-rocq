# C25: U9 supplied edge-family matching

C25 starts from the fixed C24 commit `f3d16d8b262d3a8188f76947626d06b92311bfd7` and extends the
existing C1 `matching` family. The owner stays upstream `GraphTheory.connectivity.matching`, and
the baseline stays `9e030727db115917ae077ac07a8fc6aa68661f73`.

`Packing.conjectures.U9.is_matching_edges` now unfolds to `matching M` of the supplied family.
`is_matching_edges_compat` proves it equal to the raw body (genuine edge witnesses, at most one
member through each vertex) via the public `matching_at_most_oneP` and upstream `edgesP`. The
edge-validity clause is kept, and no whole-graph or other guard is added.

`Packing.migration.matching` freezes the raw source and the whole OPG U9 hypercube row. It adds
the complete B11+C25 Original over the frozen matching and B11's frozen
`Legacy.cycle_edgesG` (module alias `CE`), with the same M, the same cycle witness c and the guard
`2 <= d`. B11's `U9Legacy` partial snapshot stays byte-exact; reciprocal stale notes are in both
specs.

Coverage is now 26 mappings and 11 rows; all 23 earlier mappings and the C24 descriptors are
unchanged. `grounding_U9`'s two source clients keep their types and now use the public matching
API. The X6 and X15alone classes stay deferred/excluded. The public client is
`packing-theory/theories/examples/supplied_matchings.v`. Regenerate the compact report with
`python3 meta/migration_report.py matching --write`. Evidence is in coordination
`evidence/C25-by-lancelot/`.
