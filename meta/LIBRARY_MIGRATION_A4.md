# A4: U11 single-edge deletion

U11 sde_rel/sdel_edge specialize GTBase.common.del_edge_set to [set e], retaining discharged Section arguments and implicit status. Relation, original opaque proofs and graph are frozen in dependency order. Invalid e is supported; the upstream del_edges bridge retains its genuine-edge guard.

The reconstruction row, deck chains, Kelly premise and external Whitney statement preserve the edge-index bijection and card multiplicities. Four-edge and same-deck guards remain; Greenwell's implication stays conditional on its registered external theorem. The recorded counterexample still prevents weakening the premise. Existing consumers keep their types; A2 fidelity is reused.

Exact sources, frozen hashes, substitutions, certificates and history:
`meta/migration_reports/sdel_edge.spec.json`; ownership/review:
`meta/library_primitives/single-edge-deletion-u11.json`. Compatibility aliases remain
until tracked consumers permit removal; statement meanings/statuses stay fixed.

Through the pinned proof-shell wrapper, regenerate the short report with
`python3 meta/migration_report.py sdel_edge --write`, full details with
`--details DIR`, and exact statement types/assumptions with `--check --kernel`
after building its packages. Section/type/dependency probes and normal milestone/
full gates remain separate requirements; exact-pin results are on BOARD and in
coordination evidence. Public API contracts/examples and certificate proofs
remain in their Rocq files; this summary does not replace those checks.
