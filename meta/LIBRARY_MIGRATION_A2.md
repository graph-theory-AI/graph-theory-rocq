# A2: Set-of-edges deletion

Seven helpers use GTBase.common.del_es_rel/del_edge_set: preserve vertices, remove supplied members of E(G); nonedges have no effect. Original opaque construction proofs are frozen; graph bridges use identity isomorphisms, not proof-term equality. X191's symmetric closure has the same adjacency.

Seven complete rows transport chromatic, bipartite and diameter clauses. X191's blocked encoding and the unused defective triangle-free-diameter completion helper remain unchanged. Public API/client covers exact edge difference, empty/full deletion and nonedges; retained symmetry/irreflexivity lemmas keep their types.

Exact sources, frozen hashes, substitutions, certificates and history:
`meta/migration_reports/delete_edges.spec.json`; ownership/review:
`meta/library_primitives/edge-set-deletion.json`. Compatibility aliases remain
until tracked consumers permit removal; statement meanings/statuses stay fixed.

Through the pinned proof-shell wrapper, regenerate the short report with
`python3 meta/migration_report.py delete_edges --write`, full details with
`--details DIR`, and exact statement types/assumptions with `--check --kernel`
after building its packages. Section/type/dependency probes and normal milestone/
full gates remain separate requirements; exact-pin results are on BOARD and in
coordination evidence. Public API contracts/examples and certificate proofs
remain in their Rocq files; this summary does not replace those checks.
