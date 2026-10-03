# C3: Indexed simple-edge partitions

X15 uses Packing.foundations.edge_partitions.edge_partition: exact coverage of E(G), disjoint at distinct indices. Empty/repeated empty parts and zero parts on edgeless graphs are allowed. MathComp's nonempty set-of-blocks partition is not an unconditional replacement.

Three X15/X18 rows reuse C1's pre-M1 matching/perfect-matching snapshots preserved by C2. Frozen bodies and old theorem types remain. X15's refutation note and X18's partial scope stay; excluded X15alone remains unbuilt. Public API/client covers containment, index/cardinality counting and invalid members; other partition/family representations stay separate.

Exact sources, frozen hashes, substitutions, certificates and history:
`meta/migration_reports/edge_partition.spec.json`; ownership/review:
`meta/library_primitives/edge-partition.json`. Compatibility aliases remain
until tracked consumers permit removal; statement meanings/statuses stay fixed.

Through the pinned proof-shell wrapper, regenerate the short report with
`python3 meta/migration_report.py edge_partition --write`, full details with
`--details DIR`, and exact statement types/assumptions with `--check --kernel`
after building its packages. Section/type/dependency probes and normal milestone/
full gates remain separate requirements; exact-pin results are on BOARD and in
coordination evidence. Public API contracts/examples and certificate proofs
remain in their Rocq files; this summary does not replace those checks.
