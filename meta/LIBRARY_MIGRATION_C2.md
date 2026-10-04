# C2: Perfect matchings

X24, X18 and X25 use GTBase.common.perfect_matching: a matching covering every vertex. Exact-one incidence is equivalent without extra guards. The empty family is perfect on K0; invalid edges and odd-order cases remain excluded. Multigraph matchings are distinct.

Three complete rows reuse C1's X18 and M1's X25 frozen chains; X24 also freezes its pre-M1 edge comprehension. Existing bodies/types stay unchanged. Preserve X24's affirmative question reading, X18's partial scope and X25's colouring domain on all vertex sets. Public API/client covers cardinality, K0/K2/K4 and negative K3/loop cases.

Exact sources, frozen hashes, substitutions, certificates and history:
`meta/migration_reports/perfect_matching.spec.json`; ownership/review:
`meta/library_primitives/perfect-matching.json`. Compatibility aliases remain
until tracked consumers permit removal; statement meanings/statuses stay fixed.

Through the pinned proof-shell wrapper, regenerate the short report with
`python3 meta/migration_report.py perfect_matching --write`, full details with
`--details DIR`, and exact statement types/assumptions with `--check --kernel`
after building its packages. Section/type/dependency probes and normal milestone/
full gates remain separate requirements; exact-pin results are on BOARD and in
coordination evidence. Public API contracts/examples and certificate proofs
remain in their Rocq files; this summary does not replace those checks.
