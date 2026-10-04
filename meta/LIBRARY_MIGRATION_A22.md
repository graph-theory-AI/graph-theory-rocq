# Library Migration A22: Closed Balls

Twelve sources share two contracts: seven recursive vertex balls and five unions over a supplied seed set.
Vertex aliases use the existing `GTBase.base.ball`; `GTBase.balls.set_ball` supplies the seed-set view.
The original ball Fixpoint, its Power Section and graph_power stay unchanged; three public lemmas follow End Power.
No connectedness, nonempty-seed or positive-radius guard is added. The relation-ball bridge is explicit;
there is no unconditional bridge to truncated graph_dist on disconnected hosts.

The registry is `meta/library_primitives/ball.json`, the authoritative specification is
`meta/migration_reports/balls.spec.json`, and fidelity is `meta/foundation_fidelity/ball.json`.
All 65 frozen mappings and 14 complete iff remain: eight current rows plus six B1/B5/B10 whole Originals.
The actual imported path-support, endpoint-path/separator and cycle/forest-after objects remain bound to their pins.
Distinct recursive legacy constants are proved equal by induction; live aliases are transparent.
The vocabulary_packing radius-induction proof and every old theorem type remain unchanged.

Current rows are GTMisc X20/X39/X40/X113/X116/X146 and Packing X26/X111; the six Originals cover all except X20/X111.
Preserved details include X20's positive-order/connectivity/least-square premises and predecessor subtraction;
X39's k-before-c-before-d order; X40's distance-two/positive-ell partial model; X113's uniform f/g;
X116's bound depending on k and d; X146's unchanged guarded A-path; and X26's d=0 reading/Delta/C*k guards.
X111 preserves one constant before r/G/U, Wagner planarity and the exact arg-min/default and maximum values.
All row statuses, witnesses and earlier partial snapshots remain unchanged, with explicit reciprocal notes.

C16 ambient-radius predicates and C18 internal balls retain their separate owners and contracts, including X139's defect;
only obsolete assertions that those aliases stayed untouched since the A22 baseline are removed.
The arbitrary-relation rel_ball and X161 local chromatic invariant remain distinct.
Public API/client and two area certificates are under base/, graph-theory-misc/ and packing-theory/.
Reproduce compact reports with `python3 meta/migration_report.py --all --write`; source/kernel checks use `--check --kernel`.
Detailed immutable source, independent/root review and integration evidence are under coordination/evidence/A22-*;
combined gate acceptance is recorded separately from the author's inherited generated-drift diagnostics.
