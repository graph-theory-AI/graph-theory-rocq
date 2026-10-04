# C24: whole-graph matching

Scope: Digraph path_fas matching and its matching-FAS chain/whole non-corpus theorem.
Canonical: GTBase.matching_graphs.matching_graph, upstream matching on E(G).
The representation stays distinct from C1 edge-family matching.

The public API proves degree-at-most-one and forest-plus-degree equivalences without
nonempty, connectedness or perfectness guards. Public clients cover empty/isolated
graphs, K2, and P3/K3 negative cases; no conjecture import is used.

Frozen Legacy keeps the exact forest/sdeg body. The full FAS equivalence preserves
the same arc-set witness, directed cycles, loop-guarded farc_graph, Delta_star
permutation minimum and bound1. Two old proofs use matchingP; their types stay exact.
No statement, corpus row, status or documented defect is changed.

The matching spec retains its20 C1 mappings and adds three source/chain/whole-row
mappings. Actual source binding is9e03072; the entire path_fas blob equals the worker
baseline. Existing exclusions remain except the migrated whole-graph case.

Reproduce details with meta/migration_report.py matching --details DIR.
Source, kernel, exact-type, strict-dependency and normal X2 evidence:
coordination/evidence/C24-by-lancelot/, C24-review-by-matching-scope/,
C24-normal-gates/ and C24-integration/. Keep generated detail reports external.
Independent review: meta/migration_reviews/matching_graphs.md.
