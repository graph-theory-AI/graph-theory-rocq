# A8: Ordered edge and nonedge pairs between supplied sets

Contract and exact scope: [specification](migration_reports/edges_between.spec.json), [registry](library_primitives/edges-between.json).
Four Extremal X118/X120/X223 helpers now use `GTBase.common.edges_between` and `nonedges_between`.
They count ordered pairs of arbitrary supplied sets, including empty and overlapping sets.
A shared vertex contributes a diagonal nonedge; an edge within the overlap contributes both orientations.
X118/X120 bodies convert; X223's Boolean association is proved equal without adding a guard.

Disjointness is sufficient for the separate cross-edge and complement-edge readings.
For overlapping full K1 sets, ordered and unordered edge counts are zero, the ordered nonedge count is one, and the complement count is zero.
The X118/X120 rows retain their disjointness conjunct; X223's ct_sparse retains arbitrary sets.
All four rows and two intermediaries keep their quantifiers, rational inequalities, natural subtraction, positive parameters and induced-free guards.

Complete X118/X120 Originals combine frozen A1 induced-free predicates with frozen A8 counts.
Earlier A1 snapshots remain unchanged and retain their documented live pair-count dependencies.
The public client imports only GTBase.base; its corners include overlap, empty sets, complete graphs and guarded interpretations.
Five existing proof bodies adapt to the public API with their theorem types unchanged.

Independent review, exact pins, preservation and validation are recorded in [the review](migration_reviews/edges_between.md).
Regenerate the compact report with `python3 meta/migration_report.py edges_between --write`; use `--details /tmp/migration-details` for full evidence.
Source checks, kernel assumptions, exact types, compiled dependency closures and normal/cumulative gates are separate evidence; final acceptance is tracked on BOARD.
