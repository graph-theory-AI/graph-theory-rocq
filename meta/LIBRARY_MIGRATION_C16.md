# C16: ambient-radius shallow minor models

Baseline `15e22500d394e76949607525a6bcafb9469b1287` is the private union of
reviewed A10 and exact C15/C14 sources. Exactly four X128/X139 helpers move to
`GTMisc.foundations.ambient_shallow_minors`. The radius centre belongs to the
branch, but distances use the host and retain `graph_dist`'s finite truncation,
including disconnected pairs. Upstream `minor_rmap` is reused on the same
supplied map; connected, nonempty, disjoint branches and edge realization remain.
The public client separates this radius from internal radius on a connected
path6 branch in a host with an extra universal vertex.

Four whole iff certificates cover both current rows and two complete A7+C16
Originals. The latter reuse A7's frozen edge count with frozen radius/model and
full grad/expansion chains. All older snapshots remain verbatim. X128 keeps its
natural costs, positive t and individual-graph expansion. X139 keeps its blocked
backward-ball defect; this migration changes neither its reading nor its status.
Internal-radius, infinite and ordinary minor models remain distinct.
The four C15 deferred-variant freeze checks now belong to C16's certificates;
their removal asserts no equivalence with ordinary finite minor models.

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py ambient_shallow_minors --write`; request full
details using `--details /tmp/ambient-shallow-details`. Focused proof, normal
milestone and independent-review evidence is retained in coordination evidence.
