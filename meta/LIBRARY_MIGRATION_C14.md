# C14: supplied-index pathwidth bounds

Baseline: `cdb9e10161e6566b9a812b0931488acb6338be9f`.
Two aliases, X126 and X95, now use `GTBase.pathwidth.pathwidth_at_most`.
The exact contract existentially supplies a graph index then its bags, with B9
path-tree, C13 bag-decomposition and every bag bounded by natural `k.+1`.
Empty graph/index and unused bags remain allowed; there is no numeric minimum
or inserted nonempty guard. Public introduction/elimination, monotonicity,
one-bag cardinality bound and width-zero edge obstruction have a public client.

Two whole current rows and two complete historical iff certificates preserve
uniform functions, guards and conclusions. The complete C13 X126/X95 Original
bodies are reused unchanged, including B6 Thue and B9/C13 frozen chains.
X95's separate embedded-index conclusion keeps its injective edge-preserving
map without tying nodes to bags. All older freezes, statement docs and statuses
remain unchanged; reciprocal notes explain retained partial live dependencies.
The two previously excluded C13 quantitative helpers are now migrated here.

Regenerate the compact summary with `python3 meta/migration_report.py pathwidth
--write` through the pinned wrapper; full details can be requested with
`--details /tmp/pathwidth-details`. Focused/normal checks and independent review
are recorded in external coordination evidence, not inferred from this note.
