# A7: undirected edge counts

Eight `sgraph -> nat` sources migrate to `GTBase.common.edge_count G := #|E(G)|` in three representation classes.
The unordered counts are Chromatic XE1.xe1_edge_count, Extremal X76.x76_edge_count, X78.x78_edge_count and D2ram.edge_count; their bridges are conversions.
Cycle X5.x5_edge_count and Extremal X4.x4_edge_count/D2tur.edge_count count enum-rank-oriented adjacent pairs; `edge_count_rank` proves equality by the finite bijection to doubletons, without extra guards.
Public `GTBase.finite_graph.fg_edge_count` is also migrated: `fg_edges` remains unchanged, while public `fg_edgesE` and `card_fg_edges` justify its doubleton-comprehension bridge without importing migration modules.
D2tur's count of both orientations, cut sizes and within-colour counts remain distinct quantities.

The complete current scope is 40 rows and 20 intermediate predicates, including five public-count rows: Extremal X143/X180/X207 and GTMisc X128/X139. Chromatic XE1's helper has no reaching row.
All whole statements retain their quantifiers, extremality/minimality clauses, arithmetic/positivity/nonempty guards, documented limitations and leg statuses.
Frozen bodies and exact helper/chain/whole-row certificates are specified in [edge_count.spec.json](migration_reports/edge_count.spec.json); the compact [report](migration_reports/edge_count.md) records checked coverage.
Count equalities and whole-row iff certificates are distinguished: the rank bridge and B2 internal-disjointness transport need proved, opaque certificates; no proof-term identity or mere-conversion claim is made for them.
The public [client](../base/theories/examples/edge_count.v) uses the canonical API for rank counts, isomorphism invariance, positivity, empty/small complete graphs and the ordered-pair distinction. Existing proof-consumer theorem types remain unchanged.

Complete histories compose earlier frozen predicates without editing earlier snapshots: the full original chains and rows are indexed by the spec and [registry](library_primitives/edge-count.json).
`XE2PathEdgesOriginal` completes #915 before B2/A7/B8 using raw rank count, frozen internal disjointness and frozen path-edge disjointness.
`XE2CycleOriginal` completes #767 before A7/B4/B10 using raw rank count, B4's frozen incident-chord predicate and B10's frozen raw cycle; neither chain nor row reaches a live M1 alias.
`X180Original` composes C1's frozen multitasker capacity with the frozen public-count average-degree chain. Reciprocal notes retain the earlier partial snapshots.
Precisely five other Original rows retain live M1 aliases: X76/X78 through `x76_edge_set`/`x78_edge_set` in cut sizes, and #567/#613/#742 through `x4_edge_set` in earlier B4/A2 predicates. Their count snapshots are frozen, but these rows are not claimed to be pre-M1; A9 later completes X76/X78.
#916 retains its support dependency. The complete raw rank-count/support A7+B12 Original remains due from B12 when it integrates after A7; both initial snapshots stay.

Preserved issues: D2ram's common-graph prose says PARTIAL while its manifest/legs say done; the finite eventual factor-1 inequality, threshold and nonempty pattern H guard remain unchanged. #915 keeps its stronger internal-and-edge-disjoint conjunction; X88 keeps its existing formal-name/edit-distance mismatch. These are separate re-audit matters.
Public contracts and proof explanations remain in [common.v](../base/theories/common.v), [finite_graph.v](../base/theories/finite_graph.v) and the certificate modules. Ownership and fidelity remain in the registry and [fidelity fragment](foundation_fidelity/edge-count.json).
Regenerate compact evidence with `python3 meta/migration_report.py edge_count --write`; add `--details /tmp/edge-count-details` for full evidence and use `--check --kernel` after building for exact certificate checks, always through the pinned proof wrapper.
Independent reviews and exact gate outcomes are recorded separately in coordination evidence and the integration review record; this note makes no cumulative-gate acceptance claim.
