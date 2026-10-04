# C20: strong induced-subdivision models

Baseline `952a89bdecf65bed9be3a1393eabc91ca091d26c` is the fixed C19 commit. Exactly four
sources move to the new focused module `GTBase.induced_subdivisions`, which `base.v` does not
re-export: `Extremal.conjectures.X98.x98_induced_subdivision_model` and
`x98_induced_subdivision`, `GTMisc.conjectures.X114.x114_induced_subdivision_model` and
`x114_induced_subdivision`. The canonical Record `induced_subdivision_model H G` keeps the
pattern before the host and all seven fields. It has injective branch vertices and a full vertex
sequence for every ordered pair. Pattern edges need endpoint-inclusive induced paths: nonempty,
from branch u to branch v, duplicate-free, along host edges, with chords only between
consecutive entries (`seq_consecutive`). Internal vertices avoid every branch vertex, a shared
internal vertex forces the same undirected edge, and global inducedness runs over the C19 raw
support. `induced_subdivision H G` is its inhabitation.

The Prop field formulas are written exactly as the local copies unfold, so every old field type
is convertible to the canonical one and no proof-irrelevance or extensionality is needed. The
local Records become aliases of the canonical Record. The constructors `X98Model`/`X114Model` and
all fourteen projections remain as definitions with the old binders, types and implicit
arguments; `About` prints them identically before and after. The local path, internal-vertex and
support helpers keep their bodies. No reversal coherence, off-edge restriction, nonempty-graph or
positive-length guard is added, and Minor's interior-list `subdiv_model` stays distinct.

Seven current objects are frozen verbatim: the two Records (type, constructor, fields), the two
wrappers, the X114 decision problem and both complete rows. Records are related by two-way
field-by-field transports that cancel. The problem has membership, full in-NP verifier and cost
witnesses, and NP-hardness reductions transported. Each row has a whole iff. The complete rows
reuse C19's `X98Original` (B3 path helpers, A5 `x59_subgraph_of`, raw support) and `X114Original`
(B3 path helpers, A14 `Delta H <= 3`, raw support); their Records and problem are fully frozen
and their certificates compile unchanged through the wrappers. All older frozen bodies stay
verbatim. A5's and A14's partial rows that keep this family's live names are documented here, and
C20's current snapshots are documented reciprocally in the B3, C19, A5 and A14 specs. The
wrappers add direct consumers of B3's and C19's helpers, so those families' `consumers_remaining`
counts are updated.

All 26 existing proof consumers and 12 repackaging definitions in the B3, C19, A5 and A14
certificates compile unchanged. The exact-signature wrappers are new conjecture-local
definitions, so the inventory gains seven two-member repeated-name groups (branch,
branch_injective, edge_path, edge_path_valid, internal_avoids_branch, paths_internally_disjoint,
global_induced). They are compatibility wrappers to remove once their consumers reach zero.

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py induced_subdivisions --write`; request full details with
`--details /tmp/induced-subdivisions-details`. Focused proof, normal milestone and
independent-review evidence is retained in coordination evidence.
