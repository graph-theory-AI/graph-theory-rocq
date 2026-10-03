# C15: finite supplied branch-set minor maps

Baseline: `35b6b165295fb373d864d646d74284c4751dae65`.
X200's nested predicate and Digraph's pair-witness predicate now alias upstream
`GraphTheory.core.minor.minor_rmap` on exactly the same `H -> {set G}` map,
with host G and pattern H in their original order. Public GTBase adapters prove
the conjunction, disjointness and edge-witness conversions unconditionally.
They introduce no duplicate canonical predicate, inducedness, host coverage,
radius or global inhabitance guard. Empty H remains valid; a supplied vertex
of H rules out an empty host. Extra host edges and unused vertices are allowed.

Two sources, five dependent definitions and six whole statements are frozen.
The six iff certificates preserve the X200 positive-k logarithmic envelope,
all original loopless/asymmetric premises, the planar oriented maximum and
M.-1 sharpness, and the acyclic-subset cardinal bound. The sixth declaration is
explicitly non-corpus and retains its absence of an asymmetric-arc premise.
No earlier snapshot reaches these helpers; all old snapshots remain unchanged.
Infinite, ambient-radius, internal-radius and subdivision contracts stay separate.
The registry also indexes the unchanged Infinite `minor_model` namesake as a
deferred distinct class; only the two finite members are migrated here.

The canonical is upstream-owned: its FAITHFUL contract and registered public
adapter evidence live in the family shard, as for other upstream-owned families.
The new public module contains lemmas only, so no repository primitive override
is appropriate. Regenerate the compact report with `python3
meta/migration_report.py minor_models --write` through the pinned wrapper;
use `--details /tmp/minor-model-details` for full evidence. Focused proof checks,
normal milestones and independent review are recorded in coordination evidence.
