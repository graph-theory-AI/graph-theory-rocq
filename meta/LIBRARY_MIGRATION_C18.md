# C18: internal-radius shallow minor models

Baseline `311fdcb89dc12a78c62cb0ee6d2477896cbce9a7` is the reviewed C16 commit.
Exactly two X220 helpers move to `Minor.foundations.shallow_minors`:
`x220_ball_in` becomes `internal_ball_in` and `x220_shallow_minor` becomes
`internal_shallow_minor`. The canonical keeps the supplied branch map and the
supplied centre map. Upstream `minor_rmap` holds on the same branch map, centre
membership is a separate clause, and every branch is an internal ball: each of
its vertices is reached from the centre by a walk of at most r edges whose listed
vertices stay inside the branch. The supplied-map adapter
`internal_shallow_suppliedE` proves that, for the same maps, these clauses are
equivalent to the legacy list of centre membership, internal balls, pairwise
disjointness and edge realization.

The standalone ball is vacuous on an empty set and does not assert centre
membership; on a nonempty set the centre is forced. The radius is an exact walk
length: no `graph_dist`, no truncation at the vertex count and no ambient host
distance. A disconnected set is an internal ball for no radius, and radius zero
gives exactly the subgraphs of GTBase `has_subgraph`. C16's ambient contract
stays distinct; no equivalence is claimed in either direction.

Four whole iff certificates cover both helpers, the `x220_polynomial_expansion`
chain and the complete row `polynomial_expansion_bounded_twin_width_statement`
(arxiv:2006.09877#01, open). The chain keeps one polynomial for the whole class
and every depth; the row keeps the class quantifier and one uniform twin-width
bound d. No earlier certificate freezes these names, so no Original module is
needed. The row text, doc block, manifest row and legs are unchanged. The two
grounding clients keep their exact types: one proof re-destructures the
canonical model, the other uses the public reflexivity lemma.

The C15 and C16 specs each excluded `Minor.conjectures.X220.x220_shallow_minor`
as a distinct variant. Both exclusions now belong to C18's certificates and are
removed; every other entry and frozen array is unchanged.

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py shallow_minors --write`; request full details
using `--details /tmp/shallow-minors-details`. Focused proof, normal milestone and
independent-review evidence is retained in coordination evidence.
