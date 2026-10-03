# C21: poset unavoidability

Baseline `97605ddae838bc6e84b0602240148246e9d065f2` is the fixed C20 commit. Exactly one source
moves: `Minor.conjectures.X228.x228_unavoidable` now unfolds to
`Minor.foundations.poset_unavoidability.poset_unavoidable H`, a new focused Minor module with the
identical body. One natural threshold d is chosen before all finite posets. Every poset whose
dimension is not at most d has H as a minor of its cover graph, host before pattern. GTBase.posets
(finite posets, cover graphs, realizer dimension) and upstream `minor` are reused unchanged. d = 0,
empty carriers and empty graphs stay allowed. A realizer may be empty, so a one-point poset has
dimension at most 0; no nonempty-realizer or positive-threshold convention is introduced.

The helper and the whole row `unavoidable_minor_kelly_construction_statement`
(arxiv:2002.00496#02) are frozen verbatim. The helper iff is a conversion and the row has a
complete iff. The row stays BLOCKED: its implication to Wagner planarity and treewidth at most three
is the existing placeholder consequence of Kelly's construction, kept exactly; no construction,
converse or status change is made. There is no earlier frozen history. All eleven grounding theorem
types and the sibling queue-number row with its proofs are unchanged.

The registry also lists `Digraph.conjectures.unvd.unavoidable`, which shares the normalized name,
as a deferred, distinct exact-order tournament contract; it is untouched and is also a documented
distinct variant of the report. No earlier exclusion is removed.

The public-only client checks the empty graph, raising a threshold, minor downward closure, and
the unit poset: it has dimension at most 0, so the guard never tests it, and its one-vertex cover
graph has no K2 minor. That shows the guard has teeth; it is not a claim that K2 is avoidable.

Regenerate the compact report through the pinned wrapper with
`python3 meta/migration_report.py poset_unavoidability --write`; request full details with
`--details /tmp/poset-unavoidability-details`. Focused proof, normal milestone and
independent-review evidence is retained in coordination evidence.
