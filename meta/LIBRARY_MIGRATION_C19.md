# C19: raw model support

Baseline `bb0bf3cd7c1d14e014704ebd5e24b03e4c475cb8` is the private union of exact
C18 `15a5a5c` and reviewed A14 `f52251a`. Exactly three sources move to the new
focused module `GTBase.model_support`, which `base.v` does not re-export:
`Extremal.conjectures.X98.x98_model_vertex`,
`GTMisc.conjectures.X114.x114_model_vertex` and the public
`Minor.foundations.containment.sdm_covers`. The last keeps its Section shape, so
its discharged type still takes `K H : sgraph` and `m : subdiv_model K H`; it is
enrolled through an immutable `repository_sources` descriptor.

The canonical `model_support br ep x` is RAW support on supplied data, pattern
before host: `x` is a branch image `br h`, or a member of the supplied list
`ep u v` of a genuine pattern edge `u -- v`. Both orientations contribute, lists
on non-edges are ignored, the empty pattern supports nothing, and an edgeless
pattern supports exactly the image of `br`. Nothing is asked of injectivity, path
shape, inducedness, reversal or disjointness. X98 and X114 read it on full edge
paths and Minor on subdivision interiors; the Records around them are not
identified and none of their fields changes.

Sixteen current objects are frozen: the three sources; nine chains (the X98 and
X114 seven-field Records with their `inhabited` wrappers, the X114 decision
problem, `subdiv_rep`, `is_subdivision_of`, `x220_theta`, `x220_prism`); and four
complete rows (X98, X114 and two X220 rows). The frozen `sdm_covers` is closed in
its own Section; the frozen `subdiv_rep` then names it and the discharged
`sdm_realises` with explicit Section arguments. Records are related by two-way
field-by-field transports that cancel, problems by membership, NP and NP-hardness
transfer, and every row by a whole iff.

Three complete Originals compose earlier histories with this family's frozen
support: X98 with B3's frozen path helpers and A5's frozen `x59_subgraph_of`;
X114 with B3's frozen path helpers and A14's frozen `x114_subcubic`; the X220
theta/prism row with B4's frozen even-wheel chain. Earlier certificate modules are
aliased without Import. Every older frozen body is unchanged. The five older
snapshots that keep this family's live names (B3's two Records, A5's X98 row,
A14's X114 row, B4's theta/prism row) are documented here, and the five C19
current snapshots that keep their families' live names are documented
reciprocally in the B3, A5, B4 and A14 specs. C15 drops exactly its three
now-migrated raw-support exclusions; C18's earlier removals stay.

No consumer needed a change: all twenty-eight direct proof headers and the import
closure rebuild unchanged. Regenerate the compact report through the pinned
wrapper with `python3 meta/migration_report.py model_support --write`; request full
details with `--details /tmp/model-support-details`. Focused proof, normal
milestone and independent-review evidence is retained in coordination evidence.
