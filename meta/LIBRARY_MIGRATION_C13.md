# C13: supplied bag-decomposition contracts

Baseline: `58d6d6090cfe12c200bc4ab64f86858074098294`.
Implementation: Lancelot draft, completed by coordinator helper family_scope after
quota handoff; original draft and logs are preserved in external coordination evidence.

Four helpers now use `GTBase.bag_decompositions`: X126/X27 retain Boolean coverage,
X189 transports equivalent Prop coverage, and X169 retains its explicit tree guard.
All refer to the same supplied graph, index and bags. No forest, tree or nonempty
index guard is inserted into the three raw interfaces. The public bridge to
upstream `sdecomp` requires the same supplied forest; quantitative widths and the
existing forest-to-tree proof stay unchanged. The old Minor `restrict_bag` theorem
keeps its type and delegates to the extracted public lemma.

Freeze all 16 reaching chains and 11 current rows. Seven complete Originals also
combine B6/B9 for X126, B9 for X189/X95, B4 for X27, A1/B4 for X42, B1/B3 for X67,
and M1/A1 for X102. All 18 full statement iff certificates retain quantifier order,
natural `k.+1` bounds, logarithmic grouping and guards. X189's explicit root and
known spaghetti defect, X169's token-path defect, existing statuses and all older
snapshots remain unchanged. Older partial snapshots receive reciprocal notes.

Public-only examples exercise empty graph/index (including the tree guard),
K1/K2, each failed coverage/fibre clause, a valid cyclic raw index rejected by the
tree guard, unused empty bags, nonempty-index consequence and upstream transport.
The compact report and its spec provide reproducible exact source/statement
coverage. Independent step10, root final whole-iff review and normal milestones
remain required; implementation evidence does not substitute for those reviews.

Regenerate: `python3 meta/migration_report.py tree_decomposition --write` through
the pinned proof shell. Detailed checks stay in coordination evidence, outside git.
