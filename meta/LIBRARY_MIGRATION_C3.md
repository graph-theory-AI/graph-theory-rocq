# C3: indexed simple-edge partitions

`Packing.conjectures.X15.x15_edge_partition` now aliases
`Packing.foundations.edge_partitions.edge_partition`. The public predicate
retains the original coverage equation and disjointness at distinct indices.
Empty parts and repeated empty parts remain allowed, including zero parts on
an edgeless graph. MathComp's set-of-blocks `partition` requires nonempty blocks
and cannot replace this indexed contract unconditionally.

The API proves coverage, each-part containment in `E(G)`, unique-index counting,
injectivity on nonempty parts, and the cardinal sum. Grounding and a public-only
client include zero parts, repeated empty parts on `K_2`, duplicate nonempty
parts, and invalid loop members.

The three affected statements are X15's
`fair_matching_edge_partition_statement` and X18's
`knn_fair_perfect_matching_statement` and
`brualdi_stein_partial_transversal_statement`. Their guards, quantifier order,
doc blocks, corpus statuses and known discrepancies are unchanged. In particular,
X15's existing local refutation note and X18's partial source status remain.

C1 already froze the source and all three complete statement chains over the
pre-M1 edge comprehension and original matching/perfect-matching bodies. C2
preserved those bodies. C3 adapts only C1's partition bridge and adds
`Packing.migration.edge_partitions` as the family entry point over the same
snapshots. No frozen body or old statement theorem changes.

The identical helper in excluded `X15alone.v` remains unchanged and unbuilt.
Its distinct statement is not claimed. `edge_family`, the four matching
underrepresentation variants, multigraph list partitions, clique partitions
and vertex partitions remain separate.

Regenerate the compact summary with
`python3 meta/migration_report.py edge_partition --write`; regenerate full
details on demand with `--details DIR`. The spec records the baseline and
substitutions, including the M1/C1/C2 history. Source checks are separate from
`--check --kernel` exact statement-type and assumption probes. Additional
dependency evidence is kept in `coordination/evidence/C3-edge_partition/`.

Step 10 review is assigned to Arthur, with final statement checks and integration
by the coordinator. See BOARD.md for the exact reviewed commit and gate results.
