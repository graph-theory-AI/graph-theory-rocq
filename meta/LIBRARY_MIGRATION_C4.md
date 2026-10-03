# C4: indexed edge families

`Packing.conjectures.X15.x15_edge_family` now aliases
`Packing.foundations.edge_families.edge_family`: every indexed member is a
subset of `E(G)`. The contract permits overlapping, repeated and empty members;
zero indices are valid on every graph. It imposes no partition condition.

The public API exposes membership, shrinking, arbitrary reindexing, and
upstream powerset/union presentations. A public-only client includes repeated
nonempty overlapping members on `K_2`, zero indices on `K_2`, empty members,
and rejection of singleton-vertex and empty-vertex-set edges.

The four X15 underrepresentation statements retain their quantifier order
(`forall m, exists c`, before choosing graph and family), bipartiteness,
positive maximum degree, natural-number floor/ceiling arithmetic, and their
four different conditions on the constant. One is a corpus row; the three LLM
variants retain their explicit non-corpus classification. No statement,
documentation block, formal resolution or corpus status changes.

C1 already froze the source over the pre-M1 edge comprehension, original
matching, and all four full statements. C4 reuses every frozen body and theorem
type; only the C1 helper proof unfolds the new alias. Its own thin certificate
module exposes the helper and four statement equivalences. C2/C3 entry points
and excluded `X15alone.v` remain unchanged.

The `fair_matching.v` consumers are `x15_rounds_instance`,
`x15_llm3_proof`, `x15_llm2_proof`, `x15_llm_proof`, and
`bipartite_matching_underrepresentation`. All five are rebuilt and checked for
assumptions; the registered resolution also receives its exact-type gate.
Their types remain unchanged. The core proof now consumes the public subset
premise directly, removing the obsolete rewrite through `x15_edge_set`.

Regenerate the compact report with
`python3 meta/migration_report.py edge_family --write`; use `--details DIR`
for full evidence. The spec retains source hashes and all historical
substitutions. `--check --kernel` checks the exact four statement equivalences
and named assumptions; separate helper-type and frozen/live dependency probes
are retained under `coordination/evidence/C4-edge_family/`.

Arthur approved step 10 at exact `57d6b9f`; the coordinator separately approved
all four final statement equivalences and the proof-only consumer adapter.
See `meta/migration_reviews/edge_family.md`. Integration regenerates earlier
compact summary counts; BOARD.md records the exact gate results.
