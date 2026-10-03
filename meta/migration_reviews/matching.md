# Independent review: matching (C1)

Implementer: lancelot. Independent reviewer: arthur (protocol step 10).
Reviewed commit: `23ee661548f0f31878e31de20add0ede2bc0e076`, including predecessor
`535b95f`, relative to `03742d1`. Date: 2026-10-02.
Verdict: approved; no semantic defect found.

This record preserves Arthur's review announced on coordination/BOARD.md at
2026-10-02T21:33Z and the coordinator's separate final statement review in
coordination/evidence/review-C1-coordinator-draft.md. Integration builds and
kernel checks are separate obligations and are not implied by this record.

Arthur checked all twenty frozen objects: three matching helpers, two pre-M1
edge sets, six chain declarations and nine statements. X15's incidence bound,
X14's pairwise disjointness and X180's empty intersections are unconditionally
equivalent to upstream `GraphTheory.connectivity.matching`; they are not
convertible presentations. `fg_edgesE` removes only a redundant inequality
guard, using graph irreflexivity. The public API grounds empty families,
subfamilies and single edges, and excludes loops, empty members and adjacent
edges. The downstream client imports only public modules and exercises both
positive and negative cases.

Each statement theorem has exactly the frozen proposition iff the live
proposition, without an additional guard. The original quantifier order,
hypotheses and bounds are preserved, including `32(m+1)^3`,
`(m+1)^2(16m+29)` and `12m+14` in the three non-corpus LLM-proof variants.
The second and third variants use `sg_edge_set` verbatim in their original
bodies; X180 uses the unchanged `fg_edges`. X15/X14 chains additionally freeze
the pre-M1 edge comprehensions from `061154c`, so their statement certificates
cover both migrations. X18's perfect-matching and X15's partition/family
declarations are frozen dependencies, not additional migrated families.

All statement texts, documentation and statuses remain unchanged: X15 row 02
is refuted, row 03 proved, X18 row 01 partial, Brualdi-Stein open, and X180's
blocked quantifier defect is preserved. X15alone remains excluded from the
build with its documented stronger constant; X6's hypergraph representation
and path_fas's whole-graph predicate remain distinct deferred cases.

Arthur checked the worker's recorded dependency evidence under
coordination/evidence/C1-matching/: eighteen frozen/live probes passed.
Frozen statements reach no live C1 or M1 alias or canonical matching, and live
statements reach canonical matching. Arthur did not independently rebuild
the reviewed commit. His isolated source-report run passed the substantive
checks; the old generator's seven failures were the intentionally absent
long JSON output and six inapplicable corpus/leg checks for explicit
non-corpus variants. The integrated hardened generator accepts these cases
and passes all 193 source checks.

The coordinator read all nine statement-equivalence types and proofs, the
complete public client and final source diffs at the reviewed SHA. Transport
preserves partition/family hypotheses and matching witnesses, all graph-size
and degree guards, and every quantitative bound. The final statement-theorem
check is approved.

The prepared integration preserves all eleven reviewed Rocq source files and
the detailed report spec byte for byte. It moves the matching registry entry
into its family shard, updates the edge-set consumer count from 53 to 51,
preserves B1 and all fidelity records, and corrects the documentation attribution
of `perfect_matching_K2` to `GTBase.common`. The canonical primitive remains
upstream-owned; its fidelity contract and API evidence stay in the matching
registry. No unrelated foundation-fidelity declaration is added.

The rebased worker series ending at `baad954fb5fefbe79cb9d696f979e33f73e49eee`
and its intermediate `ec3d4b97533f743fb9fa34c1fc0c8d95e8fa5421` were compared
against their own base `cd6f10a`. Both series patches are byte-identical to the
reviewed series outside metadata and project files; their five project
registrations and detailed spec are identical. This integration retains the
original reviewed commit as its merge parent.

The preparation regenerated all compact reports, the v2 manifest and overlay,
dependency graph, helper inventory and corpus status through the pinned wrapper.
`make audit` passed: C1 193/193 report checks, A1 264/264 and B1 430/430.
No package build or kernel probe was run in the preparation worktree; the
coordinator runs those gates on the integrated tree.
