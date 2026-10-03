# Independent review: U11 single-edge deletion (A4)

Implementer: arthur. Independent reviewer: matching_scope (protocol step 10).
Reviewed commit: `5ec0f334f5b1825e4fba29bb74252333ec41dd5d`.
Frozen baseline: `9e030727db115917ae077ac07a8fc6aa68661f73`.
Date: 2026-10-02. Verdict: approved; no semantic finding.
This completed review supersedes the draft record's pending-review note.

The reviewer read the full certificate, source and consumer changes. The relation
agrees with `del_es_rel G [set e]` for every vertex set, with no edge-validity
premise. The upstream `del_edges` comparison retains its genuine-edge guard.
The frozen relation, both complete proof bodies and SGraph construction preserve
the Section variables. A verbatim baseline Section was independently compiled;
original/frozen/live `Arguments` agree for all four declarations. Construction
compatibility is a graph isomorphism, with no proof-term identity claim.

The deck bridge retains the same bijective edge-index function in both
directions and composes card isomorphisms with identity isomorphisms. Multiplicity
is preserved. The row, Kelly premise and external statement keep the four-edge
guard and same-edge-deck hypothesis. The transported implication remains
conditional on the same external premise and vertex-reconstruction statement.

At the exact pin, independent pinned-wrapper checks passed: forced serial base
and reconstruction rebuilds; A4 report/kernel 94/94; all snapshot reports and
750/750 statement docs; U11 milestone 11/11, including four axiom-free statements
and 26 forbidden exact-type shapes. An additional probe passed 52 source/type/
closure checks and 28/28 assumptions (ten certificates, eight grounding lemmas,
nine Kelly theorems and the existing implication). Eight compiled dependency
closures show the four frozen roots reach their frozen relation, proof constants
and graph with no live family/canonical deletion references; the four live roots
reach canonical deletion. All eight grounding statements are unchanged; Kelly
changes only `sdel_adjE`'s proof; the implications file is byte-identical. Both
manifests, both leg-state overlays and external registrations are unchanged.

The coordinator separately approved the full row/premise/external iff types
and proofs and the frozen conditional transport at the same exact commit.
VM evidence: `coordination/evidence/A4-review-by-matching-scope/` and
`coordination/evidence/review-A4-coordinator-final.md`.

Integration corrects only the registry note's module names to `ProofsLegacy`
and `GraphLegacy.sdel_edge`, records these approvals, and regenerates metadata.
The reviewed Rocq files and detailed specifications remain byte-exact. Earlier
families and review fields are preserved; broad integration gates remain
coordinator-owned.

Preparation uses B3 merge `ae9945b150dca12b222a20d16d2038879c444576` as first
parent and the exact reviewed A4 commit as second parent, without conflicts.
All four A4 Rocq files, its project and three detailed specifications match the
worker pin byte-for-byte. The 2,372 protected predecessor files are unchanged;
A2/A3 registry changes are exactly the reviewed deferred-variant notes, with
their earlier review fields intact. Pinned-wrapper regeneration and `make audit`
pass, including all eleven compact reports (A4 94/94). Only the helper inventory
changes among shared generated metadata. No package build or broad proof gate
was duplicated in the preparation checkout.
