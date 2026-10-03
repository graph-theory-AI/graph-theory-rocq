# Independent review: edge-set deletion (A2)

Implementer: arthur. Independent reviewer: marcol (protocol step 10).
Reviewed commit: `dbee364e6be7ac2e9a8e7edecbb1ff5f0878c8c0`, based on `0259cec`.
Frozen-source baseline: `03742d1`. Date: 2026-10-02.
Verdict: approved; no blocking semantic finding.

This record preserves marcol's review on coordination/BOARD.md at
2026-10-02T21:37:47Z and the coordinator's separate final theorem check in
coordination/evidence/review-A2-coordinator-draft.md, approved by the coordinator
as the final check of the seven statement equivalences. Integration gates remain
separate.

Marcol read both complete certificate modules, the seven source replacements,
the API and public client, the family registry and fidelity fragment, and the
frozen statements with their full affected chains. The hardened source report
passed 221/221 checks over 28 frozen objects: seven sources, fourteen chain
objects including six symmetry/irreflexivity proofs, and seven statements.
An independent reverse-dependency scan found exactly the seven affected rows,
including the two extremal XE2 rows through the extremal XE1 helper.

The frozen graph constructors use their own frozen symmetry and irreflexivity
proofs. The six complete proof bodies match the baseline modulo the explicit
Legacy qualification. The construction bridges compare the graphs formed from
frozen and live proofs by identity isomorphism; they do not equate opaque proof
terms. X191's symmetric closure is undone using symmetry and irreflexivity,
without an additional premise. Arbitrary edge families, non-edge members, empty
deletion, deletion of all edges, singleton deletion and the retained vertex
type are covered by the API and grounding examples.

Marcol independently built the two certificate modules and checked all fourteen
frozen/live statement dependencies: no frozen closure reaches a live family
helper or chain, and every live closure reaches the canonical deletion and its
alias. All 32 compatibility theorems were closed under the global context.
Arthur's separate SHA-bound dependency probe and outputs are recorded at
coordination/evidence/A2-delete_edges/print_all_dependencies_{probe.sh,summary.txt,full.txt.gz}
in the VM coordination area.

The coordinator personally read both full certificate modules, the source diff,
the public API/client and all seven statement proofs. Every bridge is the
unconditional equivalence between the complete frozen statement and its live
counterpart. Size, degree, chromatic-number, vertex-criticality, edge-membership
and rational-exponent conditions remain in their original quantifier positions.
Chromatic number transfers through `chi_diso`, bipartiteness through the
isomorphism and its inverse, and diameter through `ball_diso`. X191's unused
outer constant and blocked encoding, X7's partial status, and XE2's solved
statuses are preserved.

Single-edge deletion in X60/X64/U11 and the documented dead completion consumer
remain unchanged. No older certificate on the A2 base references the migrated
family chain; the M1/A1 single-edge dependencies are reserved for A3. No repair
of an existing statement encoding is included here.

The prepared integration is based on the reviewed C1 merge and retains all A2
Rocq source and detailed spec bytes from `dbee364`. The only project conflicts
are resolved by retaining B1/C1 registrations and adding A2's client and
certificates. The shared module contracts and other family registries remain
unchanged. The coordinator must regenerate metadata and run the final combined
builds, exact-type/assumptions probes and integration gates after merging.

Preparation validation through the pinned wrapper regenerated the four compact
reports, v2 manifest and overlay, dependency graph, helper inventory and corpus
status. `make audit` passed: A2 221/221 source checks, A1 264/264, C1 193/193 and
B1 430/430. Byte comparisons confirmed all eight A2 Rocq files, its detailed
spec and fidelity fragment exactly match `dbee364`; the family registry differs
only in the approved review fields. No package build or kernel probe was run
in the preparation worktree.
