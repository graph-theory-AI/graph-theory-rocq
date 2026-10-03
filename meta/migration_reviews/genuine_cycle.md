# Independent review: genuine sequence cycles (B10)

Implementer: Marcol. Independent reviewer: coordinator helper path_review.
Approved exact mathematical source `e1dc8ddbfc2b5b2111ec689bab26791f5b18dfe6`
and the complete corrected series `0a0203ee4e1ff00605e4cbfa89108dcbea0e812f`
on 2026-10-03. Private source baseline `00d6bb3a80759b365fffab282d47603510bf839e`
is a source-preserving union of reviewed B9 and A6. Root separately read and
approved all seventeen complete row iff theorems and five complete Originals.

The seven Prop helpers and one Bool helper retain their exact arbitrary-relation
or simple-graph contract: ucycle/ucycleb plus the guard 2 < size c. No symmetry,
looplessness or extra guard is added. The API preserves the closing edge,
uniqueness, empty/singleton/digon rejection, rotation and directed orientation.
Reversal uses the converse relation in general; same-relation reversal has an
explicit sufficient symmetry hypothesis. The public client imports only GTBase.base.
B1, B4 and A5 historical chains and imported aliases are fully bound in the five
Originals. All earlier frozen bodies and theorem types remain unchanged.

Independent checks passed at immutable e1dc8dd: 77 freshly forced dependency
sources across seven packages, including public client and existing proof
consumers; 90 closed assumptions; 22 exact complete statement iff types; 44 strict
frozen/live dependency checks; helper conversion/type and qualified historical
binding probes. All 51 frozen declarations match their pinned baseline, with
coverage independently rediscovered as eight sources, sixteen intermediaries
and seventeen rows. 2,478 protected predecessor files and all earlier frozen
arrays are exact; seven reciprocal notes are additive. Family kernel report
passes 435/435 and all 22 worker-snapshot source reports pass.

Follow-up 0a0203e corrects four sufficiency descriptions. Independent structural
comparison proves that walks_paths.v changes only in comments, the three JSON
deltas are prose strings, and every proof, type and frozen object remains exact.
The mathematical approval therefore extends to this exact pin.

Prepared on reviewed C10 `35fdad457094187e90cad033b9fc6d487fbe13f9`, preserving
all 24 earlier frozen specifications, source/proof bodies, review/fidelity and
tooling records. Ordered project unions retain earlier entries; predecessor B8
prose corrections in walks_paths.v remain intact. Only this family's review
fields, seven reciprocal notes and routine regenerated metadata are added.
No A7 or C7 dependency is introduced. An A7/B10 #767 Original is owed if that
separate family integrates first.

This is independent source review and mechanical preparation, not complete
integration acceptance. Normal, unscoped Digraph XE2 remains required/pending;
focused compilation and scoped worker checks do not replace it. Root owns the
combined integration gates and final main-branch advance.

Detailed evidence remains outside git in
`coordination/evidence/B10-review-by-path-review.md`,
`coordination/evidence/review-B10-coordinator-final.md`, and
`coordination/evidence/B10-integration/`.
