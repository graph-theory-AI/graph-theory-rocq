# Independent review: path trees (B9)

Implementer: Marcol. Independent reviewer: coordinator helper path_review.
Approved exact `299dc71b0999743f91a1931378608078a4ef0df0` on 2026-10-03,
with source baseline `e377dcbcf549c044b7b2a4321831792c1c78f375`.
Root separately read and approved all four full statement equivalences and the
complete X126Original equivalence on the same pin.

The four X126/X189/X105/X95 helpers remain convertible to
`is_tree [set: T] /\ Delta T <= 2`. The focused public module imports `base`
without a cyclic re-export. Actual upstream conventions admit the empty graph,
K1 and K2; proofs exclude the triangle and claw. No nonemptiness guard is added.
All statement quantifiers, pathwidth bag bounds, connectivity, negative
occurrences and induced-copy density guards remain intact. X189's documented
KNOWN-UNFAITHFUL blocked encoding is preserved without repair. X126Original
composes the complete frozen B6 Thue chain with frozen B9 pathwidth; all older
bodies remain exact, with one additive reciprocal historical note.

Independent validation: 21 freshly forced modules across four packages,
including the public client and reused B6 module; 33 closed assumptions;
five complete iff types, eight whole-helper conversions, exact API/corner
and fully qualified Original binding probes; ten strict dependency closures.
Twelve new frozen declarations match the pinned source with declared
substitutions, and five reused B6 declarations match their own baseline.
The independent family kernel report passes 118/118 and all nineteen worker
snapshot source reports pass. The focused review is separate from worker
normal milestones and cumulative integration acceptance.

Prepared on reviewed B8 `6f798c0`, preserving its twenty-one frozen
specifications, all previous source/proof bodies, fidelity, review records,
tooling and metadata except routine regeneration. The four project additions
are unioned with prior entries. All B9 Rocq and specification bytes remain exact
to the approved worker pin; registry changes only record this review.
This merge introduces neither C7 nor A7 and makes no claim about future history.

Detailed evidence remains outside git in
`coordination/evidence/B9-review-by-path-review.md`,
`coordination/evidence/review-B9-coordinator-final.md`, and
`coordination/evidence/B9-integration/`.
