# Migration report roles: implementation and coordinator review

Implementer: coordinator helper family_scope. Baseline: prepared A6 0659592.
Exact implementation: `86aa0333f82d9870d783708339c59e12f61e066b`.
The coordinator independently read every checker and test change and approved
the code. At preparation, required full mutation validation was still running
on that immutable pin; this record does not claim a mutation pass or final
integration acceptance. The final outcome is recorded in
`coordination/evidence/report-kind-hardening/root-mutation-86aa033.log` and BOARD.

Complete-row obligations are derived from baseline dependency discovery and
baseline/current manifests, independently of each object's role and corpus
claims. Every occurrence requires statement/original-statement and its full
closed iff probe. Direct check_kernel calls perform the same validation.
Missing, nonstring and unknown roles fail closed. New nonstatement history uses
`historical`; the eight existing historical tags remain accepted, with the
existing m1-frozen registration exception unchanged. Prop-valued helpers,
Records and opaque graph-construction proof fields do not acquire bogus iff
or proof-equality obligations. Existing valid report counts stay unchanged.

Validation: 51 focused tests pass, including seven compiled tests. Mutations
retain a valid primary row and a genuine first Original before a second
Original with a closed but falsely guarded theorem; unknown/known nonstatement
roles and misleading corpus/non-corpus claims cannot hide it. Genuine multiple
Originals, explicit non-corpus rows, every historical role, Records and an
actual SGraph isomorphism over separate opaque proofs pass.

All 19 baseline source reports pass without spec or summary edits. Read-only
validation of the separately built C7/A6 ae0e605 snapshot passes its 242 source
and kernel checks with the new checker. No Rocq source or statement changed.
Detailed logs remain outside git in coordination/evidence/report-kind-hardening/.
Lexical dependency discovery still requires separate Section and kernel closure
review; this change does not replace that evidence.

The separate tooling merge is based on reviewed A6 0659592 and preserves its
Rocq sources, projects, family registries, specifications and review fields.
Both checker and test files remain byte-identical to the reviewed implementation.
The prepared merge's full source audit passes, including all nineteen report
checks, with no generated metadata or summary drift. Root integrates only after
the separate mutation run succeeds.
