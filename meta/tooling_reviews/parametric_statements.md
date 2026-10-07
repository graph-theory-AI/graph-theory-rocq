# Section-parametric statement enrollment review

Tooling series on `marcol-psec-tool`, started at integrated
`bfb3d6f943d029a708c937bbb9edf335cd47ba97`. Implementer: marcol. Independent
reviewer: Lancelot (after A25 author work); root reviews the complete tool
semantics before integration. Design, review findings and the decision record
are in `coordination/evidence/resume-2026-10-06/section-parametric-enrollment-design*`
(r1, Master findings, r2) and `section-parametric-r2-analysis/`.

Optional `parametric_statements` enrolls reached, build-listed whole Props that
lie directly in one top-level Section, outside the corpus manifests, with an
explicit non-corpus frozen statement. It is separate from and disjoint with the
nullary `additional_statements`, whose validator is byte-identical and still
rejects Section Props; nothing is enrolled because its type ends in `Prop`.
Each entry pins the Section label, its complete `Variable` scaffold, the
discharged parameters in Section order with fully qualified kernel types,
generated `@`-bindings of referenced same-Section declarations, and a top-level
live-shape witness. Scope parsing records enclosing scopes, so labels are unique
per scope (a frozen copy's Section inside its Legacy module and the witness's
top-level Section may share the original label). Binding targets are excluded
through the provider-resolved dependency reach at the baseline, the current tree
and every snapshot commit. History must be plain: baseline and snapshots are
ancestors, and replacement refs and grafts are rejected. Parametric
`original-statement` snapshots are checked at their own commits, and the
stale-snapshot scan treats parametric endpoints as live names.

Kernel mode states, with every endpoint `@`-applied, the exact discharged types
of the frozen copy, the live endpoint and the witness, the pointwise certificate
`forall params, @frozen params <-> @live params`, and the conversion of the live
endpoint with its witness; zero-assumption rejection is unchanged.

Not supported (fail closed, open debt rather than migration): dependent Variable
scaffolds, `Variables`/`Hypothesis`/`Context`/`Let`/`Fixpoint` and other Section
commands before the endpoint, nested Sections, frozen Section companions,
Section-parametric chains, and public-core source indexing.

Recorded design corrections during implementation: two commands on one line
(`Check nat. Section S.`) are not a wrapped scope, exactly as in the reviewed
nullary scanner, so r1 section 8's example of it as a wrapped-scope negative was
wrong and is a positive fixture; `Fixpoint` is excluded from the Section scaffold
whitelist because mutual `with` cannot be told apart from `match ... with` lexically.

Correction C5 (after Lancelot's independent source review, findings F1-F12):
F1-F7 add the design-listed fixtures that were missing (provider-restricted
acceptance and the ambient-loader conservative fallback; companion reach only at
a snapshot commit; propagation of unrelated discovery errors at a snapshot commit;
the GIT_REPLACE_REF_BASE/GIT_GRAFT_FILE guards; unlisted-source and remapped-
namespace ownership at both pins; corpus-name exclusion at the baseline and at
snapshot commits; global-form and extra-implicit snapshot kernel negatives; and
the remaining frozen-copy/witness placements). F9: the conversion line names
`Corelib.Init.Logic.eq_refl` and `Corelib.Init.Logic.eq`, so a shadowing prelude
(MathComp's eqtype `eq_refl`) can neither break it nor change its binding. F11:
kernel types follow a token grammar (fully qualified names, Prop/Set/Type,
parentheses, the arrow and application); isolated punctuation, digits, holes and
scopes are rejected. The parametric ownership comparison after `project_module`
cannot fail by itself (the call raises or returns exactly the qualified module),
so its comparison-only mutant is equivalent; removing the call is detected.

Limitations kept (fail closed, not migration): F10, snapshot-commit reach runs
the family's current sources at that commit, so a source or project context
missing or malformed there rejects the snapshot (only "must be reached" is
absorbed, because an unreached endpoint cannot make its companions reach); later
families with new source files need a design decision before using snapshots.
F12, substitution values are checked against Section variables, not against
same-Section declaration short names; such a value cannot denote the live Section
declaration inside the frozen module, and its correspondence remains the
responsibility of the compiled certificate and the independent closure review,
unchanged by this tooling (frozen Section companions stay unsupported).

Author evidence (fixtures, the 131 preserved tests, kernel suite, mutation,
78-report parity and the real-data dry run) is recorded under
`coordination/evidence/psec-tool-author/`; review outcomes are added by the
reviewers, not by this record.
