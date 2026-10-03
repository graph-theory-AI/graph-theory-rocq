# Review: explicitly pinned public migration sources

Implementer: matching_scope. Independent reviewer: path_review.
Reviewed commit: `2f15093866a15d349677db7ff58ee420dbc1b6fe`.
Coordinator final source review: approved, 2026-10-03.

The optional repository_sources descriptor keeps source_definitions authoritative
and pins a regular Git blob, full commit and declaration hash. Original and
current build membership, declaration identity and namespace ownership are
checked separately; current compatibility aliases may differ from their originals.
No public declaration is added to the conjecture inventory or debt counts.
Missing inventory sources cannot silently use this descriptor as a fallback.

Reports retain ordinary frozen-source, statement, corpus-status, exact-iff and
assumptions checks. Public intermediate declarations and every reached corpus
row must be accounted for. The implementation rejects duplicate family ownership,
path aliases, nonregular blobs, wrong hashes/object kinds, local or nested module
sources and ambiguous/hidden project ownership overrides. Mutation workspace
copies retain explicit source packages even without fidelity fragments.

Independent checks passed 19 registry tests, 40 report tests including fresh
kernel fixtures, and the inventory self-test. The fixture spans a public source,
a foundation intermediary and two corpus rows in separate packages; omitting
any of them is rejected, as is a closed theorem with an extra False guard.
The real C6 discovery independently reaches seven rows and five intermediaries,
including X229 through the existing public foundation predicate.

The coordinator read all seven files and tests. On the combined B6 integration,
all seven tooling files remain byte-exact; focused tests and audit pass all
fifteen current family reports. Required mutation execution and later integration
acceptance are tracked against the immutable source pin in BOARD.md and
MASTER_JOURNAL.md; this source review does not replace those gates.
Detailed evidence and reproducible commands are in the VM coordination area,
`evidence/repository-sources-tooling/`.

Lexical discovery does not elaborate notation, constructors, module aliases or
Section contexts. Independent family review and compiled dependency probes
remain mandatory. No family statement or Rocq source is changed here.

Required mutation execution at the unchanged source commit completed successfully:
all twelve canaries accepted their pristine baselines and were rejected for their
intended mutations, followed by all forty report/kernel tests passing. Combined
integration regeneration changed no generated artifact or family report.
