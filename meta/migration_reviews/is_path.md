# Independent review: is_path (B7)

Implementer: marcol. Independent reviewer: coordinator helper matching_scope
(protocol step 10). Exact reviewed commit:
`fa3f5f4333565c916ad92c37007688efac5fadd2`, source pin
`cd75d70bfd6254af0fb3f0f3d7d6f1010d3bb945`, baseline
`632e0b124089c15c11fc2e801435479a9c741c5c`.
Date: 2026-10-03. Verdict: approved; no remaining semantic or snapshot finding.

Read all public API/client proofs, both complete certificate modules, live
source substitutions, registry/fidelity and specifications. The sequence
predicate keeps arbitrary relType, uniqueness and consecutive adjacency, with
empty true; the explicit nonempty bridge to B6 remains a separate contract.
The multigraph edge-set predicate keeps nonempty, incident connectivity,
acyclicity and arc-end degree at most two, with no extra graph hypotheses.
Loops and parallel edges retain their behaviour. Pinned MathComp sorted and
GraphTheory pathp/upath definitions agree with the proved sequence bridge.

Both full rows and their complete reaching helper chains are frozen. U3 keeps
positive vertex count, connectivity, three longest sequences and their common
vertex. U6 keeps positive vertices and edges, simple_mgraph, mconnected, the
full edge partition and `(n+1)%/2` bound. All six compatibility certificates
have the exact full types and are conversions. Earlier walks_paths declarations
and proofs, both grounding files and connectivity are unchanged. Existing row
texts, documentation and statuses remain intact.

Independent pinned-image verification freshly force-built 20 local source
modules (base 11, Cycle 6, Hom 3), including both public-only clients, both
certificate modules and both grounding files. Six exact compatibility types,
six public Section/type checks and an explicit old/new acyclicity equality pass.
All 51 assumption checks are closed: 31 registered API/compatibility theorems,
11 client lemmas, eight unchanged grounding consumers and the acyclicity equality.
Four strict compiled closures exclude both live helpers/chains and canonical
predicates from the frozen rows; the live rows reach their expected canonical.
The family kernel report passes 86/86; B6's existing source report passes 138/138.
The final metadata-only correction points each semantic class to its actual
legacy-equivalence certificate while retaining the API registrations.

The coordinator separately read and approved both complete row iff statements
and the final metadata correction. Evidence is external:
`coordination/evidence/B7-review-by-matching-scope/README.md` and adjacent logs,
plus `coordination/evidence/review-B7-coordinator-final.md`.

Prepared one-family integration has reviewed C6 merge
`d0c1d329ba561a92de0f166592a1761eb8b26a77` as first parent. It preserves exact
B7 Rocq/spec/fidelity bytes, all C6/B6 complete Originals and reciprocal notes,
and earlier review fields. B6 metadata combines the existing history summary
with B7's narrative and removes only the two now-migrated distinct variants.
Project registrations retain all prior entries and append the reviewed B7
sources. Generated metadata and compact reports are regenerated; cumulative
integration proof gates remain separate from this preparation audit.

Preparation regeneration and `make audit` pass, including all eighteen source
reports: B7 86/86, C6 242/242, B6 175/175 (all 23 frozen objects retained),
and A5 526/526. Byte checks preserve ten reviewed source/spec/fidelity files and
2,023 predecessor files. Manifest, overlays and edge graph regenerate without
drift. Only the helper inventory and foundation-fidelity status summary change
among shared generated files. No package proof build was rerun in preparation.
