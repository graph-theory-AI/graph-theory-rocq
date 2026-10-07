# Library Migration A24: Petersen Graph

Batch A family A24, on the fixed A23 pin `ba3c748` (no private union). Registry
`meta/library_primitives/petersen.json`; spec, hashes and per-row certificates
`meta/migration_reports/petersen.{spec.json,md}`; fidelity `meta/foundation_fidelity/petersen.json`; full evidence
`coordination/evidence/A24-petersen/`.

- **Contract.** `GTBase.petersen` names two views:
  - `petersen_ord`: D1's literal ordered table of 15 pairs, the natural relation `petersen_conn` (false outside 0..9
    and on equal ends) and the ordinal graph on `'I_10`;
  - `petersen_kneser`: the exact two-subset carrier `kneser52V` of `'I_5`, with disjointness.

  `petersen_ord_kneser_diso` is the explicit isomorphism, from grounding_D1's labelling table, now public. D1's
  `pedges`/`pconn`/`padj`/`petersen` and U10's `petersenV`/`padj`/`petersen` unfold to these views. U10's
  `Pedge`/`psupp`/`Padj` stay convertible. Graphs and constructor proofs are related by pointwise adjacency and
  identity isomorphisms, never by proof-field equality; the two carriers are not convertible.
- **Rows.** Frozen verbatim at `ba3c748`: the seven sources, the four constructor proofs with their scripts,
  `Pedge`/`psupp`/`Padj`, and the three complete Props:
  - D1 4-flow;
  - U10 Petersen colouring;
  - the explicitly non-corpus BF-cover hypothesis, which stays an explicit hypothesis.
- **Complete row.** The A13+A24 colouring Original at A13's `58f2862`, over the frozen edge interface and A13's frozen
  loopless degree-three `cubic_bridgeless`. Four whole iffs and twenty mappings in all.
- **Consumers.** grounding_D1 (one unfold; the labelling block becomes type-identical wrappers), grounding_U10 (three
  unfolds) and implications_U6 (one unfold) adapt explicitly. Everything else in the 13-file closure (304 old headers,
  478 declarations) is type-identical, including Atlas implications_A1's 15 headers.
- **History.** A13's colouring snapshot keeps the live edge interface; A24's copy keeps A13's live `cubic_bridgeless`.
  Both carry reciprocal notes.
- **Reproduction.** Build the packages. Run `python3 meta/migration_report.py petersen --check --kernel`, the
  cycle-theory milestones D1/U10/U6/X184/X228 and the Atlas probe in the evidence.
