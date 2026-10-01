# P1 hardening implementation (started 2026-07-18)

This is the implementation record for `meta/EXPANSION_PLAN.md` phase P1. The
policy is prospective: X1-X210 remain the audited legacy baseline; X211 and
later are rejected unless they satisfy the hardened acceptance contract.

## Implemented in tranche 1

- `faithfulness_policy.json` fixes the prospective boundary at X211.
- `faithfulness_lint.py` reports the legacy suspicion backlog during `make
  audit` and is a hard, allowlist-backed gate for X211+.
- `foundation_fidelity.json` seeds primitive-level FAITHFUL/LIGHTWEIGHT/BROKEN
  verdicts from the blocked-retargeting audit. `foundation_fidelity.py --check`
  validates every registered declaration and evidence name; the generated
  corpus report prints the watch list.
- `build_v2_manifest.py --check` now has two honest modes: full regeneration
  against the pinned sibling checkout, or a source-less local replay over the
  committed pinned snapshot. Both check every overlay leg and every wave's
  routing/provenance. `make gate` requires the full upstream mode.
- `report_corpus_status.py --check` proves LANDED coverage of every v2 wave,
  every assigned v2 manifest cell, and every OPG row (including subbatches).
- `check_milestone.py` requires X211+ done rows to provide typed certificate
  objects for inhabited hypotheses, a non-trivial conclusion, and helper sanity.
  Each object names a `Prop` claim, a distinct proof theorem, and explicit
  row/helper references. The gate checks `claim : Prop`, `theorem : claim`, the
  reference anchors, the independent faithfulness verdict, and Print Assumptions.
- `vacuity_probe.py` specializes supported leading quantifiers at 0/1, the
  empty graph, and labelled complete graphs through K6. Its self-test has a
  separate specialization-recall fixture.
- `faithfulness_mutation.py` now includes v2 canaries for the X138 quantifier
  swap and X125 fixed-ratio-for-whp regression.
- CI has a pinned MathComp/Rocq container job that maps changed conjecture files
  and wave metadata to milestone checks and runs active probes for X211+.

## Coverage defect found while wiring LANDED

The new completeness assertion exposed nine OPG rows that were not in any
`check_milestone` invocation. Seven blocked rows lived only in legacy aggregate
files. Two partial infinite Hamilton rows had overlay legs but no formal
constants at all. `D3legacy`, `D4legacy`, and `D6legacy` now cover those rows;
the Hamilton rows have explicit spanning-double-ray proxy statements and remain
honestly partial. Seven unsupported grounding legs were changed from `done` to
`blocked` because no grounding artifact existed.

## Still open in P1

- Exercise the prospective grounding contract on the first real X211 wave and
  add a mutation fixture that drops each required certificate class.
- Add canaries for the remaining defect-taxonomy classes where a mechanical
  detector can have useful recall.
- Vendor the two upstream corpus inputs, or publish immutable source archives;
  the source-less v2 replay pins hashes and local derivations but cannot rebuild
  source-owned fields from an empty checkout.
- Validate the new container job on GitHub and pin the container by digest once
  the first run records it.
