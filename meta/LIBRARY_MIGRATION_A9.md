# Library Migration A9: Cut Sizes

Batch A family A9, on the private baseline `9de20ca` (A8 `ed9735b` plus main `54be55e`, for C8's
`monochromatic_on`). Registry `meta/library_primitives/cut-size.json`; spec, hashes and per-row
certificates: `meta/migration_reports/cut_size.{spec.json,md}`; API contracts are in the Rocq doc comments.

- **Contract.** There are two classes. X76's and X78's cut sizes (edges of `E(G)` meeting `A` and its complement)
  convert to `GTBase.common.cut_size`. X209 counts the non-monochromatic members of an arbitrary supplied
  finite family under a supplied colouring, now `GTBase.monochromatic.non_monochromatic_count`; its
  cut-edge test equals C8's `~~ monochromatic_on`. No uniformity, nonemptiness or palette premise is added.
- **Rows.** X76, X78 and X209 (through `is_max_r_cut`, `scaled_excess` and `is_min_scaled_excess`) are frozen
  verbatim at `9de20ca`. Guards, natural subtraction, quantifier order and statuses are unchanged.
- **History.** The complete X76/X78 rows are pre-M1. They use the `061154c` cut bodies over M1's frozen
  edge set, A7's pre-M1 counts and A5's frozen containment. A5's and A7's X76/X78 snapshots are
  documented reciprocally.
- **Defect, preserved.** `x209_is_min_scaled_excess` binds a fresh `T'`, but `E'` ranges over families on
  the outer `T`, so `T'` is unused. The frozen chain keeps it verbatim; it is not repaired.
- **Reproduction.** Build the 15 packages. Run `python3 meta/migration_report.py cut_size --check --kernel`
  and the milestones X76, X78 and X209. Kernel probes, including the exact `T'`-free reading of the defect,
  are in `coordination/evidence/A9-cut_size/`.
