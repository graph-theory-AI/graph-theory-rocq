# meta

Repo-wide roadmap + the validated corpus manifest (the source of truth):
- `OPG_FULL_FORMALIZATION_PLAN.md` — the plan (v4).
- `opg_corpus_manifest.json` — 227 rows, 142 core / 85 deferred (reconciling).
- `build_opg_manifest.py` — deterministic generator + pinned-input invariant gate
  (`python3 meta/build_opg_manifest.py --check`; use `--write` explicitly to refresh).
- `milestone_rows.py` — per-(phase,repo) row loader for the driver.
- `area_milestone_pipeline.workflow.js` — the per-milestone QA driver.
