# ClassicalLemmas source ownership and routing review

Implementer: `matching_scope`. Independent reviewer: `family_scope`.
Reviewed source: `ff6b3f60bbae1db77005d2e0453c611a9c291936`.
Independent code/test review: **PASS**, 2026-10-03.
Integration acceptance requires terminal `make mutation` on that exact source;
the implementer's unchanged run is tracked in BOARD.md and external evidence.

The shared public-source policy enrolls build-listed ClassicalLemmas library
modules and their public intermediaries. Original/current project ownership,
regular contained source paths, complete reaching-row coverage and existing
exclusions remain checked. Registered ClassicalLemmas theorems use the real
package owner and fresh transitive source build. Classical source/project changes
select classical and Packing builds plus migration/kernel-report gates.

Independent validation passed 20 registry, 56 report/kernel and 34 build/routing
tests, plus inventory/routing validators. Completeness negatives omit either of
two intermediaries or rows. A real-namespace fixture rejects an invalid transitive
GTBase proof despite preserved source time and a stale clean object. Three
independent rollback probes reject removal of indexing, ownership or routing.

Prepared on C12 `91a3c6eb0af6f432829320acaf195ce6d0314d07`: all eight tooling
files match the reviewed source; 2,539 predecessor files, including every Rocq
file, project and 28 frozen specs, remain exact. All 28 summaries and shared
metadata regenerate without byte drift; `make audit` passes. No mathematical
source, statement or dependency declaration changes. A future A10 base import
still needs its own project/root dependency update. Family-specific Section and
compiled closure checks remain necessary beyond lexical discovery.

Reproducible logs and preservation checks: VM coordination evidence directories
`Classical-source-tooling-review-by-family-scope/` and
`Classical-tooling-integration/`. The terminal mutation result is recorded there
without changing this immutable prepared pin.
