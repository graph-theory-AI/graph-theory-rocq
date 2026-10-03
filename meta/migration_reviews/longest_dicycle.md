# Independent review: longest directed cycles (B14)

Marcol's exact source `ed08916ff19c9c35095358d1eb835b23a484dbb5` was independently reviewed by matching_scope and personally reviewed by the coordinator. Both approve the public API/client, X2 adapter and complete statement iff. Detailed evidence is `coordination/evidence/B14-review-by-matching-scope.md` and its directory; the reviewed source/specification/fidelity remain exact at integration.

`Digraph.foundations.longest_cycles.longest_dicycle` maximizes length among every `dicycle` of the supplied digraph. The existing directed predicate admits loops and digons, excludes empty/repeated sequences, and has no added connectivity, orientation or inhabitance guard. Existence is conditional on an existing cycle. Converse reversal is general; reversal in the same graph keeps its explicit symmetry premise. This remains distinct from B13's genuine undirected cycles.

Independent checks passed:53 freshly forced modules in two packages, including all12 X2 import consumers;32 exact types covering all25 API lemmas and the whole iff;75 closed assumptions;six strict frozen/live/public closures; family kernel57 and all26 source reports. Protected2,529 other files,84 older migration modules and25 frozen arrays are unchanged. Only X2's new Require and qualified alias body differ; all statement docs, other rows and proof scripts are preserved.

The integration preserves newer family source/history and all existing B13 review metadata, removes only X2's migrated distinct-variant entry and appends the reviewed directed-contract note. Root's normal unscoped Digraph X2 and cumulative gates remain separately required; no whole-Digraph/scoped-gate acceptance is inferred from these focused tests.

Use `python3 meta/migration_report.py longest_dicycle --write` to regenerate the compact report, or `--details /tmp/longest-dicycle-details` for full generated evidence. The family registry/specification and public Rocq documentation carry the contracts and frozen mappings.
