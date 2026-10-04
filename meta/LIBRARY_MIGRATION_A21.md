# A21: Complete and anticomplete supplied vertex-set pairs

The initial reviewed worker is `1b8126b` on `229f295`; the combined preparation starts on B23 `172629c`.
API: `GTBase.set_pairs`; ownership/fidelity: `meta/library_primitives/set-pair.json` and
`meta/foundation_fidelity/set-pair.json`; exact mappings: `meta/migration_reports/set_pairs.spec.json`.

Three contracts remain distinct: raw anticompleteness is upstream `~~ neighbor A B`; disjoint
anticompleteness additionally requires `[disjoint A & B]`; cross completeness requires every cross
pair adjacent. On an sgraph cross completeness forces disjointness. No nonempty or unequal-vertex
guard is added. Complement duality requires disjoint parts. X94 heterogeneous pairs, X67 interior
wrappers, one-set stability and whole-graph `complete_bipartite` remain separate contracts.

The public client covers empty parts/K0, an overlapping K1 singleton, K2 and edgeless pairs, swaps,
restrictions, a complete pair with a nonclique part, and the guarded complement duality.
Ten sources, five current chains and nine complete current rows retain all quantifiers, guards,
bounds and statuses, including X58's defect, X41's sublinear side and X11's complete right alternative.

There are 41 frozen objects and 15 whole-row iffs: nine current rows and six complete Originals.
X57/X58/X41 retain A1's raw induced-freeness; X11 composes B1 path support and B5 set paths/right
alternative. Added C12+A21 D2ram/X144 Originals freeze both perfection and pair contracts. D2ram
keeps the full G OR compl G disjunction on the same parts; X144 keeps disjointness, both nonempty
parts and complete OR anticomplete. Old snapshots, proof bodies and reciprocal history remain intact.

Four existing grounding proofs use the reviewed pair views with unchanged types. The verified
gc:e076 X58-to-X223 implication is unchanged; gc:e077 remains a candidate. Newer C12 perfection,
A7 edge counts, A20 stability and B22/B23 path/cycle declarations are preserved in precise unions.
Only A8's obsolete X223 anticomplete exclusion is removed; X76/X78 remain.

Initial source/independent evidence is in `coordination/evidence/A21-set-pairs/` and
`A21-review-by-matching-scope/`. Combined evidence belongs to `A21-combined-by-path-review/`.
Both new full-row proofs are independently approved at mathematical pin b16a8e2; the coordinator
reviewed all15 whole iff. See meta/migration_reviews/set_pairs.md. Final cumulative/main acceptance
remains separate. Reproduce the family report with `python3 meta/migration_report.py
set_pairs --check --kernel`; combined normal routes include Extremal D2ram and GTMisc X144.
