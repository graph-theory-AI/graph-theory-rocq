# Library Migration A11: Minimum-Degree Lower Bounds

Batch A family A11, on A10 `9abf440` plus the separately reviewed registry-namespace tooling fix (cherry-picked
from `5977389`). Registry `meta/library_primitives/minimum-degree-at-least.json`; spec, hashes and per-row
certificates: `meta/migration_reports/min_degree_at_least.{spec.json,md}`; API contracts are in the Rocq doc
comments.

- **Contract.** `GTBase.base.min_degree_at_least G d := forall v : G, d <= #|N(v)|`, beside `Delta` and
  `regular`, is a universal lower bound, not an attained minimum: `K_0` and an empty induced subgraph satisfy
  every bound, and no nonemptiness is added. Ten local copies convert to it. X13's induced adapter is
  `min_degree_at_least (induced S) d` on the supplied `S`, and XE1's no-isolated-vertices is the bound 1.
- **API.** Zero bound, antitonicity, regularity, the bound 1 as no isolated vertex, `K_0`, complete and
  complete bipartite graphs and k-connectivity (upstream degree lemmas), isomorphism transport, and, given a
  vertex, the bounds by `Delta` and by the order. The public client adds `K_1`/`K_2`, empty and singleton
  induced subgraphs, and the non-inheritance of a bound by induced subgraphs.
- **Rows.** The 17 rows (X203, Cycle XE2 #752, X13 ×2, X30, XE1 #85/#545/#566/#567/#568, Extremal XE2 #570,
  X38, X74, X211, X135, X47, X48) and the two chains are frozen verbatim at `9abf440`. X203's empty-graph
  defect and blocked status are kept.
- **Complete rows.** #85 composes the frozen bound with A5's frozen containment. #545/#566/#567/#568/#570
  compose the frozen no-isolated bound with A7's frozen count and sparse-set chain, A6's frozen Ramsey number
  and B4's frozen h5. X38 composes A10's frozen raw incidence count and degree classes with the frozen bound,
  M1 alias live as in A10 (no pre-M1 claim). Each converts to the earlier family's certificate. Earlier
  snapshots are documented reciprocally; no older frozen body changes.
- **Distinct.** Exact attained minima (Extremal XE2, X227), subcubic and cubic contracts, scaled bounds
  (X30 logarithmic, D7), directed degeneracy, hypergraph coverage and restricted-set upper bounds stay distinct.
- **Reproduction.** Build the packages, the Digraph targets `chi_bounded`/`classic_core` and the atlas. Run
  `python3 meta/migration_report.py min_degree_at_least --check --kernel` and the milestones of the touched
  modules. Kernel probes and closures are in `coordination/evidence/A11-min_degree_at_least/`.
