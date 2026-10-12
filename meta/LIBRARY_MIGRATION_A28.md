# Library Migration A28: Disjoint Unions

Batch A family A28, on Arthur's A27 pin `ec5fb25`. Registry `meta/library_primitives/disjoint-union.json`; spec,
hashes and per-row certificates `meta/migration_reports/disjoint_union.{spec.json,md}`; fidelity
`meta/foundation_fidelity/disjoint-union.json`; full evidence `coordination/evidence/A28-disjoint-union/`
(discovery and approved scope: `coordination/evidence/A28-disjoint-union-discovery/`).

- **Contract.** Two representations, one family:
  - simple graphs: upstream `GraphTheory.core.sgraph.sjoin`/`join_rel` (despite the name, the disjoint union on
    `G + H`, nothing across), reused without a new canonical;
  - digraphs: the public `Digraph.constructions.digraph_sum D1 D2` on `D1 + D2` with `Finite.on` and a `HasArc`
    instance, arcs inside each summand and none across. API: the arc view, both injection and both cross-arc equations,
    `#|D1| + #|D2|` vertices. Loops, asymmetric arcs and empty summands are kept; no conjecture import, no guard.
- **Sources.** X66's `x66_disjoint_union_rel`/`x66_disjoint_union` alias `join_rel`/`sjoin`; its two constructor
  proofs are one-line uses of the upstream ones, related by `eq_diso`, never by proof-field equality. X2's
  `x2_disjoint_union`/`x2_disjoint_union_rel` alias `digraph_sum`/`digraph_sum_rel`, keeping the Section's packaging.
- **Rows.** Frozen verbatim at `ec5fb25`: the four sources, both X66 proofs with their scripts, X2's whole
  `Section DisjointUnion` (alias, anonymous `Finite`/`HasArc` instances, relation), and two complete rows:
  - X66: both tree guards and both goodness premises, then goodness of the union;
  - X2: both summands delta-plus-Maderian, then the union.

  The complete X2 Original at B1's baseline `9e03072` joins the frozen sum with B1's raw Maderian chain (nonempty host,
  minimum out-degree, full subdivision model); B1's five raw providers are borrowed. Fourteen mappings, three whole iffs.
- **History.** B1's `X2UnionLegacy.statement` keeps the live sum (documented here); A28's per-row X2 copy keeps
  B1/B2's live chain (reciprocal notes in both specs).
- **Consumers.** implications_X66 (`x66_union_forest`, gc:e036), the X2 grounding/implication files, X16, X17, X52,
  X90, X107, `directed_kneser_nonexistence` and the B1/B2 certificates recompile unchanged.
- **Kept distinct.** The joins `heroes.djoin` and X122's `x122_dijoin` (left-to-right arcs added).
- **Reproduction.** Build the packages and the Digraph closure targets, then run
  `python3 meta/migration_report.py disjoint_union --check --kernel` (and `path_vertices`, `internal_vertices`), the
  milestones X66 (chromatic-theory) and X2 (digraph-theory), and the kernel probes.
