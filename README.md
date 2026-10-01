# graph-theory-rocq

![corpus-status](https://github.com/LLM4Rocq/graph-theory-rocq/actions/workflows/corpus-status.yml/badge.svg)
**OpenProblemGarden corpus: statement-complete** — 227/227 attempted · **208 done** (axiom-free
`Definition <name>_statement : Prop`, `Print Assumptions` clean) · **12 partial** · **7 blocked**.
Release: **`opg-v1.0.1-227-attempted`** (release-time counts 212/8/7; 4 crossing-number rows were
since downgraded to partial — `meta/CORPUS_STATUS.md` is the canonical living report). v1
completion report: [`meta/OPG_FULL_FORMALIZATION_PLAN.md`](meta/OPG_FULL_FORMALIZATION_PLAN.md).

**v2 corpus (growing)** — every conjecture source of the upstream `graph-conjectures` repo:
**1,745 rows tracked** (762 arXiv + 277 erdősproblems + 138 attack-engine derived + 568
studies-slice) · **1,629 non-alias statement legs**, with the rest recorded as aliases ·
**331 done · 11 partial · 36 blocked · 1,251 todo** (waves X1–X210: directed reconciliation +
directed/χ-boundedness/extremal/structural/topological/cycle/minor/misc/packing/quasi-kernel/reconstruction/deck/nonrepetitive/normal/treewidth/total-list/linear-arboricity/coarse-Menger/coarse-Erdős–Pósa/tree-decomposition/hedgehog-and-3-uniform-Ramsey/Erdős–Hajnal-pairs/dijoin-inversion/directed-Gyárfás–Sumner/fractional-and-distance-colouring/induced-subdivision-complexity authored statements — every one
axiom-free with a faithfulness audit recorded in the manifest; blocked rows need a foundation deliberately out of scope, e.g. merge-width, random-lift probability, bounded-expansion sparsity, fixed-surface clustered colouring, graphon forcing, asymptotic dimension, computation-model, random-graph, DP-colouring, Kempe-class, polyhedral extension-complexity, metric-line/bridge-generation, poset-dimension, flow, thin-overlay, Ramsey-nice, cops-and-robbers, hypergraph-cut, or conflict-colouring layers). Plan:
[`meta/V2_FULL_CORPUS_PLAN.md`](meta/V2_FULL_CORPUS_PLAN.md); live counts in
[`meta/CORPUS_STATUS.md`](meta/CORPUS_STATUS.md).

A monorepo of Rocq/MathComp **graph-theory** libraries. Each `<area>-theory/` subdirectory is a
separate Rocq build unit over the shared `GTBase` namespace; opam metadata currently covers GTBase
and the Digraph compatibility packages, while the remaining area units are built from this
monorepo. Each area states open conjectures and gains their proofs over time.

Built on [`coq-graph-theory`](https://github.com/rocq-community/graph-theory) (undirected) and
MathComp. The roadmap + the validated 227-problem manifest live in **`meta/`**. Verify the
statement-complete claim with `make audit` (toolchain-free) or the full `make gate` (Coq builds).

The repository contains no local `Axiom` or `Admitted` declarations. The Digraph subsystem does
intentionally import `mathcomp-classical`; the gates report assumptions theorem by theorem rather
than claiming that every public result is constructive.

## Checked formal resolutions

Three new Rocq formalizations prove the list Ramsey equality, the chromatic/cochromatic gap family, and the nine-vertex color-avoiding tournament construction. A fourth result connects the existing Question 5.9 counterexample family to its exact statement. All four have closed assumptions.

See the [proof overview](meta/formalizations/README.md), [development journal](meta/formalizations/JOURNAL.md), and [resolution registry](meta/FORMAL_RESOLUTIONS.md). Run `ROCQ_OPAM_SWITCH=rocq-tools make resolutions` to build and check them with the compatible development switch.

## Packages
| package | namespace | core | deferred |
|---|---|---:|---:|
| `chromatic-theory/` | `Chromatic` | 32 | 0 |
| `digraph-theory/` | `Digraph` | 32 | 0 |
| `packing-theory/` | `Packing` | 15 | 0 |
| `cycle-theory/` | `Cycle` | 14 | 15 |
| `graph-theory-misc/` | `GTMisc` | 12 | 5 |
| `homomorphism-theory/` | `Hom` | 10 | 0 |
| `hamiltonicity-theory/` | `Hamilton` | 9 | 0 |
| `minor-theory/` | `Minor` | 6 | 0 |
| `reconstruction-theory/` | `Reconstruction` | 4 | 0 |
| `hypergraph-theory/` | `Hypergraph` | 4 | 0 |
| `topological-graph-theory/` | `Topological` | 4 | 14 |
| `extremal-graph-theory/` | `Extremal` | 0 | 32 |
| `infinite-graph-theory/` | `Infinite` | 0 | 14 |
| `spectral-graph-theory/` | `Spectral` | 0 | 5 |

Σ = 142 core + 85 deferred = 227.

## Layout
- `base/` — `coq-graph-theory-base`: the single owner of cross-area primitives (interop façade,
  homomorphism, products, list-χ, line/total-graph, Δ).
- `<area>-theory/` — the area packages (each: foundations/core/invariants/constructions/conjectures/applications).
- `meta/` — the v1 completion report + roadmap (`OPG_FULL_FORMALIZATION_PLAN.md`), the validated 227-row
  manifest + leg-state overlay, the federated dependency graph (`dependency_graph.json`), the status report
  (`CORPUS_STATUS.md`), and the gates (`check_milestone.py`, `report_corpus_status.py`, `build_edge_graph.py`).
- `atlas/`, `blueprint/` — *scaffolds* reserved for later extraction of the cross-area edge atlas and the
  shared dev tooling; both currently live in `meta/` (see the stubs' `Status: scaffold`).

`digraph-theory/` was absorbed from the standalone repo via a subtree merge (history preserved).
See `meta/OPG_FULL_FORMALIZATION_PLAN.md` §A / §A.1.
