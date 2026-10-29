# graph-theory-rocq

![corpus-status](https://github.com/LLM4Rocq/graph-theory-rocq/actions/workflows/corpus-status.yml/badge.svg)
**OpenProblemGarden corpus: statement-complete** — 227/227 attempted · **205 done** (axiom-free
`Definition <name>_statement : Prop`, `Print Assumptions` clean) · **14 partial** · **8 blocked**.
Release: **`opg-v1.0.1-227-attempted`** (release-time counts 212/8/7; six rows were since
downgraded to partial: four crossing-number rows, then `crossing_sequences` and
`what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian`, whose own
notes call them partial — `meta/CORPUS_STATUS.md` is the canonical living report). v1
completion report: [`meta/OPG_FULL_FORMALIZATION_PLAN.md`](meta/OPG_FULL_FORMALIZATION_PLAN.md).

**v2 corpus (growing)** — every conjecture source of the upstream `graph-conjectures` repo:
**1,790 rows tracked** (768 arXiv + 277 erdősproblems + 138 attack-engine derived + 568
studies-slice + 38 Bondy–Murty Appendix A `bm-NNN` + 1 curated `others`; corpus pinned to
graph-conjectures `b72c585`) · ~1,100 statement-owing after triage, the rest parked/alias/edge-anchor
with documented dispositions · **542 statements done · 11 partial · 40 blocked · 1,080 todo** over the
1,673 non-alias rows (waves X1–X229: directed reconciliation +
directed/χ-boundedness/extremal/structural/topological/cycle/minor/misc/packing/quasi-kernel/reconstruction/deck/nonrepetitive/normal/treewidth/total-list/linear-arboricity/coarse-Menger/coarse-Erdős–Pósa/tree-decomposition/hedgehog-and-3-uniform-Ramsey/Erdős–Hajnal-pairs/dijoin-inversion/directed-Gyárfás–Sumner/fractional-and-distance-colouring/induced-subdivision-complexity/Bondy–Murty-Appendix-A/cops-and-robbers/χ-boundedness/list-colouring-on-surfaces/treewidth-and-twin-width/dichromatic-and-tournaments/Sidorenko-and-Ramsey/hypergraph-Turán/η-boundedness/hat-guessing/flows-and-crossings authored statements — every one
axiom-free with a faithfulness audit recorded in the manifest; blocked rows need a foundation deliberately out of scope, e.g. merge-width, random-lift probability, bounded-expansion sparsity, fixed-surface clustered colouring, graphon forcing, asymptotic dimension, computation-model, random-graph, DP-colouring, Kempe-class, polyhedral extension-complexity, metric-line/bridge-generation, poset-dimension, flow, thin-overlay, Ramsey-nice, cops-and-robbers, hypergraph-cut, or conflict-colouring layers). Plan:
[`meta/V2_FULL_CORPUS_PLAN.md`](meta/V2_FULL_CORPUS_PLAN.md); live counts in
[`meta/CORPUS_STATUS.md`](meta/CORPUS_STATUS.md).

**Latest update (2026-09-23/24, branch `conjecture-relations`)** — re-synchronised the Rocq
statements with the graph-conjectures corpus at commit `b72c585` (merged into its main by PR #18 on 2026-09-23): 38 Bondy–Murty
Appendix A rows and the curated `others` row joined the manifest, every one of the 741
conjecture statements now carries a doc block with its corpus row, site and review links, an
English back-translation of the Rocq body and its non-standard definitions, a shared vocabulary
layer was added in `base/theories/common.v`, the 225 corpus relations were mirrored and
cross-checked against the machine-verified edge graph, and waves X211–X229 authored 90 new
statements (13 blocked with a stated reason) under a two-reader faithfulness protocol with
grounding lemmas, vacuity probes and mutation canaries. The audits uncovered and repaired six
foundation-level defects (directed-walk bridges, loop degree counted once, torus encoded as
Euler genus two, missing connectivity and degree guards, uncounted isolated vertices in the
surface layer); every gate (`make all`, `make audit`, `make mutation`, `make gate`, a full
vacuity sweep) is green. **Total cost: 10,832,396 tokens** metered over 42 Claude Opus 5
sub-agents, plus the orchestrating Claude session (not metered, of the order of one million
tokens).

**Implication programme (2026-09-24, branch `conjecture-relations`)** — every implication relation
between formalized conjectures (the corpus's `implies`/`equivalent_to` relations plus the ones this
repository identified) now has a machine-checked disposition: **66 verified** (Qed, `Print
Assumptions` closed under the global context; 20 before), **13 conditional** (Qed under one of 10
registered, second-read external theorems such as Tutte's flow theorems, Jaeger's CDC reductions
or Dujmović–Morin–Wood's layered treewidth; `meta/external_theorems.json`), **33 refuted
directions** documented with their reason, and 32 candidates blocked on a named ingredient.
Cross-package edges live in the new `atlas/` package; the `edges` legs are derived from the edge
graph (`meta/sync_edge_legs.py`) and every proved edge is re-checked for its exact type and
axiom-freedom by `meta/check_edges.py` in `make gate`. The proofs exposed and repaired seven
unfaithful statements (empty-digraph guards, Behzad's row, the multibounding quantifier order,
the vacuous fractional-Hadwiger row). **Cost: 7,242,533 tokens** metered over 26 Claude Opus 5
sub-agents, plus the orchestrating session (not metered).

A monorepo of Rocq/MathComp **graph-theory** libraries — the math-comp model (one repo,
many independently-installable opam packages). Each `<area>-theory/` subdir states the open
conjectures of one area of graph theory (and gains their proofs over time).

Built on [`coq-graph-theory`](https://github.com/rocq-community/graph-theory) (undirected) and
MathComp. The roadmap + the validated 227-problem manifest live in **`meta/`**. Verify the
statement-complete claim with `make audit` (toolchain-free) or the full `make gate` (Coq builds).

## Building

The tested environment is **Rocq core 9.2.0, rocq-stdlib 9.1.0, OCaml 5.3.0,
MathComp 2.6.0, classical 1.16.0 and Hierarchy Builder 1.10.3**, with the unreleased
[`coq-graph-theory`](https://github.com/rocq-community/graph-theory) commit
`322e352b72c4ca3f153e5f80123c5020a0d40620`. This release makes **no Rocq 9.1 support claim**.
See the [accepted release receipt](meta/releases/ROCQ92_ACCEPTED_2026-10-23.md) and
[image recipe and full pin inventory](environment/rocq92/README.md).

### 1. One-time toolchain setup

For a native development switch, use the locked package versions:

```sh
opam switch create digraph ocaml-base-compiler.5.3.0
eval $(opam env --switch=digraph)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add -n coq-graph-theory.dev \
  'git+https://github.com/rocq-community/graph-theory.git#322e352b72c4ca3f153e5f80123c5020a0d40620'
opam install --jobs=2 $(sed '/^#/d; /^$/d' environment/rocq92/opam-packages.lock)
```

These top-level versions are locked; a native install still resolves platform dependencies.
The release receipt distinguishes the accepted Linux image from the fresh Mac installation,
including its Python and Zify qualifications. The image recipe also records which build inputs
remain live; rebuilding it does not reproduce the accepted image's identity.

Name the switch `digraph` if you can: the gates in `meta/` look for `~/.opam/digraph` by
default. Any other name works too, as long as you either put it on `PATH` (`eval $(opam env)`)
or point the gates at it explicitly with `ROCQ_OPAM_SWITCH=<switch-name>`.

### 2. Build

```sh
make all -j4              # base + classical-lemmas + the 13 area packages
make digraph-theory -j4   # the absorbed Digraph package
```

`digraph-theory` includes the large committed Cheng–Keevash certificate development
(see the note below) and dominates a full build. Budget a long first build; the release
receipt records the measured remainder stages and their resource limits. It is kept
out of `all` because its proofs are the heaviest in the repo;
its P9 milestone is still covered by `make gate`.

Build one package on its own with `make chromatic-theory`, and start over with `make clean`.
Each package target is just `rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq`
run inside that directory, so you can drop down to `Makefile.coq` for a single file.

### 3. Check the corpus claims

```sh
make audit    # no Rocq needed — python3 only; runtime depends on the host
```

`make audit` verifies that the committed manifest, leg-state overlay, dependency graph and
`meta/CORPUS_STATUS.md` are mutually consistent. CI runs this audit and the meta test suites;
the `meta-kernel` job installs the locked Rocq 9.2 stack. D-5 is the release acceptance.
The Mac audit took 38 minutes; do not assume this target is instantaneous.

The full acceptance gate additionally builds every landed milestone and checks it is
axiom-free with `Print Assumptions` clean:

```sh
git clone https://github.com/graph-theory-AI/graph-conjectures graph-conjectures
git -C graph-conjectures checkout --detach b72c5857060addbe4523016e88ae3aa626e958fd   # the pinned corpus commit (see below)
make gate
```

`make gate` regenerates the manifests from the conjecture source, so it needs that checkout.
If `$GRAPH_CONJECTURES` is set, it is the only place looked at; otherwise `./graph-conjectures`
(the nested clone, git-ignored), the sibling `../graph-conjectures` and
`~/Recherche/graph-conjectures` are tried in that order
(`meta/corpus_registry.py:graph_conjectures_dir`). The checkout found is VERIFIED before use:
it must be the top level of its own git clone, its `HEAD` must be exactly
`b72c5857060addbe4523016e88ae3aa626e958fd` (`GRAPH_CONJECTURES_COMMIT`), and `data/` must have no
changed or untracked file; anything else stops the command with `GraphConjecturesPinError`
instead of reading another corpus. Without any checkout, `make audit` replays the committed
pinned snapshot (as in CI).
The committed manifests are pinned to the exact commit `b72c5857060addbe4523016e88ae3aa626e958fd`
(`meta/corpus_registry.py:GRAPH_CONJECTURES_COMMIT`; short label `GRAPH_CONJECTURES_PIN`). It
came from the branch `CDC-relations-update`, merged into the official repository's `main` by
pull request #18 on 2026-09-23, so a clone of `main` contains it; the corpus is that commit, not
`main`'s later head. That commit adds the Bondy–Murty Appendix A records (`bm-NNN`), the curated `others` records and
the relations graph (`data/relations.json`) to the arXiv, OpenProblemGarden and erdősproblems
corpora.

### 4. Statement documentation, corpus links and relations

Every `Definition <name>_statement` (741 of them) is immediately preceded by a doc block
```
(** Corpus row: bm:bm-026
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-026/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-026.json
    English statement: ... (back-translated from the Rocq body, attribution first)
    Definitions: ... (every non-standard notion, with the file it lives in)
    Notes: ... (modelling choices, repairs, known settled cases) *)
```
whose row id and links must match the manifest (`python3 meta/check_statement_docs.py`, part of
`make audit`; the links assume the pinned corpus branch is merged into `main`). Statements
without a corpus row carry `(** No corpus row: <reason> *)`. The corpus relations file
(`data/relations.json`, 225 edges) is mirrored in `meta/corpus_relations.json` and cross-checked
against the machine-verified edge graph (`meta/dependency_graph.json`, 97 edges of which 20 are
Qed theorems). Shared vocabulary lives in `base/theories/common.v` (matchings, hamiltonicity,
edge-connectivity, tournaments, ...) on top of the coq-graph-theory modules re-exported by
`base/theories/base.v`; the ledger `meta/STATEMENT_IMPROVEMENTS.md` lists local notions that
duplicate library ones and the defects found and fixed, and
`meta/X211-X229_faithfulness_audit.md` records the two-reader readbacks, active probes and
repairs of the 2026-09-23 update.

The scope and token cost of that update are summarised in the "Latest update" paragraph at the
top of this file.

**Relations.** [github.com/graph-theory-ai/graph-conjectures](https://github.com/graph-theory-ai/graph-conjectures)
(`data/relations.json`) records 225 relations between its conjectures: 159 `implies`, 8
`equivalent_to`, 16 `same_conjecture` (aliases) and 42 `related_only`. Of the 167 implications
and equivalences, 112 have both endpoints formalized here and every one has a machine-checked
disposition: 62 are Qed theorems, 15 hold conditionally on a registered external theorem (the ten
theorems still to formalize are listed in [`classical-lemmas/TODO.md`](classical-lemmas/TODO.md)), 2 are
refuted as encoded, 24 are candidates blocked on a named ingredient, and 9 are kept as candidates
in the registry only (deep classical theorems such as Ryjáček's closure, or the unproved half of
an equivalence). The other 55 cannot be attempted yet: 33 join two rows with no statement (rows
parked as needing a computation model, a probability layer, or a proposition the source does not
state), 11 have one such endpoint, and 11 touch a statement that is itself a blocked placeholder.
On top of those, the repository's own audits contributed 5 verified Rocq-only relations, 31
documented non-edges and 4 further candidates (`meta/dependency_graph.json`, registry
`meta/edge_waves.json`, upstream feedback `meta/CORPUS_FEEDBACK.md`). Getting to this state cost
**18,074,929 metered sub-agent tokens** in total: 10,832,396 for the corpus re-sync, doc blocks,
base layer and waves X211–X229, and 7,242,533 for the implication programme (68 agents), plus the
two orchestrating Claude sessions, which are not metered.

### Note on `digraph-theory/theories/applications/ck_path`

The certificate modules are **committed**, so a fresh clone can check the
δ = 4, 5, 6, 7 cases of the Cheng–Keevash path conjecture without a SAT solver.
`scripts/generate_ckpath_certificates.py` and an external SAT solver produced the certificate
data; the transparent hinted-RUP/DRUP checker replays it inside Rocq.
The proved theorem [`ck_conj1_delta7`](digraph-theory/theories/applications/ck_path/ckpath_k7_concrete.v)
states that a nonempty oriented graph with minimum out-degree at least 7 has a simple
directed path of at least 14 arcs; `ck_conj1_delta7_path` supplies a path of exactly 14 arcs.
Both are in the accepted Rocq 9.2 release candidate
([`meta/releases/ROCQ92_ACCEPTED_2026-10-23.md`](meta/releases/ROCQ92_ACCEPTED_2026-10-23.md)).
They settle the case δ = 7 only: the conjecture itself (`cheng_keevash_conj1_statement`) stays
open, so they are recorded as special cases in
[`digraph-theory/docs/correspondence/curated.json`](digraph-theory/docs/correspondence/curated.json),
not as formal resolutions. See the [development README](digraph-theory/theories/applications/ck_path/README.md).

## Checked formal resolutions

Eleven source records have checked formal resolutions: ten new formalizations and a bridge to the existing Question 5.9 counterexample family. The latest addition refutes the heavy-path extension in the introduction of arXiv:1904.12273 (Chudnovsky, Scott and Seymour, "Detecting a long odd hole") as the row states it: for ell = 7 and every bound b, a graph on 3q + 4 vertices (q = 2b + 3) has a shortest long odd hole C and a set M of four C-major vertices, one of them nonadjacent to the others, such that every path of C containing a neighbour of each vertex of M has at least q edges. The graph is from a write-up generated by gpt-5.6-sol and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/9871a536271989364598b11974b95c7be4fe7cc2/attacks/1904.12273__01/output.md) (committed 2026-08-31); the paper states the extension inside its algorithm, for "candidate" graphs, a hypothesis the row does not state and which this graph is known to satisfy only by a computation (ell = 7, odd q >= 9) in the review of the write-up, so the extension in that setting stays open; the row's upstream status is unchanged. The previous addition checks in Rocq that the Open Problem Garden question "Geodesic cycles and Tutte's Theorem" has a negative answer as stated: in the eight-vertex 3-connected graph with one vertex inside each face of a tetrahedron, every assignment of positive edge lengths has a geodesic cycle that is not peripheral. The graph comes from a write-up generated by gpt-6-astra and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/abcc3defa6684921fe4b460174ea8b2810b5485b/attacks_opg/geodesic_cycles_and_tuttes_theorem/output.md) (committed 2026-09-16, merged 2026-09-17, MIT licence); "peripheral" has its standard meaning, induced and non-separating, the literature has not been searched for this example, and the row's OPG status is unchanged. The one before it refutes Conjecture 1 of arXiv:2304.03567 as the paper defines forward covers: a cyclic chain of m directed diamonds is a strong digraph on 3m vertices whose every forward cover needs m vertex orderings, so no O(log n) bound holds. The construction is from a write-up generated by gpt-5.6-sol and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/6b326f8fe5f24d25c4394dfb3fb51aea45a98f0b/attacks/2304.03567__04/output.md) (committed 2026-09-01); the row's upstream status is unchanged. The addition before that checks in Rocq that Melnikov's valency-variety question, as printed, has a negative answer: a 37-vertex graph with the degrees 0 to 29 is properly 3-colourable, so its chromatic number does not exceed the proposed bound ceil(15/7) = 3. The graph comes from a write-up generated by gpt-6-astra and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/65eeb06fe2e9368a123cf331cf2a1eead195097c/attacks_opg/melnikovs_valency_variety_problem/output.md) (committed 2026-09-16, merged 2026-09-17, MIT licence). Yang and Zeng ([arXiv:2610.09649](https://arxiv.org/abs/2610.09649), submitted 2026-10-07) prove chi(G) >= ceil(floor(w(G)/2)/(|V(G)| - w(G))) for every graph with at least two vertices, show that this is sharp, and refute the strict inequality with a different 37-vertex graph, not isomorphic to this one; their bound is not formalized here. Both graphs have an isolated vertex, which the printed statement admits; the row's OPG status is unchanged. Before them: Conjecture 1.15 of arXiv:1611.03196 (a large matching in a bipartite graph that takes at most its fair share of each given edge set), and the disproofs of directed Kneser existence at `(5,3)` and of the printed Alon–Tarsi Question 6.1. All eleven have closed assumptions.

See the [proof overview](meta/formalizations/README.md), [latest development journal](meta/formalizations/ROUND2_JOURNAL.md), and [resolution registry](meta/FORMAL_RESOLUTIONS.md). Run `ROCQ_OPAM_SWITCH=rocq-tools make resolutions` to build and check them with the compatible development switch.

## Checked repairs of proof gaps

The frozen-colouring switching bound and a six-cycle viability certificate now
have Rocq proofs. These are scoped results toward two source conjectures; the
full dynamics and planar-construction conclusions remain unformalized. See the
[repair audit](meta/GAP_REPAIRS.md) and [development journal](meta/GAP_REPAIRS_JOURNAL.md).
Run `ROCQ_OPAM_SWITCH=rocq-tools make gap-repairs` to compile the artifacts and
check their exact theorem types and closed assumptions.

## Public library packages (opam)

**Status: accepted source release, tagged `rocq92-accepted-2026-10-23`.**
- All 15 public packages and 3 compatibility wrappers were installed in a fresh Mac opam root; all 110 downstream examples passed. D-5 also passed its Linux private-prefix install gate.
- The [release receipt](meta/releases/ROCQ92_ACCEPTED_2026-10-23.md) records the exact source, environment, checks and installation qualifications. This is not an opam-repository release.
- Counts, dependencies and barriers below are measured at `2e15adf` (the classifier and this metadata on `45474d5`). No public module imports a corpus file there: the barriers listed at the classifier parent `2933916` were resolved by their family releases.

Each package builds and installs **only public modules**. These live in `base/theories/*.v`, in `classical-lemmas/theories/` except its conjectures, migration and examples, and in `<area>/theories/{foundations,core,invariants,constructions}/` (plus `digraph-theory/theories/invariants_advanced/`). They are installed as `.v`/`.vo`/`.glob` under `user-contrib/<Namespace>`.

Conjectures, statements, grounding and implication files, applications, migration certificates and `examples/` are never installed. They stay in this repository and are built by `make`.

| opam package | area | namespace | public modules | internal deps (`{= version}`) | external deps (exact pins) | at `2e15adf` |
|---|---|---|---:|---|---|---|
| `rocq-graph-theory-base` | `base/` | `GTBase` | 55 | — | coq-graph-theory dev (pin-depends), mathcomp algebra/boot/finite-group 2.6.0; rocq-hierarchy-builder 1.10.3 (a reviewed pin, not a measured direct need) | no corpus barrier; installed end to end at `2933916` |
| `rocq-graph-theory-classical-lemmas` | `classical-lemmas/` | `ClassicalLemmas` | 15 | base | coq-graph-theory, mathcomp algebra/boot/order | no corpus barrier |
| `rocq-graph-theory-topological` | `topological-graph-theory/` | `Topological` | 6 | base | coq-graph-theory, mathcomp algebra/boot/finite-group | no corpus barrier |
| `rocq-graph-theory-minor` | `minor-theory/` | `Minor` | 8 | base | coq-graph-theory | no corpus barrier |
| `rocq-graph-theory-chromatic` | `chromatic-theory/` | `Chromatic` | 10 | base | coq-graph-theory, mathcomp boot | no corpus barrier |
| `rocq-graph-theory-cycle` | `cycle-theory/` | `Cycle` | 7 | base | coq-graph-theory | no corpus barrier |
| `rocq-graph-theory-packing` | `packing-theory/` | `Packing` | 5 | base, classical-lemmas | coq-graph-theory, rocq-stdlib 9.1.0 | no corpus barrier |
| `rocq-graph-theory-reconstruction` | `reconstruction-theory/` | `Reconstruction` | 2 | base | coq-graph-theory, mathcomp boot | no corpus barrier |
| `rocq-graph-theory-hypergraph` | `hypergraph-theory/` | `Hypergraph` | 7 | base | — | no corpus barrier |
| `rocq-graph-theory-misc` | `graph-theory-misc/` | `GTMisc` | 3 | base | coq-graph-theory | no corpus barrier |
| `rocq-graph-theory-spectral` | `spectral-graph-theory/` | `Spectral` | 2 | base | coq-graph-theory, mathcomp algebra/boot/finite-group | no corpus barrier |
| `rocq-graph-theory-extremal` | `extremal-graph-theory/` | `Extremal` | 10 | base | coq-graph-theory, mathcomp algebra/boot/order | no corpus barrier |
| `rocq-graph-theory-infinite` | `infinite-graph-theory/` | `Infinite` | 2 | — | mathcomp boot | no corpus barrier |
| `rocq-graph-theory-digraph` | `digraph-theory/` | `Digraph` | 24 | — | coq-graph-theory, rocq-hierarchy-builder, mathcomp algebra/boot/classical/finite-group | no corpus barrier |
| `rocq-graph-theory-atlas` | `atlas/` | `Atlas` | 6 | base, chromatic, extremal, misc, hypergraph | coq-graph-theory, mathcomp algebra | no corpus barrier |

**Dependency notes:**
- Every package also depends on `rocq-core` 9.2.0 and on `conf-python-3` at build time.
- MathComp packages are `rocq-mathcomp-*` 2.6.0, except `rocq-mathcomp-classical` 1.16.0. On Rocq 9.2 the fingroup modules belong to `rocq-mathcomp-finite-group`.
- `coq-graph-theory` is the UNRELEASED commit `322e352b` of rocq-community/graph-theory (tree `46c83591`). Every package that lists it pins it with `pin-depends` (url#commit).
- The dependencies listed are the direct ones measured from each package's public modules. Base also keeps its reviewed `rocq-hierarchy-builder` pin, which is not a measured direct need.

**Barriers:** a package is blocked when one of its public modules imports a corpus file. Such a module is never dropped to make packaging pass. At `2e15adf` no package is blocked.

**Empty layers:** `hamiltonicity-theory` (`Hamilton`) and `homomorphism-theory` (`Hom`) have no public layer yet, only statements. They have no package, and none will be invented.

**Compatibility names:** `coq-graph-theory-base`, `rocq-digraph-theory` and `coq-digraph-theory` are now wrappers. Each installs nothing itself and depends on `rocq-graph-theory-base` or `rocq-graph-theory-digraph` at the same version. They provide the public library only, no longer the corpus, applications or certificate modules. Their canonical files are in `opam/`; the old files in `base/` and `digraph-theory/` are identical copies.

**Supported imports:** the logical path is the namespace followed by the path under `theories/`, for example:

```coq
From GTBase Require Import base.
From Packing Require Import foundations.matching.
From Digraph Require Import core.tournament.
```

Only modules of installed packages resolve; a corpus or example module never does. The repository's `theories/examples/` files are public-API clients built by `make`, and no example reaches a corpus file. They are documentation, not installed.

**Installing the accepted source release:** these files are not published in any opam repository, and no opam-repository release is claimed. Pin the WHOLE source, never one package alone: `pin-depends` is not transitive, so a single pinned package would leave its internal dependencies unpinned. Use a switch with Rocq 9.2.0, `rocq-stdlib` 9.1.0, MathComp 2.6.0 (`rocq-mathcomp-classical` 1.16.0) and `rocq-hierarchy-builder` 1.10.3; `coq-graph-theory` comes from its `pin-depends` commit. On this project's VM, pass `--jobs=2` explicitly: the default job count failed there.

```sh
# from a CLEAN checkout at the release commit (the VCS kind pins the committed state, not the working directory)
opam pin add -y --no-action --kind=git .
opam install rocq-graph-theory-base --jobs=2
# or, from the forge, at the release commit
RC_COMMIT=3ca79221b863786b7b79c68f9a635928e8f82601
opam pin add -y --no-action "git+https://github.com/graph-theory-AI/graph-theory-rocq.git#${RC_COMMIT}"
opam install rocq-graph-theory-misc --jobs=2
```

**Build requirement:** building requires **Python >= 3.9** (tested with 3.12.3 on Linux and 3.12.4 on the Mac). It stages the public modules with `meta/library_package.py`. `conf-python-3` only checks that `python3` is present, so each package's first build step checks the version.

**Versioning:** consistent with the plan's §12.
- All packages share one version, and internal dependencies require exactly that version.
- Public names follow the registry: stable once `canonical`; possibly changed while `proposed` or `auditing`. Deprecated aliases remain for at least one completed migration batch and until their tracked consumers are zero.
- **Major** increment: removing or renaming a canonical name, removing a deprecated alias after that window, or a semantic correction of a public definition. A semantic correction is not a deprecation: it needs a faithfulness audit, a manifest note and an explicit old/new relationship.
- **Minor** increment: new public modules or names, and new deprecations that keep their aliases.
- **Patch** increment: proofs, documentation or packaging only, with no change to public names or meanings.
- Statement `formal_name`s are permanent corpus identifiers and are not part of these packages.

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
- `base/` — `rocq-graph-theory-base` (compatibility name `coq-graph-theory-base`): the single owner of cross-area primitives (interop façade,
  homomorphism, products, list-χ, line/total-graph, Δ, surfaces) and, in `theories/common.v`,
  the shared conjecture vocabulary built on the re-exported coq-graph-theory modules
  (`connectivity`, `minor`, `treewidth`, `dom`).
- `<area>-theory/` — the area packages (each: foundations/core/invariants/constructions/conjectures/applications).
- `meta/` — the v1 completion report + roadmap (`OPG_FULL_FORMALIZATION_PLAN.md`), the validated 227-row
  manifest + leg-state overlay, the federated dependency graph (`dependency_graph.json`), the status report
  (`CORPUS_STATUS.md`), the corpus relations mirror (`corpus_relations.json`), and the gates
  (`check_milestone.py`, `report_corpus_status.py`, `build_edge_graph.py`, `check_statement_docs.py`).
- `atlas/`, `blueprint/` — *scaffolds* reserved for later extraction of the cross-area edge atlas and the
  shared dev tooling; both currently live in `meta/` (see the stubs' `Status: scaffold`).

`digraph-theory/` was absorbed from the standalone repo via a subtree merge (history preserved).
See `meta/OPG_FULL_FORMALIZATION_PLAN.md` §A / §A.1.
