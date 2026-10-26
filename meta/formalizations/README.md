# Checked graph-theory resolutions

Eleven source records now have exact, assumption-free Rocq proofs or refutations in this repository. Ten are new formalizations; Question 5.9 reuses an existing construction through a new statement bridge.

| Source record | Checked result | Final module |
|---|---|---|
| `2103.15175__00` | List Ramsey least forcing order `s^k+1`, for all `s>=2`, `k>=1` | [list_ramsey_graph.v](../../extremal-graph-theory/theories/applications/list_ramsey_graph.v) |
| `2408.02400__00` | For every `k>=5`, a graph with clique number 4, cochromatic number `k`, and chromatic number `k+3` | [cochromatic_gap.v](../../chromatic-theory/theories/applications/cochromatic_gap/cochromatic_gap.v) |
| `2512.10438__00` | Six-color, nine-vertex nontransitive tournament with longest avoiding path 7 vertices, below the exact transitive benchmark 8 | [color_avoiding_tournament.v](../../digraph-theory/theories/applications/color_avoiding_tournament.v) |
| `2310.04265__09` | Negation of the existing Question 5.9 statement | [question_5_9_resolution.v](../../digraph-theory/theories/applications/question_5_9_resolution.v) |
| `1812.02420__03` | No directed Kneser graph at `(k,b)=(5,3)`, refuting the universal existence statement | [directed_kneser_nonexistence.v](../../digraph-theory/theories/applications/directed_kneser_nonexistence.v) |
| `2209.09107__00` | The triangle refutes printed Alon–Tarsi Question 6.1 with its unfloored degree bound | [alon_tarsi_triangle.v](../../chromatic-theory/theories/applications/alon_tarsi_triangle.v) |
| `2304.03567__04` | The diamond chain on `3m` vertices is strong and needs `m` orderings in every forward cover, refuting Conjecture 1 (an `O(log n)` forward cover for every strong digraph); the construction is from the gpt-5.6-sol write-up in [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/6b326f8fe5f24d25c4394dfb3fb51aea45a98f0b/attacks/2304.03567__04/output.md) | [forward_cover_disproof.v](../../digraph-theory/theories/applications/forward_cover_disproof.v) |
| `1904.12273__01` | For `ell = 7` and every bound `b`, a graph on `3q + 4` vertices (`q = 2b + 3`) has a shortest long odd hole `C` and four `C`-major vertices, one nonadjacent to the others, that no path of `C` with fewer than `q` edges catches, refuting the heavy-path extension of arXiv:1904.12273 as stated (the paper's candidate setting is not encoded); the construction is from the gpt-5.6-sol write-up in [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/9871a536271989364598b11974b95c7be4fe7cc2/attacks/1904.12273__01/output.md) | [heavy_path_disproof.v](../../graph-theory-misc/theories/applications/heavy_path_disproof.v) |
| `1611.03196__03` | Conjecture 1.15: every bipartite `G` with `Delta(G)>0` and any `m` edge sets `E_i` admit a matching `S` with `floor(#E(G)/Delta(G)) <= #S + c(m)` meeting each `E_i` in at most `ceil(#E_i/Delta(G))` edges, with `c(m) = 12m + 14` in this formal floor form, giving `12m + 15` in the paper's form `#S >= #E(G)/Delta(G) - c(m)` | [fair_matching.v](../../packing-theory/theories/foundations/fair_matching.v) |
| `opg:geodesic_cycles_and_tuttes_theorem` | The 3-connected graph with one vertex inside each face of a tetrahedron has, for every positive edge-length assignment, a geodesic cycle that is not peripheral, so the OPG question has a negative answer as stated; the graph is from the gpt-6-astra write-up in [Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/abcc3defa6684921fe4b460174ea8b2810b5485b/attacks_opg/geodesic_cycles_and_tuttes_theorem/output.md) | [geodesic_cycles_tutte.v](../../extremal-graph-theory/theories/applications/geodesic_cycles_tutte.v) |
| `opg:melnikovs_valency_variety_problem` | A 37-vertex graph with degrees `0..29` is properly 3-colourable, a negative answer to the printed question (it has an isolated vertex, which the statement admits); the graph is from the gpt-6-astra write-up in Graph-Theory-LLM-Proofs; Yang and Zeng, arXiv:2610.09649, prove the sharp non-strict bound | [melnikov_valency_variety.v](../../chromatic-theory/theories/applications/melnikov_valency_variety.v) |

The `1611.03196__03` entry, added on 2026-09-16 and sharpened on 2026-09-18 and
2026-09-19, is proved
through Alon's Splitting Necklace Theorem: König line colouring turns `E(G)` into
`Delta(G)` matchings whose statistic vectors average to the target, and two
matchings are interpolated by splitting the necklace of their symmetric
difference — one group of `m+1` beads per edge — between two thieves. It follows
the LLM attack recorded in `packing-theory/theories/conjectures/X15.v` except on
three points, all stated in the proof file. Every interpolation is a halving, in
place of the write-up's prescribed-ratio splitting lemma, which does not follow
from the equal-share necklace theorem at a cut cost independent of the ratio. The
write-up's Carathéodory step and its one-splitting-per-pair mixing are replaced
by *synchronized rounds*: Alon's cut budget is per splitting, not per pair, so
all the pairs of one round are halved by a single splitting of the concatenation
of their necklaces, and the leaves are `2^L` copies of all the colour classes
padded with the empty matching. And the write-up's trimming step disappears,
parity being repaired by retyping the first bead of each odd type to a null type
and discarding its edge, so each round rounds the class counts exactly down. The
constant is therefore linear, `c(m) = 12m + 14` in the formal floor form
`floor(#E(G)/Delta(G)) <= #S + c(m)` (`12m + 15` in the source's form
`#S >= #E(G)/Delta(G) - c(m)`, allowing one extra unit when converting the floor bound),
against the `32(m+1)^3` claimed by the attack. Those first two deviations are suggestions of Laurent Viennot,
and are what turns the write-up's `O(m^3)` into `O(m)`; a third of his
suggestions sharpens the ledger of a single round — a cut interior to a bead
group throws its edge away and so cannot also witness a conflict, conflicts
being between two *kept*, hence unanimous, edges whose thief change sits at a
group boundary — which brings `16m + 24` down to `12m + 14` in the formal floor
form (`12m + 15` in the paper's inequality form). The same file also
proves X15's own `bipartite_matching_underrepresentation_llm_statement`,
`..._llm2_statement` and `..._llm3_statement` (`c <= 12m + 14` in the formal floor
form, giving `12m + 15` in the paper's form), all with that same floor-form
constant. The topological and classical inputs — Alon's theorem via
Meunier's simplotopal Tucker lemma, König's line colouring, and the structure of
the union of two matchings — are in the `classical-lemmas` package, which depends
only on MathComp and GraphTheory and on which `packing-theory` depends;
Carathéodory over the rationals is there too but is no longer used by this proof.
See
[X15_FAIR_MATCHING_REPORT.md](../../packing-theory/docs/X15_FAIR_MATCHING_REPORT.md)
and `classical-lemmas/NECKLACE_STATUS.md`. Its source correspondence was
independently reviewed on 2026-10-23 (the registry entry names the reviewer):
confirmed, with one precision — the explicit constant `12m + 14` is that of the
formal floor form, `12m + 15` in the source's form. The statement it proves is
the pre-existing, already-reviewed encoding of Conjecture 1.15 in `X15.v`,
unchanged.

## Checked repair artifacts

Two further Rocq developments repair finite proof steps without resolving their
source conjectures. The frozen-colouring modules prove `(n+4)F <= 4P` and
`P > 0` for connected noncomplete graphs with `Delta+1` colours; the
[frozen-colouring result](../../chromatic-theory/theories/applications/gap_repairs/frozen_coloring_resolution.v)
also identifies frozen proper colourings with those isolated under one-vertex
recolouring. The [six-cycle certificate](../../chromatic-theory/theories/applications/gap_repairs/viable_boundary.v)
proves the exact grid-map viability condition for both boundary hue labellings.

These artifacts are not entries in the resolution registry: the broader
dynamics and arbitrary-parameter planar-construction conclusions remain
unformalized. The [repair audit](../GAP_REPAIRS.md),
[development journal](../GAP_REPAIRS_JOURNAL.md), and
[assumption transcript](../GAP_REPAIR_ASSUMPTIONS.txt) record their scope and
verification.

From the repository root, using an installed compatible switch:

```sh
ROCQ_OPAM_SWITCH=rocq-tools make resolutions
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/test_formal_resolutions.py
ROCQ_OPAM_SWITCH=rocq-tools make gap-repairs
make audit
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/formal_resolutions.py \
  --report meta/formalizations/ASSUMPTIONS.txt
```

The development environment used Rocq 9.1.1, OCaml 5.3.0 and the installed MathComp/GraphTheory libraries in `rocq-tools`. The live checker builds the required local dependencies and rejects nonclosed assumptions and mismatched statements. It preserves historical source statuses.

Read the [first-round development journal](JOURNAL.md) and [second-round journal](ROUND2_JOURNAL.md) for the proof attempts, MCP workflow, certificate optimizations and integration decisions. The [assumptions transcript](ASSUMPTIONS.txt) records the successful eleven-entry check (regenerated on 2026-10-25 in the Rocq 9.2 image; the Melnikov entry added the same day, the forward-cover, geodesic-cycle and heavy-path entries on 2026-10-26). The [registry documentation](../FORMAL_RESOLUTIONS.md) explains source correspondence and the validation contract.

Validation on 2026-09-19, after sharpening the ledger of a single round
(`c(m)` from `16m+24` down to `12m+14` in the formal floor form, or `12m+15`
in the paper's inequality form: hits and conflicts charge disjoint cuts,
and only the `2m` class types are charged for the parity repair):
`python3 meta/check_milestone.py X15 packing-theory` passed all 11 acceptance
checks again, `make classical-lemmas && make packing-theory` is clean, and
`Print Assumptions` answers `Closed under the global context` for the nine
results of `fair_matching.v`. The `..._llm3_statement` of `X15.v` was tightened
from `c <= 16m + 25` to `c <= 12m + 14` in the formal floor form
(`12m + 15` in the paper's form); `..._statement`,
`..._llm_statement` and `..._llm2_statement` are unchanged.

Validation on 2026-09-18, after the synchronized-rounds rewrite of
`fair_matching.v` (`c(m)` from `(m+1)^2(16m+29)` down to `16m+24`):
`python3 meta/check_milestone.py X15 packing-theory` passed all 11 acceptance
checks again, `make classical-lemmas && make packing-theory` is clean, and
`Print Assumptions` answers `Closed under the global context` for
`round_exists`, `rounds_exists`, `approx_fair_rounds`, `x15_rounds_instance`,
`x15_llm3_proof`, `x15_llm2_proof`, `x15_llm_proof` and
`bipartite_matching_underrepresentation`.

Validation on 2026-09-17: `python3 meta/check_milestone.py X15 packing-theory`
passed all 11 acceptance checks, which includes the live registry check for
`1611.03196__03` — the registered sources are recompiled and a fresh probe checks
`Check (theorem : statement)` and reports `Closed under the global context` for
both constants. The whole-registry run `make resolutions` cannot be completed in
the current switch for an unrelated reason: the `1812.02420__03` entry lives in
`digraph-theory`, which requires MathComp's `boolp`/`classical_sets`, absent
here.

Validation on 2026-09-05: all six resolutions passed, both new proof objects passed independent `rocqchk` validation, all 14 checker regression tests passed, and `make audit` passed. The native X2 milestone passed all 11 acceptance checks. The second round was developed in an isolated worktree based on the pushed first-round proof commit. The old dependency-graph drift belongs to the separate library-migration checkout. Source correspondence was independently reviewed by other agents and remains open to human mathematical review.
