# Formal resolutions

`formal_resolutions.json` records local, kernel-checked proofs separately from the
upstream conjecture catalog. Its source statuses, manifests, snapshots and
statement-formalization legs remain unchanged. A source row can therefore still
say `open` or `partial` while this registry records a checked proof or disproof.

The registry holds eleven entries:

| Record key | Direction | Result (section below) |
|---|---|---|
| `1611.03196__03` | prove | Fair representation by matchings (X15) |
| `1812.02420__03` | disprove | Directed Kneser nonexistence |
| `1904.12273__01` | disprove | Heavy paths in shortest long odd holes |
| `2103.15175__00` | prove | List Ramsey numbers |
| `2209.09107__00` | disprove | Alon–Tarsi orientation counterexample |
| `2304.03567__04` | disprove | Forward covers of strong digraphs |
| `2310.04265__09` | disprove | Question 5.9 |
| `2408.02400__00` | prove | Chromatic and cochromatic gap |
| `2512.10438__00` | prove | Color-avoiding tournament paths |
| `opg:geodesic_cycles_and_tuttes_theorem` | disprove | Geodesic cycles and Tutte's theorem |
| `opg:melnikovs_valency_variety_problem` | disprove | Melnikov's valency-variety problem |

Run the proof checks in the repository's pinned Rocq 9.2 toolchain (the image of
the guarded wrapper, where `rocq` is on `PATH`):

```sh
make resolutions                                  # python3 meta/formal_resolutions.py
python3 meta/test_formal_resolutions.py
python3 meta/formal_resolutions.py --record 1611.03196__03
python3 meta/formal_resolutions.py --package digraph-theory --metadata-only
```

`--record KEY` (repeatable) and `--package PACKAGE` restrict either mode to those
entries; an unknown key, or a selection that matches no entry, fails. Outside the
image, `ROCQ_OPAM_SWITCH` selects an opam switch by name or absolute directory: it
must be the Rocq and OCaml build that produced the existing objects, since the Rocq
version alone does not identify compatible objects.

The checker builds the registered statement/proof targets with the package's
generated Makefile, then recompiles the actual registered source files and a
fresh probe. Local package dependencies named by load-path flags are built
first; external libraries must be available under the selected switch. `make gate` includes the
resolution checker. `make audit` checks metadata only and explicitly reports that
proofs were not checked.

## What an entry establishes

Each v2 entry copies the source row identity, text, locator and source hash from the
pinned corpus manifest. It names a statement file and a fully qualified
proposition, the statement declaration's SHA-256 digest, a proof file and a fully
qualified theorem, and the direction `prove` or `disprove`. Both source files
must be listed in their package's `_CoqProject`, and the qualified names must
match the files' load-path mappings. Existing formalized rows must use their
original statement location and formal name.

An OPG entry (`"corpus": "opg"`) is keyed `opg:<slug>` and copies the identity of
that row of the pinned `opg_corpus_manifest.json`: `node_id`, `canonical_url`, the
two upstream commits `source_commit_repo` and `source_commit_problems_json`,
`source_text` and `selected_proposition`. OPG rows carry no source hash, and the
checker does not invent one. The statement must be the row's `formal_name`, in the
row's package. Its `statement_file` must be the one project-listed file of that
package that defines the name at top level:
- definitions inside a `Module`, such as the frozen copies in migration
  certificates, do not count;
- a `Section` leaves its definitions public, so they do count;
- a second top-level definition makes the row ambiguous and is rejected.

Every entry carries exactly the fields of its corpus.

The checker compiles either `Check (theorem : statement)` or
`Check (theorem : ~ statement)`, and requires `Print Assumptions` for **both**
constants to report `Closed under the global context`. This rejects additional
mathematical axioms, admissions, conditional proofs, the wrong polarity and
proofs of unrelated statements. A stored transcript is supplementary evidence;
it never substitutes for the live compiler checks. Use `--report PATH` to save
the successful probe output. The report drops compiler warning blocks, which name the
run's temporary probe file, so it is reproducible; the pass or fail decision reads the
whole output, and any other mention of the probe file fails the check.

The milestone gate allows only the freshly verified triple
`(statement, theorem, direction)`. All other exact-type faithfulness probes remain
active, including probes for another theorem claiming the same source row. The
registry has no wildcard, package-wide or source-status exception. Failed
registry verification itself fails the milestone.

## Source correspondence

The `correspondence` object records the implementation author, a distinct source
reviewer, review date and an explanation of the formal statement. For a new
encoding, review quantifier order, object types and relevant finite or degenerate
cases before adding a resolution. For an existing encoding, preserve the
statement and add an exact bridge theorem when the mathematical construction is
stated in a different form.

The statement hash is computed from its declaration after stripping Rocq
comments and normalizing whitespace. A changed declaration requires an updated
correspondence review. Source hashes are the corpus's pinned values; the checker
compares them directly and does not invent a different source-hashing algorithm.

Rocq checks the formal proposition. Whether that proposition faithfully expresses
the paper is still a source-reading judgment. The registry does not replace the
existing foundation-fidelity checks, correspondence audits, or human mathematical
review, and it does not establish historical novelty.

## Initial result: list Ramsey numbers

For source record `2103.15175__00`,
`Extremal.applications.list_ramsey_graph.list_ramsey_chromatic_resolution`
proves the exact least forcing order `s^k + 1` for every `s >= 2` and `k >= 1`.
The statement allows arbitrary natural-number colors and distinct `k`-element
edge lists, and uses the graph library's chromatic number to express a
monochromatic member of the family of graphs with chromatic number greater than
`s`.

The finite proof is in `foundations/list_ramsey.v`: label each vertex by one
`s`-valued coordinate for each color, avoiding agreement on all colors in any
incident list. Each already labeled vertex excludes a fraction `s^(-k)` of the
possible labels, so fewer than `s^k` vertices cannot block all choices. Constant
lists give the matching upper bound by the pigeonhole principle. The modules
`applications/list_ramsey_nat.v` and `applications/list_ramsey_graph.v` establish
the arbitrary-color and graph-chromatic interpretations, respectively.

## Initial result: Question 5.9

For source record `2310.04265__09`, the existing theorem
`Digraph.applications.unified.question_5_9_fails_at_k3` gives arbitrarily large
3-critical tournaments whose proper subtournaments all have tournament clique
number below 3. The new
`Digraph.applications.question_5_9_resolution.question_5_9_disproved` connects
that family directly to `~ Digraph.conjectures.clique_cluster.question_5_9_statement`.

If a bound function `ell` existed, apply the family at order greater than `ell 3`.
The asserted bounded witness would have clique number at least 3 and hence would
have to be the whole tournament, contradicting its size bound. The construction
was already in the repository; this addition supplies the exact source-statement
bridge and checks its full assumptions.

## Chromatic and cochromatic gap

For source record `2408.02400__00`,
`Chromatic.applications.cochromatic_gap.cochromatic_gap.cochromatic_gap_three_proved`
has exactly the existing `Chromatic.conjectures.X7.cochromatic_gap_three_statement`
type. For every `k >= 5` it constructs a finite simple graph with clique number
four, exact cochromatic number `k`, and chromatic number `k + 3`.

The seed is the 13-vertex complement of the circulant graph `C_13(1,5)`.
Exhaustive Rocq certificates bound its clique and stable-set sizes, and explicit
colorings give chromatic number seven and cochromatic number four. General
Mycielski-construction lemmas preserve clique number four while increasing both
coloring numbers by one. After `k - 4` iterations, the parameter identities give
the exact source statement. All implementation modules are under
`chromatic-theory/theories/applications/cochromatic_gap/`.

## Color-avoiding tournament paths

For source record `2512.10438__00`,
`Digraph.applications.color_avoiding_tournament.problem_5_1_q6_n9` gives a
six-colored nontransitive tournament on nine vertices whose longest
color-avoiding simple directed path has seven vertices. The proof also computes
the exact transitive benchmark: every six-coloring of the transitive tournament
on nine vertices has an avoiding path with at least eight vertices, and one
coloring has no longer avoiding path. Therefore `7 < f_{6,5}(9) = 8` answers
the source question affirmatively at `q = 6`, `N = 9`.

The formal paths use the library's `dipath` predicate. Exhaustive searches have
a proved completeness lemma, which connects their negative results to bounds
on all simple paths. The universal transitive lower bound uses a smaller
certificate: consider the eight consecutive edge colors, then delete an
endpoint or one internal vertex. Color-renaming symmetry reduces the word
enumeration to two cases of `6^6` words. All certificates are closed Rocq proofs.

The [original paper](https://arxiv.org/html/2512.10438v1) defines path length in
vertices and its `f`-function by minimization over transitive tournaments. Its
Problem 5.1 requires nontransitivity; the construction satisfies the stated
conditions. The five implementation files are
`digraph-theory/theories/applications/color_avoiding_{paths,benchmark,word_symmetry,word_certificate,tournament}.v`.

## Directed Kneser nonexistence

For source record `1812.02420__03`,
`Digraph.applications.directed_kneser_nonexistence.directed_kneser_existence_disproved`
refutes the unchanged `Digraph.conjectures.X2.directed_kneser_existence_statement`.
There is no digraph on the three-element subsets of a five-element set whose
induced acyclic families are exactly the families with nonempty intersection.
This answers general existence negatively at `(k,b)=(5,3)`.

The proof is symbolic. Four triples have empty total intersection, whereas every
three intersect. Auxiliary triples force every pair among the four to have an
arc between them. The intersection condition prohibits loops, digons and directed
triangles, so these four vertices induce a transitive, acyclic tournament, a
contradiction. Finite computation checks only small set facts.

The [source paper](https://arxiv.org/html/1812.02420) permits antiparallel arcs and
counts digons as cycles, matching the formal acyclicity predicate. Parallel arc
multiplicities do not affect the property. This result establishes the finite
counterexample; the informal attack's complete classification of all parameter
pairs remains outside this formalization.

## Alon–Tarsi orientation counterexample

For source record `2209.09107__00`,
`Chromatic.applications.alon_tarsi_triangle.question_6_1_disproved` refutes the
printed Question 6.1 of *List-avoiding orientations*. The triangle has no spanning
subgraph with an Alon–Tarsi orientation meeting the requested bound at every
vertex.

The [printed question](https://arxiv.org/html/2209.09107v2) requires outdegree at
least `(degree_G(v)-1)/2`, without a floor. The formal statement uses the exact
integer inequality `degree_G(v) <= 2*outdegree(v)+1`, with degree measured in the
original graph. Its chosen arc set may omit edges and retains all vertices.
Eulerian subgraphs include the empty arc set.

On the triangle, the bound forces the three-cycle orientation, which has equal
even and odd Eulerian-subgraph counts. The reusable
`foundations/alon_tarsi.v` proves the general reason: complementing an Eulerian
subset inside any odd Eulerian arc set reverses its parity and gives a bijection
between the two classes. The application proves the triangle constraints by
expanding three vertices and considering its six possible directed nonloop arcs;
it uses ordinary Boolean case analysis. This refutes the printed inequality;
no floored variant is claimed.

## Fair representation by matchings

For source record `1611.03196__03`,
`Packing.foundations.fair_matching.bipartite_matching_underrepresentation` has
exactly the existing
`Packing.conjectures.X15.bipartite_matching_underrepresentation_statement` type
(arXiv:1611.03196, Conjecture 1.15). For every `m` there is a constant `c(m)` with
the following property. Let `G` be a bipartite graph with at least one edge and
`E_1, ..., E_m` any sets of its edges. Then `G` has a matching `S` with
`floor(|E(G)|/Delta(G)) <= |S| + c(m)` and `|S ∩ E_i| <= ceil(|E_i|/Delta(G))`
for every `i`.

The proof gives `c(m) = 12m + 14` in this floor form. In the source's form
`|S| >= |E(G)|/Delta(G) - c(m)` the constant is `12m + 15`; the existence statement
is the same.
- König's line colouring splits `E(G)` into `Delta(G)` matchings.
- Synchronized rounds of halvings mix those matchings. Each round is a single
  application of Alon's splitting necklace theorem at `q = 2` (formalized in
  `classical-lemmas`) to the concatenated necklaces of one level of the mixing tree.
- Parity is repaired by removing one bead of every odd type and discarding its edge (the
  X15 report, section 1).

The construction, its deviations from the attack write-up and the constant are
described in `packing-theory/docs/X15_FAIR_MATCHING_REPORT.md`. The correspondence
was reviewed independently on 2026-10-23.

## Melnikov's valency-variety problem

For the OPG row `opg:melnikovs_valency_variety_problem`,
`Chromatic.applications.melnikov_valency_variety.melnikovs_valency_variety_disproved`
refutes `Chromatic.conjectures.U1.melnikovs_valency_variety_statement`, the
affirmative answer to the problem as printed: every graph `G` with at least two
vertices has chromatic number greater than `ceil(floor(w(G)/2) / (|V(G)| - w(G)))`,
where the valency-variety `w(G)` counts the distinct vertex degrees, degree 0
included.

The 37-vertex graph, from section 1 of the write-up generated by gpt-6-astra and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/65eeb06fe2e9368a123cf331cf2a1eead195097c/attacks_opg/melnikovs_valency_variety_problem/output.md) (commit `65eeb06`, 2026-09-16; merged by PR #3 on 2026-09-17; MIT licence), has the degrees `0, 1, ..., 29`, so
`w(G) = 30` and the bound is `ceil(15/7) = 3`, and a proper 3-colouring, so its
chromatic number is at most 3 (a triangle makes it exactly 3). The proof checks the
write-up's degree table and the colouring by computation over an explicit list of
the 37 vertices, and bounds the chromatic number with
`GTBase.colourings.proper_colouring_chi`.

Caveat: the graph has an isolated vertex. The printed "any graph G with at least two
vertices" admits it, and so does the row's body; whether the problem was meant for
graphs without isolated vertices is not settled here, and the row's OPG status is
unchanged. The write-up's claim that 37 vertices is the minimum is not formalized.

Literature: Yang and Zeng, *Melnikov's Valency Variety Problem*, [arXiv:2610.09649](https://arxiv.org/abs/2610.09649) (v1, submitted 2026-10-07), prove `chi(G) >= ceil(floor(w(G)/2) / (|V(G)| - w(G)))` for every graph with at least two vertices (Corollary 1.3, from the sharper Theorem 1.2) and refute the strict inequality with a 37-vertex graph `G*` (Section 4.1) and an infinite family `G_q` (`q >= 3`) with `14q - 5` vertices and chromatic number `q`; `G*` and every `G_q` also have a vertex of degree 0. `G*` is not isomorphic to the graph checked here: both have 263 edges and the same degree multiset, but here the vertex of degree 1 is adjacent to a vertex of degree 21, in `G*` to one of degree 26. Their lower bound is not formalized here. The write-up's public referee report ([verification_astra/melnikovs_valency_variety_problem.md](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/d8f9d6470c7c51f719591fd03de672e1d6ef2f3d/verification_astra/melnikovs_valency_variety_problem.md)) could not obtain Jensen and Toft (1995), p. 90, which OPG cites; neither it nor the original appearances OPG marks (Vizing 1968; Zykov 1968) were consulted here.

## Forward covers of strong digraphs

For source record `2304.03567__04`,
`Digraph.applications.forward_cover_disproof.logarithmic_forward_cover_disproved`
refutes `Digraph.conjectures.X231.logarithmic_forward_cover_statement`, Conjecture 1
of *Temporalizing digraphs via linear-size balanced bi-trees* (arXiv:2304.03567):
every strong digraph on `n` vertices has a forward cover of size `O(log n)`. The
statement uses the paper's definitions. A forward cover is a set of vertex orderings
in which every pair of distinct vertices is joined, in at least one ordering, by a
directed path whose vertices increase in that ordering. `O(log n)` is read as
constants `c` and `n0` with a cover of at most `c * floor(log2 n)` orderings for
every strong digraph on `n >= n0` vertices.

The diamond chain `D_m` is the construction of the write-up generated by gpt-5.6-sol and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/6b326f8fe5f24d25c4394dfb3fb51aea45a98f0b/attacks/2304.03567__04/output.md) (commit `6b326f8`, 2026-09-01). It has the vertices `c_k, a_k, b_k` for `k` in `Z_m` and
the arcs `c_k -> c_(k+1)`, `c_k -> a_k -> c_(k+1)` and `c_k -> b_k -> c_(k+1)`.
It is strong and has `3m` vertices. The twins `a_i` and `b_i` have the single
in-neighbour `c_i` and the single out-neighbour `c_(i+1)`. A forward path between
them therefore goes once around the `c`-cycle and puts `c_j` before `c_(j+1)` for
every `j` other than `i`. One ordering thus serves at most one twin pair, and every
forward cover of `D_m` has at least `m = |V(D_m)|/3` orderings (`dc_cover_size`).
With `m = 2^k` for `k` large, this exceeds `c * floor(log2 (3m))`. The write-up asks
for `m >= 3`; the formal proof works from `m = 2`.

Caveat: the paper's other results are untouched: linear-size balanced bi-trees, and
its sketch of the conjecture for bi-oriented digraphs, a class that does not contain
`D_m`. Its binary-tree instance of the request problem is not formalized. The row's
upstream review status (open) is unchanged.

## Geodesic cycles and Tutte's theorem

For the OPG row `opg:geodesic_cycles_and_tuttes_theorem`,
`Extremal.applications.geodesic_cycles_tutte.geodesic_cycles_and_tuttes_theorem_disproved`
refutes `Extremal.conjectures.D2str.geodesic_cycles_and_tuttes_theorem_statement`, the
affirmative answer to the problem: every 3-connected finite graph has an assignment of
positive lengths to its edges for which every geodesic cycle is peripheral. A cycle is
geodesic when, between any two of its vertices, one of its two arcs is a shortest path of
the graph; it is peripheral when it is induced and its complement is connected.

The counterexample is the eight-vertex graph of the write-up generated by gpt-6-astra and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/abcc3defa6684921fe4b460174ea8b2810b5485b/attacks_opg/geodesic_cycles_and_tuttes_theorem/output.md) (committed 2026-09-16, merged 2026-09-17, MIT licence): a `K4` core `b_0..b_3`
and, for each `i`, a vertex `s_i` joined to the three core vertices other than `b_i`, one
vertex inside each face of a tetrahedron. It is 3-connected (`G8_3connected`), and
`g8_geodesic_not_peripheral` shows that every positive symmetric length assignment, over
any ordered field, has a geodesic cycle that is not peripheral. The proof follows the
write-up. A lightest closed walk with an odd number of steps in a symmetric edge set is a
geodesic cycle (`min_odd`), which replaces the write-up's generation fact and its dimension
count. Under the perturbed lengths `ell + eps * gamma`, every shortest walk is also shortest
for `ell`, and the two 2-paths over each core edge get different lengths. Every chordless cycle of the graph is a triangle, the
core triangles are not peripheral, and the parity of dual paths between two non-geodesic
faces gives the contradiction. The finite facts are checked by computation over explicit
lists of the vertices and faces.

Caveat: "peripheral" has its standard meaning, induced and non-separating, as in the row.
The literature has not been searched for this counterexample, and the row's OPG status is
unchanged.

## Heavy paths in shortest long odd holes

For source record `1904.12273__01`,
`GTMisc.applications.heavy_path_disproof.heavy_path_extension_disproved` refutes
`GTMisc.conjectures.X232.heavy_path_extension_statement`, the heavy-path extension in the
introduction of *Detecting a long odd hole* (Chudnovsky, Scott and Seymour, arXiv:1904.12273):
for every `ell >= 5` there is a bound `b` such that, whenever `C` is a shortest odd hole of
length at least `ell` and `M` is a set of `C`-major vertices one of which is nonadjacent to all
the others, some path of `C` with at most `b` edges contains a neighbour of every vertex of `M`.
A vertex is `C`-major, in the paper's sense, when it is off `C` and no three-vertex path of `C`
contains all its neighbours on `C`. "Bounded" is read as a bound depending only on `ell`.

The counterexample is the construction of the write-up generated by gpt-5.6-sol and published in [graph-theory-AI/Graph-Theory-LLM-Proofs](https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/9871a536271989364598b11974b95c7be4fe7cc2/attacks/1904.12273__01/output.md) (commit `9871a53`, 2026-08-31). For odd `q >= 3`, `G(q)` has the hole
`C` on `3q` positions, split into three arcs `A_0, A_1, A_2` of `q` edges; a vertex `y_k`
complete to `A_k`, the `y_k` forming a triangle; and a vertex `x` complete to `C` and adjacent
to no `y_k`. Let `M = {x, y_0, y_1, y_2}` and `ell = 7`. Every hole of `G(q)` has at most five
vertices (through `x`), or contains `C`, or has `2q + 2` vertices (one `y_k`) or `q + 3` (two),
so `C` is a shortest long odd hole (`hole_cases`). `x` and the `y_k` are `C`-major (`majors_hM`).
A path of `C` with fewer than `q` edges misses an arc, so a path containing a neighbour of each
vertex of `M` has at least `q` edges (`catch_bound`). Taking `q = 2b + 3` defeats every bound
`b`, and since `|M| = 4` throughout, a bound depending on `|M|` as well is defeated too. The
arcs are normalised by the rotation automorphism of `G(q)`.

Caveat: the paper states the extension inside its algorithm, for "candidate" graphs (no long
pyramid, no long jewel of order at most `ell + 2`, no long odd hole of length at most
`2 ell + 2`). The row does not state that hypothesis, and it is not encoded. That `G(q)` is a
candidate (`ell = 7`, odd `q >= 9`) is known only from a computation in the review of the
write-up, so the extension in the candidate setting stays open as far as this refutation is
concerned. The row's upstream review status (open) is unchanged.

## Regression tests

The test suite uses isolated synthetic packages and real Rocq compilation. Its
mutations cover an unrelated closed theorem, reversed polarity, a transitive
axiom, an admitted proof, stale compiled objects, changed source metadata,
statement substitution, command/path injection, duplicate entries, missing build
entries and lack of a distinct correspondence reviewer. A further compiler probe
checks that registering one proof does not exempt a second, unregistered proof
of the same statement.

The OPG tests compile one synthetic OPG resolution and reject:
- each changed identity field, and a malformed or unknown `opg:<slug>` key;
- duplicate rows, a row without `formal_name`, another package or name;
- fields of the wrong corpus.

For the statement file, frozen `Module` copies, comments, strings and unlisted
files are ignored. A second top-level definition, including one in a `Section` or a
`Local` one, is ambiguous, and malformed scopes fail closed. The selection tests
cover `--record` and `--package` in both modes. One compiled run checks and reports
only the selected entry.

The transcript tests strip one- and multi-line warning blocks, including dotted
categories such as `deprecated-since-9.2`. They refuse an unrecognised message, and a
block without its category line, which must not swallow the output that follows. One
compiled fixture re-exports `ssrnat`, as X15's imports do, and deprecates its statement. It yields
a report without `Warning:` or the probe path, although the same probe text, compiled
directly, warns.
