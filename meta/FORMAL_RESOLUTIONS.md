# Formal resolutions

`formal_resolutions.json` records local, kernel-checked proofs separately from the
upstream conjecture catalog. Its source statuses, manifests, snapshots and
statement-formalization legs remain unchanged. A source row can therefore still
say `open` or `partial` while this registry records a checked proof or disproof.

The registry holds seven entries:

| Record key | Direction | Result (section below) |
|---|---|---|
| `1611.03196__03` | prove | Fair representation by matchings (X15) |
| `1812.02420__03` | disprove | Directed Kneser nonexistence |
| `2103.15175__00` | prove | List Ramsey numbers |
| `2209.09107__00` | disprove | Alon–Tarsi orientation counterexample |
| `2310.04265__09` | disprove | Question 5.9 |
| `2408.02400__00` | prove | Chromatic and cochromatic gap |
| `2512.10438__00` | prove | Color-avoiding tournament paths |

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
the successful probe output.

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
- Parity is repaired by removing the first bead of each odd type.

The construction, its deviations from the attack write-up and the constant are
described in `packing-theory/docs/X15_FAIR_MATCHING_REPORT.md`. The correspondence
was reviewed independently on 2026-10-23.

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
