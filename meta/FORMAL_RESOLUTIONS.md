# Formal resolutions

`formal_resolutions.json` records local, kernel-checked proofs separately from the
upstream conjecture catalog. Its source statuses, manifests, snapshots and
statement-formalization legs remain unchanged. A source row can therefore still
say `open` or `partial` while this registry records a checked proof or disproof.

Run the proof checks with a compatible installed Rocq/opam switch:

```sh
ROCQ_OPAM_SWITCH=rocq-tools make resolutions
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/test_formal_resolutions.py
```

On the development machine, `rocq-tools` provides Rocq 9.1.1 built with OCaml
5.3.0, matching the existing graph library objects. The historical `digraph`
switch also provides Rocq 9.1.1 but was built with OCaml 5.2.1, so it cannot read
those objects. `ROCQ_OPAM_SWITCH` accepts either a switch name or an absolute
switch directory. With no override, the existing historical default is retained.

The checker builds the registered statement/proof targets with the package's
generated Makefile, then recompiles the actual registered source files and a
fresh probe. Local package dependencies named by load-path flags are built
first; external libraries must be available under the selected switch. `make gate` includes the
resolution checker. `make audit` checks metadata only and explicitly reports that
proofs were not checked.

## What an entry establishes

Each entry copies the source row identity, text, locator and source hash from the
pinned corpus manifest. It names a statement file and a fully qualified
proposition, the statement declaration's SHA-256 digest, a proof file and a fully
qualified theorem, and the direction `prove` or `disprove`. Both source files
must be listed in their package's `_CoqProject`, and the qualified names must
match the files' load-path mappings. Existing formalized rows must use their
original statement location and formal name.

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

## Regression tests

The test suite uses isolated synthetic packages and real Rocq compilation. Its
mutations cover an unrelated closed theorem, reversed polarity, a transitive
axiom, an admitted proof, stale compiled objects, changed source metadata,
statement substitution, command/path injection, duplicate entries, missing build
entries and lack of a distinct correspondence reviewer. A further compiler probe
checks that registering one proof does not exempt a second, unregistered proof
of the same statement.
