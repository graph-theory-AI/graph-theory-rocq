# Formalization journal

## 2026-09-05 — Scope and baseline

The goal is to add checked Rocq proofs for the list Ramsey equality (2103.15175__00), the nine-vertex color-avoiding tournament construction (2512.10438__00), and the chromatic/cochromatic gap family (2408.02400__00), and link the existing tournament criticality proof (2310.04265__09).

The destination is `graph-theory-rocq`. It contains substantial pre-existing uncommitted work. Its initial status and tracked diff were recorded in temporary staging; changes will be additive and will preserve that work. Source catalog status is historical data and will not be silently changed into a formal-proof status.

Development uses Rocq 9.1.1 in the `digraph` opam switch and MathComp. The root agent owns the single rocq-evolve proof session. Independent agents develop the tournament and cochromatic proofs with normal compiler calls, and a third agent audits integration gates. Successful interactive steps must be saved to source files and compiled normally; diagnostic admission of a failed proof never counts as completion.

Acceptance requires an exact formal statement, a complete proof, ordinary compilation, a theorem assumptions report, and source correspondence. Existing Python computations are reference checks, not trusted proof evidence.

## Toolchain discovery

The first import check exposed mixed compiled artifacts: parts of the destination were built with OCaml 5.3.0, while the historical `digraph` switch uses 5.2.1. The installed `rocq-tools` switch provides Rocq 9.1.1 with OCaml 5.3.0 and loads the directed foundations. Some chromatic artifacts instead use 5.2.1; the chromatic worker rebuilt the unchanged source dependency chain in staging. Integration will provide an explicit switch override and rebuild affected sources.

## First completed proof components

The existing Question 5.9 family now has a checked exact bridge proving `~ question_5_9_statement`. The bridge takes a hypothetical bound `ell`, chooses the existing 3-critical tournament larger than `ell 3`, and contradicts the requirement for a small subtournament of clique number at least 3. Its assumptions report is closed under the global context.

For list Ramsey, `lr_agree_card`, a finite union bound, and `lr_pick_label` were developed through rocq-evolve and saved as ordinary source. The first attempts exposed three routine MathComp issues: family predicates use a membership wrapper, `eq_bigr` forgets sequence membership (replaced with `eq_big_seq`), and typed set unions require the finite carrier argument. The complete file now compiles normally.

`lr_separation_seq` proves the greedy construction by induction on a duplicate-free vertex sequence, including empty sequences and empty constraint sets. `lr_product_bound` uses injectivity into a finite function space. Together they prove the least forcing order is `s^k+1` for `s>=2`, `k>=1`. The formal Ramsey number is characterized by existence and minimality, without assuming a decidable unbounded search. Graph-chromatic and arbitrary-natural-palette correspondence remain to be completed before registering the theorem as a source-matched resolution.


## List Ramsey: completing the source-level meaning

The finite-palette lemma was not yet the paper's statement. Two bridges completed the formalization. First, flatten the finitely many natural-number edge lists and take one plus their maximum; this embeds every used color into a finite ordinal palette without changing list membership or cardinality. Symmetry is required of membership, so the order of an edge's list may differ between its two orientations.

Second, connect vertex labels to the existing graph library's chromatic number. Proper ordinal colorings and stable partitions give both directions of the equivalence. The monochromatic graph is loopless and symmetric, with a proved exact adjacency characterization. A finite support argument handles arbitrary natural colors, including unused colors. These arguments were developed with rocq-evolve, saved to ordinary `.v` files, and compiled normally.

The final `list_ramsey_chromatic_resolution` now states the exact least forcing order `s^k+1` for every `s>=2`, `k>=1`, using the graph library's chromatic number and arbitrary natural-number edge lists. Both its statement and theorem have closed assumptions. An independent agent reviewed the formal definitions against the source statement.

## Cochromatic gap: from a seed to every parameter

The proof uses the 13-vertex complement of the circulant graph with differences 1, 5, 8, 12. Direct finite-set enumeration and then ordinal-based enumeration were too expensive. A plain natural-number checker over `iota 0 13`, together with a proved bridge to the actual graph, checks the absence of a five-clique and an independent triple in seconds.

A general fiber-counting inequality and explicit colorings prove that this seed has clique number 4, chromatic number 7 and cochromatic number 4. The optimal cochromatic coloring contains an independent class, needed to extend it through the Mycielski construction.

For the general reduction, select the shadow of a vertex precisely when the old vertex has the root's color. This gives an induced copy avoiding the root's color and proves the ordinary and cochromatic lower bounds. Explicit extension colorings give matching upper bounds. Iteration preserves clique number four and increases both coloring numbers by one.

The stronger theorem `gap_graph_parameters n` proves the exact triple `(4, n+4, n+7)`. Taking `n=k-4` proves the unchanged existing X7 statement for every `k>=5`. All six final modules compiled under their destination namespace; `Print Assumptions` was closed, and the worker's separate `rocqchk` check passed. Root independently reviewed the construction and exact source-statement bridge.

## Tournament: a complete universal benchmark

The witness uses nine vertices and six colors. Its tournament follows the natural order except for the reversed arc between vertices 3 and 5, which gives an explicit directed triangle. An explicit seven-vertex avoiding path supplies the lower bound; a finite search and a proved completeness lemma rule out all longer simple avoiding paths. The formal statement counts path length in vertices, whereas the underlying `dipath x s` represents the number of arcs by `size s`.

The comparison must hold for every coloring of the transitive tournament. The proof reads the eight consecutive edge colors. Deleting an endpoint works when a color is absent; otherwise deleting a suitable internal vertex leaves two missing colors before adding the one chord, so one color remains absent whatever the chord color is. An explicit transitive coloring supplies the matching upper bound of eight vertices.

The first search eagerly evaluated recursive branches under `&&`; explicit `if` expressions made the same proved computation much faster. The full `6^8` word certificate was checked, but VM reduction and kernel validation each took roughly 135 seconds, and a later script error prevented that draft module from completing. A proved invariance under color involutions reduced all words to suffixes `00` and `10`. The two `6^6` certificates compile, including kernel checking, in about 17 seconds together.

A final SSReflect `exact:` call spent excessive time inferring arguments through reducible checker premises. Supplying the sequence argument explicitly with ordinary `exact` made elaboration immediate. No unchecked cast or assumed certificate was used.

The final theorem proves a nontransitive witness with longest avoiding path seven vertices and exact transitive minimum eight. Thus it answers the source existential question at `q=6`, `N=9`. Independent source review checked the original paper's vertex-count convention and nontransitivity condition. All five modules compiled and nine audited theorem dependencies had closed assumptions.

## Integration: accepting proofs without weakening the statement gate

The existing faithfulness gate deliberately rejected exact proofs of source rows still marked open. A separate `formal_resolutions.json` registry now records checked local resolutions while preserving the pinned source catalog. An entry binds the original source identity, text and hash; formal statement and declaration hash; exact theorem; direction; and separate implementation and source-review identities. The reviewers here are other agents, not human referees.

The checker builds the registered dependency closures, recompiles the registered sources, checks the exact theorem type, and requires closed assumptions for both proposition and proof. Only the verified `(statement, theorem, direction)` triple is exempted from the gate's existing exact-type probes. A second unregistered proof remains subject to those probes. Metadata-only validation grants no proof exemption.

Compiler mutation tests caught macOS temporary-path canonicalization differences and verified rejection of admissions, extra axioms, wrong polarity or type, stale objects, statement substitution, and source drift. A dependency-build test ensures unrelated unfinished sources do not prevent checking the registered proof closure. All 14 tests passed in the actual destination repository.

Automatic approval review rejected an attempted bulk copy of integration files because the destination contained existing local edits. The safe replacement was a minimal patch against the current files, checked with `git apply --check` before applying it. This preserved the existing work. The three package project files received only the new module entries. No source catalog, original conjecture statement, manifest, snapshot or overlay was changed by this work.

## Final verification in the destination

All four entries passed the live resolution checker in `graph-theory-rocq`, including normal compilation and exact-type checks. The saved [assumptions report](ASSUMPTIONS.txt) contains two closed-context reports per entry, one for the statement and one for the theorem. The Question 5.9 entry reuses the existing construction and adds its exact negated-statement bridge; it is not a newly discovered counterexample family.

The chromatic X7 milestone passed all 11 acceptance checks: the package compiled, its five statement assumptions were clean, registered resolutions were verified, and the remaining faithfulness probes stayed active. The new proof-checker test suite passed all 14 tests.

A separate `rocqchk -silent` run checked all four final modules and their imported proof objects in the destination and exited successfully. No admission, axiom or unchecked-cast escape was introduced in the delivered proof sources.

The full `make audit` stopped at an existing `meta/dependency_graph.json` drift. Independent read-only extraction identified the precise cause: the legacy implication-theorem count is 50 in the saved graph and 52 in the current sources, because `long_dipath.v` already adds `conj1_implies_delta5` and `conj1_implies_delta6`. That file is byte-identical to its initial tracked diff. All 46 federation edges and totals are unchanged. The extractor reads 386 tracked inputs, none of which this work changes. This is a repository-wide audit limitation, separate from the successful checks of the four resolutions. The unrelated metadata was left for its ongoing owner to reconcile.

The preservation audit compared all 74 initial dirty tracked-file diffs. Before adding the final README link, 68 were byte-identical and exactly six had our intended additive integration changes. All 19 initial untracked status entries still existed. The baseline records names rather than contents for untracked files, so that artifact alone cannot prove their byte-level preservation; the two pre-existing untracked helper files touched here were updated through reviewed minimal patches.

Reproduction commands and theorem links are in [README.md](README.md) and [../FORMAL_RESOLUTIONS.md](../FORMAL_RESOLUTIONS.md). Build artifacts are local; the journal and assumptions transcript document this run, while the live checker remains the authority for future edits.
