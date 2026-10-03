# C9: ordinary chi-bounded graph classes

This family starts at reviewed A6 `0659592`. It migrates five sources, including
the public `Chromatic.foundations.chi_bounding.chi_bounded_class`, with ten whole
statement equivalences (nine corpus rows and one genuine rowless declaration)
and a complete A6/C9 X3 Original. Independent step-10 and coordinator final
statement review approved exact `5f8211a10b7260fec67dad1450be6da41efeb1a9`; see
`meta/migration_reviews/chi_bounded.md`. Cumulative integration and normal
milestone gates remain separately reported.

Authoritative inputs are `meta/library_primitives/chi-bounded.json` and
`meta/migration_reports/chi_bounded.spec.json`. Regenerate the compact report with
`python3 meta/migration_report.py chi_bounded --write`; request detailed evidence
outside the report directory with `--details /tmp/c9-details`.

## Mathematical contract and ownership

One arbitrary function `f : nat -> nat` is chosen BEFORE every member of a class,
with ordinary `chi(U x) <= f(omega(U x))` for the explicitly supplied underlying
simple graph `U x`. The indexing type can be infinite or empty; each graph is
finite. Neither the function nor the class needs monotonicity, heredity or
isomorphism closure. This is ordinary chromatic boundedness as a function of
clique number, not dichromatic, polynomial or constant boundedness.

`GTBase.chi_bounding.chi_bounded_via` states that contract and
`chi_bounded_class` is its identity-map specialization. The home is GTBase because
both Chromatic and Digraph need it; the module imports only MathComp and the
upstream graph primitives, so it creates no base/area import cycle. The existing
Chromatic public name stays public as an adapter. The pinned upstream library has
chi, omega, chi0 and leq_chi, but no class chi-boundedness predicate; the existing
Chromatic foundation supplies the faithful simple-graph contract reused here.

| Source | Representation and bridge |
| --- | --- |
| U8.chi_bounded | simple graph class, convertible identity specialization |
| X112.x112_chi_bounded | same via convertible x112_omega |
| Chromatic.foundations.chi_bounding.chi_bounded_class | same public contract, explicitly enrolled repository source at0659592 |
| X170.x170_chi_bounded | class of existing oriented records, supplied x170_underlying map, convertible |
| Digraph.chi_bounded.chi_bounded_under | ordinary underlying chi/omega of diGraphType; the explicit `0 < #|G|` guard remains in the filtered class, with an iff for the conjunction adapter |

The simple-graph wrappers allow empty members. The guarded Digraph wrapper keeps
its original nonempty-member premise. A separate public lemma proves chi(empty)
fits any supplied bound; that fact is not used to remove a guard from a source.
The Digraph underlying graph still removes loops and forgets direction through
the original urel/SGraph; X170's existing oriented record stays unchanged.

## Complete statements and history

All five original source bodies are frozen. There are no intermediate reaching
helper definitions to omit. The ten complete statements are:

- U8 forbidden-induced-tree chi boundedness and vertex-minor-closed proper classes.
- X3 hereditary chi-bounded but non-polynomial classes, complementation chi
  boundedness, and the alpha/omega large-class bound.
- X112 closure under substitution and bounded-size gluing, preserving both sides
  of the implication and the existing whole closure inductive.
- X170 oriented-P4 forbidden families, preserving the known defective exceptional
  codes and BLOCKED leg exactly.
- Digraph conj2 (the entire oriented-forest iff), conj4 (oriented stars), and
  conj5 (all three forbidden-family premises and the class conclusion).

Digraph conj5 has no manifest binding and is explicitly non-corpus. The corpus's
arxiv:1605.07411#02 belongs to X170's different, blocked encoding; no equivalence
between those two encodings is claimed. All nine row bodies, doc blocks, leg
states, statuses and implication dispositions are unchanged.

A6 previously froze the X3 complement image while retaining live chi_bounded.
C9's migration-time X3 snapshot freezes chi_bounded while retaining live
complement_image. Both remain: a new `X3Original` uses A6's existing frozen
complement image and C9's frozen chi-bound, with its own complete iff certificate.
Reciprocal notes document the two partial snapshots. Every earlier A6 frozen body
and theorem type is retained, including its raw relation/proofs/SGraph package.
The old A6 proof now explicitly unfolds the two canonical chi-bounding adapters
before applying its existing complement equivalence. No proof-term identity
claim is made.

## Public API and proof consumers

The API provides empty and bounded-order classes, subclass restriction,
pointwise class equivalence, finite union using the sum of two bounds,
representation-image transport, and the empty-graph corner. A conditional
obstruction takes an actual supplied unbounded-chi family at one fixed clique
number; it does not assert such a family exists. The public-only client also
checks K0, a bounded one-vertex class and the concrete failure of a zero bound on
K1, clearly distinguishing a wrong witness from an unbounded class.

Twelve existing proof consumers retain exact types: two U8 grounding lemmas,
the public polynomial-to-general bridge, four verified Chromatic implications,
three Digraph grounding lemmas, the conditional conj2-to-conj4 implication (with
its star-is-forest premise), and A6's X3 compatibility theorem. Atlas A2's related
candidate/blocked edge metadata remains unchanged. Import/module-prefix tokens
such as `chi_bounded.underlying` are not uses of U8's same-spelled predicate.
The directed bounded-order grounding proof destructs the explicit conjunction
instead of taking the two former curried assumptions; its theorem type is
unchanged. Certificates use the filename `chi_bounded_classes.v` to avoid
colliding with Digraph's existing short-import module `chi_bounded.v` under `-R`.

Polynomial wrappers (X3, X124 and the public monomial form), the existing
poly_forms conversions, constant chromatic boundedness, dichromatic predicates
and X52's Mader threshold stay separate. Their old declarations are unchanged.

## Protocol and validation

Discovery, source comparison, generic contract, upstream audit, reusable API and
public grounding precede the verbatim legacy copies and complete equivalences.
All source/Section/domain types, eleven complete iff types, closed assumptions
and strict frozen/live dependency closures require pinned-kernel probes and
independent review. The complete Original must avoid both live C9 and live A6
vocabulary, while retaining all class witnesses and guards.

Source, kernel, audit and milestone results are announced against the stable pin
on BOARD and archived outside committed meta under
`coordination/evidence/C9-chi-bounded-by-matching-scope/`. A normal Digraph X1
milestone remains required; no expensive whole-Digraph build is duplicated before
safe complete artifacts are available. Aliases remain for the compatibility
cycle and the existing foundation name remains public. Eight same-file direct
consumers remain, including the public polynomial-to-general bridge.

Before pinning, focused project builds covered 58 C9/client/consumer source
targets, followed by 34 additional forced A6/B1 history targets. Checks passed:
51 closed assumptions; 29 exact type/conversion probes including all eleven
whole iff declarations; 23 strict family dependency closures; and the separate
B1 X52 closure showing that its module-prefix reference reaches the unchanged
underlying graph, not a C9 predicate. The family kernel report passes 248 checks
and the full A6 complement kernel report passes 433 checks on these combined
sources. The preservation check protects 2,018 predecessor files and verifies
both proof-only edits and every earlier A6 declaration/theorem type.
