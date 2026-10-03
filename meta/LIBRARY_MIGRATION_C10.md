# C10: closure properties of graph classes

This family begins at C9 `5f8211a`. It combines the three repeated hereditary
class definitions with their two exclusive isomorphism-closure prerequisites.
It preserves three separate contracts; it does not identify induced closure
with the stronger conjunction. Step-10 and coordinator final review are pending.

The authoritative inputs are `meta/library_primitives/hereditary-class.json`
and `meta/migration_reports/hereditary_class.spec.json`. Regenerate the compact
report with `python3 meta/migration_report.py hereditary_class --write`; use
`--details /tmp/c10-details` for verbose evidence outside the report area.

## Contract and public home

All classes have type `sgraph -> Prop` with no inhabitance, properness or
decidability assumption. `GTBase.graph_classes.iso_closed` transports membership
along the upstream `diso` witness. `induced_closed` requires membership for every
literal induced subset, including the empty subset. `hereditary_class` explicitly
conjoins these two properties. Three areas use this vocabulary, so GTBase is the
shared home; it imports only MathComp and upstream graph primitives.

The exact five source definitions are:

| Source | Preserved contract |
| --- | --- |
| Chromatic.X3.x3_iso_closed | inhabited(diso) before membership; iff to the explicit-witness canonical |
| Minor.X220.x220_iso_closed | membership before a diso witness; convertible canonical |
| Chromatic.X3.x3_hereditary_class | iso closure AND induced closure; iff through the first adapter |
| Minor.X220.x220_hereditary_class | iso closure AND induced closure; convertible canonical |
| Packing.X155.x155_hereditary_class | induced closure ONLY; convertible to induced_closed, never the stronger canonical |

The two iso-closure sources are used only by the two strong hereditary sources;
they are included as dependencies in this whole family. X155's old name remains
a compatibility alias to the weaker interface. No converse from induced closure
to strong hereditary closure is asserted without an iso-closure premise.

Upstream `diso` is a Type-valued bijection with both edge-preservation directions;
it is not graph equality or a Boolean. Packing/unpacking `inhabited` uses ordinary
implication proofs, with no propositional/function extensionality. Upstream
`GraphTheory.dom.hereditary` concerns Boolean predicates on subsets of one fixed
finite type and is a different contract. Existing local Minor conveniences
`diso_card` and `card_induced` are not imported into GTBase: the API uses upstream
bijection cardinality and the literal induced subtype directly.

## Complete statements and history

All five source bodies and three whole corpus statements are frozen:

- X3's hereditary chi-bounded but non-polynomial class: the same existential
  class and conjunction, corpus status solved, statement leg done.
- X220's Small Conjecture: hereditary AND small before one uniform twin-width
  bound, corpus status disproved, statement leg done.
- X155's identifying-code/approximation dichotomy: the full disjunction and all
  existing complexity clauses, corpus status open, statement leg BLOCKED.

X155's documented empty-class refutation and missing VC-dimension antecedent
remain untouched. The migration introduces no guard or statement repair. External
focused evidence reproduces the existing empty-class reasoning for the frozen
and live statements; it is not a new formal-resolution entry.

C9's `chi_bounded_classes.X3Legacy` snapshot freezes chi-boundedness but retains
live hereditary closure. Its body and theorem type stay unchanged. C10's partial
snapshot freezes closure but retains live chi-boundedness; a complete
`graph_classes.X3Original` composes the frozen closure with C9's existing frozen
chi-bounded predicate. It preserves the same existential class and polynomial
negation and has its own full iff certificate. Reciprocal spec notes distinguish
the two partial snapshots. The existing `x3_iso` wrapper is unchanged, so A6's
complement history and C9's complementation Original remain outside this scope.

The three Minor X220 grounding theorems (zero-order class, Small Conjecture
nonvacuity, and exact-two-vertex guard failure) retain their exact types/proofs.
The e078 implication annotation stays refuted-direction; no new implication is
claimed. All original row bodies, doc blocks and statuses are preserved.

## API, public clients and validation

The API supplies explicit projections/assembly, isomorphism transport, pointwise
class iff, unions/intersections, empty/all classes and bounded-order classes.
A concrete obstruction rejects the positive exact-order class by taking the
empty induced subset. The public-only client includes an iso-closed class of
exactly two vertices that fails induced closure, plus empty/universal/zero-order
cases. No conjecture or area-foundation import is used by that client.

Keep ordered adjacency-table hereditary classes, vertex-minor closure, the two
different proper-minor-closed-class contracts, perfect graphs and fixed-host
hereditary subset predicates separate. They are recorded as intentional variants
where relevant; none is silently strengthened.

Pinned-kernel checks must cover five source adapter types, the actual diso and
inhabited representation, all four complete row iff types, assumptions, strict
source/statement closures, complete C9/C10 history, and the unchanged A6/C9
complement closure. Preservation checks protect all predecessor bodies, theorem
types, metadata review fields and statuses. Normal affected milestones are
Chromatic X3, Minor X220 and Packing X155. Results and exact source hashes are
archived in `coordination/evidence/C10-graph-classes-by-matching-scope/` and
announced on BOARD against the stable pin. Three same-file row consumers remain;
all five compatibility names are retained for the deprecation cycle.

Before pinning, the focused source closure passed 35 project targets, with ten
additional directed targets for the full C9 history kernel report. Checks passed:
40 closed assumptions (including two external frozen/live X155 refutations),
33 exact type/conversion probes, seventeen strict family dependency closures and
two unchanged A6/C9 complement-history closures. The C10 kernel report passes
99 checks and the complete C9 kernel report passes 249 on the combined sources.
The preservation check protects 2,029 predecessor files and verifies the exact
five redirects, all unchanged prior proof scripts/types and the one additive
reciprocal history note.
