# C8: monochromatic subsets under a supplied map

This family migrates three definitions to `GTBase.monochromatic.monochromatic_on`,
on baseline `47eed16`. The five complete reaching statements keep their original
bodies, guards, documentation and statuses. The family is awaiting independent
step-10 and coordinator statement review; the registry leaves `reviewed_by` unset.

The authoritative source list and public-source pin are in
`meta/library_primitives/monochromatic.json`. The compact report
`meta/migration_reports/monochromatic.md` is regenerated from its adjacent spec by
`python3 meta/migration_report.py monochromatic --write`; optional detailed JSON
belongs outside that report directory.

## Contract and upstream choice

The canonical predicate says that every two members of a supplied finite subset
receive equal colours under a supplied map. Its domain is any `finType` and its
palette any `eqType`; neither a graph nor a finite or inhabited palette is needed.
It is exactly MathComp `constant` applied to the sequence of colours on `enum S`.
The reflection proof uses pairwise equality without the default palette element
required by the existing `constantP` view. The map and colour labels remain data.

Empty sets and singletons are monochromatic; an empty domain with an empty palette
is admitted. Values outside the subset do not matter. A negative reflection gives
two subset members with different colours, without adding nonemptiness or palette
inhabitance assumptions. The public API also provides restriction, extensionality,
injective relabelling, a two-element characterization and constant-map lemmas.
Its public-only client checks positive, negative and empty-palette cases.

| Source | Original interface | Migration |
| --- | --- | --- |
| `Chromatic.conjectures.X181.x181_monochromatic` | Boolean bounded pairwise forall, ordinal palette | Boolean equality to the canonical predicate |
| `GTMisc.conjectures.U13.monochromatic` | Prop pairwise equality, Boolean palette | Reflected Prop adapter, proved iff |
| `GTBase.surface.same_colour_on` | Public Prop pairwise equality, ordinal palette | Public reflected adapter, proved iff |

The public source is enrolled explicitly at immutable pin `2e0fb67`, with its
regular Git blob and declaration hash. Its body at baseline `47eed16` is identical.
It is not classified as a non-corpus source: its full foundation-to-statement
closure contributes X138, X194 and X218. The existing foundation fidelity warning
for graph-local `clustered_chromatic_at_most` remains unchanged.

## Complete closure and preserved distinctions

All sixteen statement-reaching declarations are frozen: three source predicates,
eight intermediate definitions and five complete rows. Two further public/non-row
contracts are frozen too: `clustered_chromatic_at_most` and X138's unused
`x138_clustered_two_colourable`. Each original body is checked against its pinned
source with only explicit substitutions to frozen family dependencies. Nineteen
certificates cover those eighteen objects and the X181 event-weight transport.

| Row | Preserved contract |
| --- | --- |
| X181 random graph clique chromatic constant | Maximal cliques of size at least two; finite-function colourability, the full numeric window and probability/eventual chain; existing partial upper-half proxy |
| U13 two-colouring maximum cliques | Maximum-cardinality cliques, Boolean map, positive vertex count and exclusion of induced odd cycles of length at least five |
| X194 clustered minor class | `2 <= k`, supplied treedepth premise and one clustering bound before quantification over all graphs |
| X218 odd-minor defective/clustered bound | The entire conjunction, minimal connected-treedepth premises, `k - 1` and all existing blocked placeholders |
| X138 surface clustered two-colouring | Uniform clustering bound, girth/degree premises, connectedness and the existing orientable-only partial surface scope |

U13's four grounding lemmas and X218's two grounding consumers keep their exact
types. Only the U13 proofs need reflection adaptations. No earlier committed
migration snapshot reaches these sources at this baseline; previous family
certificates and histories stay unchanged.

Monochromatic paths, connected sets in an edge-colour relation and injective
monochromatic graph/hypergraph copies have extra graph and witness structure.
They remain distinct, recorded with their concrete source names in the spec.
Hypergraph X209's cut-edge predicate is also outside this family; the generic
negative reflection is available for a future explicit bridge.

## Separate re-audit concern

Readback raises a possible U13 singleton issue: its positive-vertex guard permits
`K1`, whose singleton maximum clique cannot split into two colours, while its
long odd-cycle exclusion appears vacuous. This is an unproved concern recorded
for a separate statement re-audit. C8 neither changes this encoding nor imports
X181's clique-size guard, and makes no claim to repair the row.

## Protocol and validation

Discovery, semantic comparison, upstream audit, generic specification, reusable
implementation and public grounding precede frozen-body/equivalence certificates.
All five complete statement iff types, discharged Section/domain parameters,
closed assumptions and strict compiled frozen/live closures are checked through
the pinned toolchain. These are logical equivalences, not proof-term identity
claims. The report checks the full corpus closure and original hashes.

Gate and review results are recorded against the eventual exact commit on BOARD.
Detailed implementation evidence is kept outside committed meta at
`coordination/evidence/C8-monochromatic-by-matching-scope/`. Compatibility names
remain transparent aliases for the migration cycle; `same_colour_on` remains a
public adapter. The registry's three remaining consumers are their three direct
same-file consumers.
