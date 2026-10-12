# A33: strongly regular graphs

`GTBase.strongly_regular` owns the unguarded `strongly_regular_parameters G k lam mu` and two distinct
existentials: `has_strongly_regular_parameters` (no guard) and `connected_nontrivial_strongly_regular`
(exactly `connected [set: G]`, `0 < k` and `k < #|G|.-1`). Only guarded implies unguarded.
The public client covers K2 with (1,0,0), the empty graph (every triple, vacuously) and K2,2 with (2,0,2);
K2 and the empty graph fail the guards. GTBase does not import Spectral.

Hom U3 `srg`/`strongly_regular` convert to the clauses and to the unguarded existential, so
K2 (`grounding_U3.srg_K2`) and the degenerate graphs stay accepted. Spectral D5 `strongly_regular`, one
flat five-conjunct existential, is a proved iff with the guarded wrapper; K2,2 (`grounding_D5.sr_K22`)
stays in. Both whole statements keep their quantifiers, providers and the eight-graph non-isomorphism clause.

The matrix identity `A^2 = k I + lam A + mu (J - I - A)` over int, introduced in `grounding_D5`, is
released as `Spectral.foundations.strongly_regular_matrix`: equivalent to the clauses for all parameters,
and with the same guards to the guarded existential. Every `grounding_D5` qualified name keeps its
type and arguments: `sr_clauses`, `sr_mateq` and `strongly_regular_alg` are aliases, the support lemmas,
`sr_mateqE` and `strongly_regularE` are proved wrappers.

Eight rows are frozen at the literal parent `a69e27f`; their bodies are byte-identical to `a59246d` (U3),
`7c23ef2` (D5) and `9c47cd0` (the grounding matrix block). Six source definitions and two whole statements
are certified, and the two frozen grounding theorems hold of the frozen bodies. No SRG name or `common_nbr`
occurs in any migration module at the parent. That is scoped search evidence, not proof that no equivalent
body was frozen elsewhere; the provider/history scan is part of the gate evidence.

Mappings and notes: `meta/migration_reports/strongly_regular.spec.json`. Reproduce with the public client,
the `strongly_regular` kernel report and the normal routes `U3 homomorphism-theory`, `D5 spectral-graph-theory`.
Evidence: `coordination/evidence/A33-strongly-regular/`. Independent review: Marcol.
