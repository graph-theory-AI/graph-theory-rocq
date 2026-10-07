(** * D8: finite supplied-family incidence regularity, Hypergraph certificate

    Frozen at the D7 pin 7e030f252c859c5334185673b10b69971cab9402, the family baseline of
    meta/migration_reports/regularity.spec.json.
    - [Legacy]: X73's [x73_regular], verbatim.  It keeps A10's live [x73_hyperdegree], the alias of
      [GTBase.incidence.incidence_degree]; the source now unfolds to the public
      [Hypergraph.foundations.hypergraph_regularity.hg_regular] over the same count.
    - [X73RegularLegacy]: the complete current X73 row over the frozen regularity.  It keeps the live D2
      partite and D6 matching aliases.
    The complete Original is the existing, unchanged D6
    [Hypergraph.migration.matching.X73MatchingOriginal] row (raw A10 regularity and degree, D2 partite
    source, D6 matching) with its genuine D6 iff, which the spec reuses as is. *)
From GTBase Require Import base.
Require Hypergraph.foundations.hypergraph_regularity.
Require Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.
Import Hypergraph.conjectures.X73.

Definition x73_regular (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall v : T, x73_hyperdegree E v = d.

End Legacy.

Module X73RegularLegacy.
Import Hypergraph.conjectures.X6 Hypergraph.conjectures.X73.

Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @x6_r_partite_uniform T 3 part E ->
    Legacy.x73_regular E d ->
    exists M : {set {set T}},
      x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

End X73RegularLegacy.

(** Both bridges are conversions: the live regularity unfolds to the same incidence count. *)

Lemma x73_regular_compat (T : finType) (E : {set {set T}}) (d : nat) :
  @Legacy.x73_regular T E d <->
  @Hypergraph.conjectures.X73.x73_regular T E d.
Proof. exact: iff_refl. Qed.

Lemma regular_tripartite_hypergraph_matching_lower_bound_statement_compat :
  X73RegularLegacy.regular_tripartite_hypergraph_matching_lower_bound_statement <->
  Hypergraph.conjectures.X73.regular_tripartite_hypergraph_matching_lower_bound_statement.
Proof. exact: iff_refl. Qed.
