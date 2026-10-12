(** A33 strongly regular parameters (Hom): the frozen U3 parameter clauses, the frozen UNGUARDED existential and the
    cores row.  [srg] and [strongly_regular] convert to [GTBase.strongly_regular.strongly_regular_parameters] and
    [has_strongly_regular_parameters]: no connectivity or degree guard is added, so [K_2] (grounding_U3.srg_K2), the
    empty graph, complete graphs, edgeless graphs and disjoint unions of cliques remain accepted.  The live [hom_equiv],
    [is_core] and ['K_n] are unchanged.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/strongly_regular.spec.json. *)
From GTBase Require Import base strongly_regular.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition srg (G : sgraph) (k l m : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_nbr x y| = l)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_nbr x y| = m)].

Definition strongly_regular (G : sgraph) : Prop :=
  exists k l m : nat, Legacy.srg G k l m.

End Legacy.

Module U3Legacy.

Definition cores_of_strongly_regular_graphs_statement : Prop :=
  forall G : sgraph, Legacy.strongly_regular G ->
    is_core G \/ exists n : nat, hom_equiv G 'K_n.

End U3Legacy.

(** ** Source and full-statement certificates (conversion). *)

Lemma u3_srg_compat (G : sgraph) (k l m : nat) :
  Legacy.srg G k l m <-> srg G k l m.
Proof. exact: iff_refl. Qed.

Lemma u3_strongly_regular_compat (G : sgraph) :
  Legacy.strongly_regular G <-> strongly_regular G.
Proof. exact: iff_refl. Qed.

Lemma cores_of_strongly_regular_graphs_statement_compat :
  U3Legacy.cores_of_strongly_regular_graphs_statement <-> cores_of_strongly_regular_graphs_statement.
Proof. exact: iff_refl. Qed.
