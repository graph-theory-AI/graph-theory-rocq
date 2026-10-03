(** Frozen C7 source and complete statement declarations; baseline and exact substitutions
    are recorded in meta/migration_reports/bipartition.spec.json. *)
From GTBase Require Import base.
From Packing.conjectures Require Import U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module U9Legacy.

Definition del_bipartite (G : sgraph) (S : {set {set G}}) : Prop :=
  exists A : {set G},
    forall x y : G, x -- y -> [set x; y] \notin S -> (x \in A) != (y \in A).

Definition odd_cycle_transversal_in_triangle_free_graphs_statement : Prop :=
  forall G : sgraph,
    triangle_free G ->
    exists S : {set {set G}},
      [/\ S \subset edge_setG G,
          #|S| <= (#|G| ^ 2) %/ 25
        & U9Legacy.del_bipartite S].

End U9Legacy.

Lemma del_bipartite_compat (G : sgraph) (S : {set {set G}}) :
  U9Legacy.del_bipartite S <-> del_bipartite S.
Proof. exact: iff_sym (bipartite_after_deletionP S). Qed.
Lemma odd_cycle_transversal_in_triangle_free_graphs_statement_compat :
  U9Legacy.odd_cycle_transversal_in_triangle_free_graphs_statement <->
  odd_cycle_transversal_in_triangle_free_graphs_statement.
Proof.
split=> h G hg; have [S [sE sb hb]] := h G hg; exists S; split=> //.
- exact: (proj1 (del_bipartite_compat S) hb).
- exact: (proj2 (del_bipartite_compat S) hb).
Qed.
