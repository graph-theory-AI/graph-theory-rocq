(** Frozen C7 source and complete statement declarations; baseline and exact substitutions
    are recorded in meta/migration_reports/bipartition.spec.json. *)
From GTBase Require Import base.
From Chromatic.conjectures Require Import X219.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X219Legacy.

Definition x219_bipartition (G : sgraph) (A : {set G}) : Prop :=
  forall u v : G, u -- v -> (u \in A) != (v \in A).

Definition asymmetric_bipartite_list_colouring_statement : Prop :=
  (* (i) *)
  (forall q : nat, 0 < q ->
     exists D0 : nat,
       forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
         X219Legacy.x219_bipartition A ->
         x219_max_degree_on A DA ->
         x219_max_degree_on (~: A) DB ->
         0 < kA -> 0 < kB -> D0 <= DA -> D0 <= DB ->
         DA <= kA ^ q -> DB <= kB ^ q ->
         x219_kAkB_choosable A kA kB)
  /\
  (* (ii) *)
  (exists C D0 : nat, [/\ 1 < C, 1 < D0 &
     forall (G : sgraph) (A : {set G}) (DA DB kA kB : nat),
       X219Legacy.x219_bipartition A ->
       x219_max_degree_on A DA ->
       x219_max_degree_on (~: A) DB ->
       0 < kA -> 0 < kB -> D0 <= DA -> D0 <= DB ->
       C * trunc_log 2 DB <= kA -> C * trunc_log 2 DA <= kB ->
       x219_kAkB_choosable A kA kB])
  /\
  (* (iii) *)
  (exists C D0 : nat, [/\ 0 < C, 1 < D0 &
     forall (G : sgraph) (A : {set G}) (D kA kB : nat),
       X219Legacy.x219_bipartition A ->
       x219_max_degree_on A D ->
       x219_max_degree_on (~: A) D ->
       0 < kA -> 0 < kB -> D0 <= D ->
       (C ^ kA * D * trunc_log 2 D ^ kA.-1 <= kB ^ kA \/
        C ^ kB * D * trunc_log 2 D ^ kB.-1 <= kA ^ kB) ->
       x219_kAkB_choosable A kA kB]).

End X219Legacy.

Lemma x219_bipartition_compat (G : sgraph) (A : {set G}) :
  X219Legacy.x219_bipartition A <-> x219_bipartition A.
Proof. exact: iff_sym (bipartition_neq A). Qed.
Lemma asymmetric_bipartite_list_colouring_statement_compat :
  X219Legacy.asymmetric_bipartite_list_colouring_statement <->
  asymmetric_bipartite_list_colouring_statement.
Proof.
split.
- move=> [h1 [h2 h3]]; split.
  + move=> q hq; have [D0 hh] := h1 q hq; exists D0.
    move=> G A DA DB kA kB hb.
    exact: (hh G A DA DB kA kB (proj2 (x219_bipartition_compat A) hb)).
  + split.
    * have [C [D0 [hC hD hh]]] := h2; exists C, D0; split=> //.
      move=> G A DA DB kA kB hb.
      exact: (hh G A DA DB kA kB (proj2 (x219_bipartition_compat A) hb)).
    * have [C [D0 [hC hD hh]]] := h3; exists C, D0; split=> //.
      move=> G A D kA kB hb.
      exact: (hh G A D kA kB (proj2 (x219_bipartition_compat A) hb)).
- move=> [h1 [h2 h3]]; split.
  + move=> q hq; have [D0 hh] := h1 q hq; exists D0.
    move=> G A DA DB kA kB hb.
    exact: (hh G A DA DB kA kB (proj1 (x219_bipartition_compat A) hb)).
  + split.
    * have [C [D0 [hC hD hh]]] := h2; exists C, D0; split=> //.
      move=> G A DA DB kA kB hb.
      exact: (hh G A DA DB kA kB (proj1 (x219_bipartition_compat A) hb)).
    * have [C [D0 [hC hD hh]]] := h3; exists C, D0; split=> //.
      move=> G A D kA kB hb.
      exact: (hh G A D kA kB (proj1 (x219_bipartition_compat A) hb)).
Qed.
