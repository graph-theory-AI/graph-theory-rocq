(** Public-only clients of the finite bipartition API. *)
From GTBase Require Import base.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example boolean_interface_is_convertible (G : sgraph) :
  bipartite_relation (@edge_rel G) = bipartite G.
Proof. by []. Qed.
Example zero_relation (T : finType) :
  bipartite_relation (fun _ _ : T => false).
Proof. exact: bipartite_relation0. Qed.
Example a_loop_prevents_bipartiteness (T : finType) (r : rel T) (x : T) :
  r x x -> ~ bipartite_relation r.
Proof. exact: bipartite_relation_loop. Qed.
Example empty_graph_empty_side : @bipartition 'K_0 set0.
Proof. by move=> x y; move: (ltn_ord x); rewrite ltn0. Qed.
Example supplied_part_complement (G : diGraph) (A : {set G}) :
  bipartition A -> bipartition (~: A).
Proof. exact: (proj1 (bipartition_complement A)). Qed.
Example balanced_zero : @balanced_bipartition 'K_0 set0 set0 0.
Proof.
split; first by rewrite disjoints_subset sub0set.
split; first by apply/setP=> x; move: (ltn_ord x); rewrite ltn0.
split; first by rewrite cards0.
split; first by rewrite cards0.
by move=> x y; move: (ltn_ord x); rewrite ltn0.
Qed.
Example part_sizes_zero : bipartition_sizes 'K_0 0 0.
Proof.
apply/bipartition_sizesP; exists set0, set0.
by have := (proj1 (balanced_bipartitionP set0 set0 0)) balanced_zero.
Qed.
Example complete_bipartite_side n m :
  @bipartition (KB n m) [set x : KB n m | is_inl x].
Proof.
apply/bipartition_neq; by move=> [a|a] [b|b]; rewrite /edge_rel /= !inE.
Qed.
Example triangle_has_no_side (A : {set 'K_3}) : ~ bipartition A.
Proof.
move/bipartition_neq=> h.
pose a : 'K_3 := @Ordinal 3 0 isT.
pose b : 'K_3 := @Ordinal 3 1 isT.
pose c : 'K_3 := @Ordinal 3 2 isT.
move: (h a b isT) (h a c isT) (h b c isT).
by case: (a \in A); case: (b \in A); case: (c \in A).
Qed.
Example deletion_of_all_edges (G : sgraph) : bipartite_after_deletion E(G).
Proof. exact: bipartite_after_deletion_full. Qed.
Example deletion_ignores_nonedges (G : sgraph) (S : {set {set G}}) :
  bipartite_after_deletion S <-> bipartite_after_deletion (S :&: E(G)).
Proof. exact: bipartite_after_deletion_nonedges. Qed.
Example upstream_cycle_is_even (G : diGraph) (A : {set G}) (p : seq G) :
  bipartition A -> cycle (--) p -> ~~ odd (size p).
Proof. exact: bipartition_cycle. Qed.
Example directed_one_arc :
  bipartite_relation (fun x y : bool => ~~ x && y).
Proof. exists idfun; by case=> [] []. Qed.
Example directed_reverse_arc :
  bipartite_relation (fun x y : bool => x && ~~ y).
Proof. exists idfun; by case=> [] []. Qed.
