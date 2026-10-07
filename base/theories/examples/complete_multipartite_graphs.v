(** Downstream use of the complete multipartite graph with equal parts without corpus imports: the product carrier
    with parts first, k*m vertices, adjacency exactly across parts, the zero parameters (no vertex), one part (no
    edge), singleton parts (the complete graph, by an isomorphism with ['K_k]), and a concrete K_3(2). *)
From mathcomp Require Import all_boot.
From GTBase Require Import base complete_multipartite_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables k m : nat.

(** Carrier, adjacency and size: pairs (part, index), adjacent iff the parts differ; k parts of m vertices. *)
Example multipartite_carrier_adjacency (x y : 'I_k * 'I_m) :
  @edge_rel (complete_multipartite_graph k m) x y = (x.1 != y.1) /\ #|complete_multipartite_graph k m| = k * m.
Proof. by rewrite complete_multipartite_edgeE card_complete_multipartite_graph. Qed.

(** Same part: never adjacent; different parts: always adjacent. *)
Example multipartite_parts (i j : 'I_k) (a b : 'I_m) :
  ~~ @edge_rel (complete_multipartite_graph k m) (i, a) (i, b) /\
  (i != j -> @edge_rel (complete_multipartite_graph k m) (i, a) (j, b)).
Proof. by split; [exact: complete_multipartite_same_part | exact: complete_multipartite_diff_part]. Qed.

End PublicClient.

(** Zero parameters: no part, or empty parts, leave no vertex at all. *)
Example multipartite_zero (k m : nat) :
  #|complete_multipartite_graph 0 m| = 0 /\ #|complete_multipartite_graph k 0| = 0.
Proof. by rewrite card_complete_multipartite_graph0n card_complete_multipartite_graphn0. Qed.

(** One part: an edgeless graph on m vertices. *)
Example multipartite_one_part (m : nat) (x y : complete_multipartite_graph 1 m) :
  ~~ (x -- y) /\ #|complete_multipartite_graph 1 m| = m.
Proof. by rewrite card_complete_multipartite_graph mul1n complete_multipartite_graph1n_edgeless. Qed.

(** Singleton parts: every two distinct vertices are adjacent, and the graph is isomorphic to ['K_k]. *)
Example multipartite_singleton_parts (k : nat) (x y : complete_multipartite_graph k 1) :
  (x -- y) = (x != y) /\ inhabited (complete_multipartite_graph k 1 ≃ 'K_k).
Proof. by split; [exact: complete_multipartite_graphn1_edgeE | exact: inhabits (complete_multipartite_graphn1_diso k)]. Qed.

(** A concrete K_3(2): six vertices, (0,0) and (1,0) adjacent, (0,0) and (0,1) not. *)
Local Notation P i a := ((@Ordinal 3 i isT, @Ordinal 2 a isT) : complete_multipartite_graph 3 2).

Example multipartite_K3_2 :
  [/\ #|complete_multipartite_graph 3 2| = 6, P 0 0 -- P 1 0 & ~~ (P 0 0 -- P 0 1)].
Proof. by rewrite card_complete_multipartite_graph. Qed.

Print Assumptions multipartite_carrier_adjacency.
Print Assumptions multipartite_parts.
Print Assumptions multipartite_zero.
Print Assumptions multipartite_one_part.
Print Assumptions multipartite_singleton_parts.
Print Assumptions multipartite_K3_2.
