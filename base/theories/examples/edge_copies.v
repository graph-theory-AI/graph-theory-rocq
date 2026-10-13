(** Public-only examples for edge images, copies and the two list-decomposition conventions. *)
From GTBase Require Import base common edge_copies.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [n] vertices and no edge. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Lemma edgeless_edges (n : nat) : E(edgeless n) = set0.
Proof. by apply/setP => e; rewrite inE; apply/negP => /edgesP [x [y [_]]]. Qed.

(** An injective image need not lie in the host: the edge of [K_2] maps onto a non-edge. *)
Example injective_image_outside_host :
  injective_edge_image (G := edgeless 2) 'K_2 (edge_image (fun x : 'K_2 => (x : edgeless 2))) /\
  ~ embedded_edge_copy (G := edgeless 2) 'K_2 (edge_image (fun x : 'K_2 => (x : edgeless 2))).
Proof.
split; first by exists (fun x : 'K_2 => (x : edgeless 2)); split=> // x y.
move=> /embedded_edge_copy_sub /subsetP /(_ [set (ord0 : edgeless 2); ord_max]) H.
have : [set (ord0 : edgeless 2); ord_max] \in E(edgeless 2).
  by apply: H; rewrite edge_imageE; apply/existsP; exists (ord0, ord_max); rewrite /= ?eqxx ?andbT.
by rewrite edgeless_edges inE.
Qed.

(** The identity image of [K_2] is its edge set. *)
Example identity_image_K2 :
  injective_edge_image (G := 'K_2) 'K_2 E('K_2).
Proof. by exists (fun x : 'K_2 => x); split; [exact: inj_id | rewrite edge_image_id]. Qed.

(** Repeated identical parts are allowed by the equal-parts convention ... *)
Example equal_parts_repeat_K2 : edge_decomposition_by_equal_parts 'K_2 'K_2.
Proof.
exists [:: E('K_2); E('K_2)]; split; [|split; [|split]].
- by move=> F; rewrite !inE orbb => /eqP ->; exact: identity_image_K2.
- by move=> F; rewrite !inE orbb => /eqP ->.
- by move=> e eE; exists E('K_2); rewrite inE eqxx.
- by move=> F1 F2 e; rewrite !inE !orbb => /eqP -> /eqP ->.
Qed.

(** ... but not by the exact-count convention. *)
Example exact_count_no_repeat_K2 : ~ edge_decomposition_exact 'K_2 [:: E('K_2); E('K_2)].
Proof.
apply: (@edge_decomposition_exact_double_not _ [set (ord0 : 'K_2); ord_max]).
by rewrite in_edges.
Qed.

(** An empty host is decomposed by the empty list, for any pattern, in both conventions. *)
Example empty_host_exact (T : sgraph) : edge_decomposition_exact (G := edgeless 3) T [::].
Proof. exact: edge_decomposition_exact_nil (edgeless_edges 3). Qed.

Example empty_host_equal_parts (T : sgraph) : edge_decomposition_by_equal_parts (edgeless 3) T.
Proof. exact: edge_decomposition_equal_parts_nil (edgeless_edges 3). Qed.

(** The one-vertex tree has no edge, and repeated empty copies of it are allowed by the exact count. *)
Example one_vertex_tree_no_edge : E('K_1) = set0.
Proof.
apply/setP => e; rewrite inE; apply/negP => /edgesP [x [y [_ xy]]].
by move: xy; rewrite (ord1 x) (ord1 y) sgP.
Qed.

Example one_vertex_tree_repeated_empty_copies :
  edge_decomposition_exact (G := 'K_1) 'K_1 [:: E('K_1); E('K_1)].
Proof.
split.
- by move=> A; rewrite !inE orbb => /eqP ->; exact: embedded_edge_copy_self.
- by move=> e; rewrite /= one_vertex_tree_no_edge !inE.
Qed.

(** A tree on two vertices has an edge. *)
Example K2_tree_has_edge : 0 < #|E('K_2)|.
Proof.
apply/card_gt0P; exists [set (ord0 : 'K_2); ord_max]; by rewrite in_edges.
Qed.

Print Assumptions injective_image_outside_host.
Print Assumptions identity_image_K2.
Print Assumptions equal_parts_repeat_K2.
Print Assumptions exact_count_no_repeat_K2.
Print Assumptions empty_host_exact.
Print Assumptions empty_host_equal_parts.
Print Assumptions one_vertex_tree_no_edge.
Print Assumptions one_vertex_tree_repeated_empty_copies.
Print Assumptions K2_tree_has_edge.
