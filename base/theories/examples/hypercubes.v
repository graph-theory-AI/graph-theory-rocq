(** Downstream use of the two hypercube views without corpus imports: Q_0 (one vertex, no edge), the Q_1/K_2 bridge
    in both views, the product recurrence, 2^d vertices in both views, tuple adjacency at exactly one changed
    coordinate (with a concrete Q_3 check), and the explicit isomorphism with its edge transport in every dimension. *)
From GTBase Require Import base hypercubes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Q_0 is a single vertex with no edge, in both views: not the empty graph. *)
Example hypercube0 :
  [/\ #|product_hypercube 0| = 1, #|tuple_hypercube 0| = 1,
      forall x y : product_hypercube 0, ~~ x -- y & forall x y : tuple_hypercube 0, ~~ x -- y].
Proof.
split; rewrite ?card_product_hypercube ?card_tuple_hypercube // => x y.
  by rewrite product_hypercube0_edge.
by rewrite tuple_hypercube0_edge.
Qed.

(** Q_1 is K_2 in both views. *)
Definition tuple_hypercube1_diso : tuple_hypercube 1 ≃ 'K_2 :=
  diso_comp (diso_sym (product_tuple_hypercube_diso 1)) product_hypercube1_diso.

Example hypercube_recurrence (d : nat) : product_hypercube d.+1 = cartesian_product 'K_2 (product_hypercube d).
Proof. exact: product_hypercubeS. Qed.

Example hypercube_card (d : nat) : #|product_hypercube d| = 2 ^ d /\ #|tuple_hypercube d| = 2 ^ d.
Proof. by rewrite card_product_hypercube card_tuple_hypercube. Qed.

(** Two tuples are adjacent iff exactly one coordinate changes. *)
Example tuple_hypercube_one_coordinate (d : nat) (x y : tuple_hypercube d) :
  x -- y <-> exists i : 'I_d, tnth x i != tnth y i /\ forall j : 'I_d, j != i -> tnth x j = tnth y j.
Proof. by split=> /tuple_hypercube_edgeP. Qed.

(** In Q_3, 100 -- 110 -- 010, while 100 and 010 differ in two coordinates (coordinate by coordinate). *)
Example tuple_hypercube3_edges :
  [/\ ([tuple true; false; false] : tuple_hypercube 3) -- [tuple true; true; false],
      ([tuple true; true; false] : tuple_hypercube 3) -- [tuple false; true; false]
    & ~~ (([tuple true; false; false] : tuple_hypercube 3) -- [tuple false; true; false])].
Proof. by rewrite !tuple_hypercube_edge_cons !tuple_hypercube0_edge. Qed.

(** The explicit isomorphism: inverse coordinate maps, edges transported both ways, in every dimension. *)
Example hypercube_views_iso (d : nat) (x y : product_hypercube d) (s : tuple_hypercube d) :
  [/\ tuple_to_product (product_to_tuple x) = x, product_to_tuple (tuple_to_product s) = s
    & product_to_tuple x -- product_to_tuple y = x -- y].
Proof. by rewrite product_to_tupleK tuple_to_productK product_to_tuple_edge. Qed.

(** The bundled isomorphism transports isomorphism invariants, e.g. the number of edges. *)
Example hypercube_views_edges (d : nat) : #|E(product_hypercube d)| = #|E(tuple_hypercube d)|.
Proof. exact: diso_card_edge (product_tuple_hypercube_diso d). Qed.

Print Assumptions hypercube0.
Print Assumptions tuple_hypercube1_diso.
Print Assumptions hypercube_recurrence.
Print Assumptions hypercube_card.
Print Assumptions tuple_hypercube_one_coordinate.
Print Assumptions tuple_hypercube3_edges.
Print Assumptions hypercube_views_iso.
Print Assumptions hypercube_views_edges.
