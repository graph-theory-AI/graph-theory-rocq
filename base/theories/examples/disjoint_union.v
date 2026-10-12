(** Downstream use of the simple-graph disjoint union, upstream GraphTheory's [sjoin] on [G + H] (despite its name,
    no edge across), without corpus imports: same-side adjacency, no edge and no connection across, the number of
    vertices, an empty summand, and the forest bridge [join_is_forest]. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import treewidth.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables G H : sgraph.

(** Adjacency inside each side; nothing across, in either order. *)
Example sjoin_adjacency (a b : G) (c d : H) :
  [/\ ((inl a : sjoin G H) -- inl b) = (a -- b), ((inr c : sjoin G H) -- inr d) = (c -- d),
      ~~ ((inl a : sjoin G H) -- inr c) & ~~ ((inr c : sjoin G H) -- inl a)].
Proof. by []. Qed.

(** No path joins the two sides; the vertices are those of both summands. *)
Example sjoin_disconnected_card (a : G) (c : H) :
  ~~ connect (--) (inl a : sjoin G H) (inr c) /\ #|sjoin G H| = #|G| + #|H|.
Proof. by split; [exact: sjoin_disconnected | rewrite card_sum]. Qed.

End PublicClient.

(** An empty summand adds no vertex, on either side. *)
Example sjoin_empty_left (H : sgraph) : #|sjoin 'K_0 H| = #|H|.
Proof. by rewrite card_sum card_ord. Qed.

Example sjoin_empty_right (G : sgraph) : #|sjoin G 'K_0| = #|G|.
Proof. by rewrite card_sum card_ord addn0. Qed.

(** Two forests have a forest as disjoint union. *)
Example sjoin_forest (T1 T2 : forest) : is_forest [set: sjoin T1 T2].
Proof. exact: join_is_forest. Qed.

Print Assumptions sjoin_adjacency.
Print Assumptions sjoin_disconnected_card.
Print Assumptions sjoin_empty_left.
Print Assumptions sjoin_empty_right.
Print Assumptions sjoin_forest.
