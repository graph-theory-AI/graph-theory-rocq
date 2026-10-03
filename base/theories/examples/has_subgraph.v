(** Downstream use of ordinary subgraph containment [has_subgraph G H] (host first),
    without corpus imports. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables (G H K : sgraph).

(** The witness view: an injective map preserving adjacency, and nothing about
    non-adjacency. *)
Example embedding_gives_containment (f : H -> G) :
  injective f -> (forall x y : H, x -- y -> f x -- f y) -> has_subgraph G H.
Proof. by move=> inj_f hom_f; apply/has_subgraphP; exists f. Qed.

Example containment_gives_an_embedding :
  has_subgraph G H ->
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.
Proof. by move/has_subgraphP. Qed.

Example containment_composes :
  has_subgraph G H -> has_subgraph H K -> has_subgraph G K.
Proof. exact: has_subgraph_trans. Qed.

Example patterns_are_not_larger_than_hosts : has_subgraph G H -> #|H| <= #|G|.
Proof. exact: has_subgraph_card. Qed.

(** Degenerate cases: the empty pattern, the empty host, edge deletion. *)
Example every_host_contains_the_empty_graph : has_subgraph G 'K_0.
Proof. exact: has_subgraph_K0. Qed.

Example the_empty_host_contains_only_empty_patterns :
  has_subgraph 'K_0 H <-> #|H| = 0.
Proof. exact: has_subgraph_K0_host. Qed.

Example deleting_edges_gives_a_subgraph (F : {set {set G}}) :
  has_subgraph G (del_edge_set G F).
Proof. exact: has_subgraph_del_edge_set. Qed.

End PublicClient.

(** Ordinary versus induced: two isolated vertices sit inside [K_2] as a subgraph,
    but not as an induced subgraph. *)
Example ordinary_but_not_induced :
  has_subgraph 'K_2 (del_edge_set 'K_2 [set [set: 'K_2]]) /\
  induced_free 'K_2 (del_edge_set 'K_2 [set [set: 'K_2]]).
Proof. exact: has_subgraph_not_induced. Qed.

(** Negative: a bigger pattern never fits, and a pattern with an edge does not fit in
    an edgeless host of the same size. *)
Example K2_is_not_a_subgraph_of_K1 : ~ has_subgraph 'K_1 'K_2.
Proof. by move/has_subgraph_card; rewrite !card_ord. Qed.

Example an_edge_needs_an_edge :
  ~ has_subgraph (del_edge_set 'K_2 [set [set: 'K_2]]) 'K_2.
Proof.
move/has_subgraphP=> [f [inj_f hom_f]].
have := hom_f ord0 ord_max isT; rewrite del_edge_set1.
have f01 : f ord0 != f ord_max by rewrite (inj_eq inj_f).
by rewrite eqEcard subsetT cards2 f01 cardsT card_ord andbF.
Qed.

Print Assumptions ordinary_but_not_induced.
Print Assumptions an_edge_needs_an_edge.
