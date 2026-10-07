(** Downstream use of the undirected Cayley graph without corpus imports: the carrier and the symmetrised loopless
    adjacency for an arbitrary finite group and connection set, the empty, identity and full connection sets, a group
    of order one, edges along right multiplication for an arbitrary (not inverse-closed) set, the inverse-closed
    specialisation, and a small nonsymmetric example in the nonabelian group ['S_3]. *)
From mathcomp Require Import all_boot fingroup perm.
From GTBase Require Import base cayley_graphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variables (gT : finGroupType) (S : {set gT}).

(** Carrier and adjacency: the group elements, adjacent when distinct with a quotient in [S] in either order;
    symmetric, and never a loop even when [1 \in S]. *)
Example cayley_carrier_adjacency (x y : gT) :
  [/\ #|undirected_cayley_graph S| = #|gT|,
      @edge_rel (undirected_cayley_graph S) x y = (x != y) && (((x^-1 * y)%g \in S) || ((y^-1 * x)%g \in S)),
      @edge_rel (undirected_cayley_graph S) x y = @edge_rel (undirected_cayley_graph S) y x
    & ~~ @edge_rel (undirected_cayley_graph S) x x].
Proof.
split; [exact: card_undirected_cayley_graph | exact: undirected_cayley_edgeE | exact: sg_sym | by rewrite sg_irrefl].
Qed.

(** The empty and identity connection sets give no edge; the full one gives every edge, a complete graph. *)
Example cayley_connection_sets (x y : gT) :
  [/\ @edge_rel (undirected_cayley_graph set0) x y = false,
      @edge_rel (undirected_cayley_graph [set 1%g]) x y = false,
      @edge_rel (undirected_cayley_graph [set: gT]) x y = (x != y)
    & inhabited (undirected_cayley_graph [set: gT] ≃ 'K_#|gT|)].
Proof.
split; [exact: undirected_cayley_set0 | exact: undirected_cayley_set1 | exact: undirected_cayley_setT |].
exact: inhabits (undirected_cayley_setT_diso gT).
Qed.

(** A group of order one: one vertex and no edge, whatever the connection set. *)
Example cayley_trivial_group (x y : gT) : #|gT| = 1 -> ~~ @edge_rel (undirected_cayley_graph S) x y.
Proof.
move=> g1; have /card_le1_eqP/(_ x y isT isT) yx : #|gT| <= 1 by rewrite g1.
by rewrite yx sg_irrefl.
Qed.

(** An arbitrary connection set: right multiplication by a non-identity element of [S] is an edge, and so is right
    multiplication by its inverse, which need not lie in [S]. *)
Example cayley_right_multiplication (x s : gT) : s \in S -> s != 1%g ->
  @edge_rel (undirected_cayley_graph S) x (x * s)%g /\ @edge_rel (undirected_cayley_graph S) x (x * s^-1)%g.
Proof. by move=> sS s1; apply/andP; exact: undirected_cayley_edge_mul. Qed.

(** An inverse-closed connection set: one disjunct suffices. *)
Example cayley_inverse_closed (x y : gT) : (forall z : gT, (z \in S) = ((z^-1)%g \in S)) ->
  @edge_rel (undirected_cayley_graph S) x y = (x != y) && ((x^-1 * y)%g \in S).
Proof. exact: undirected_cayley_edge_inv. Qed.

End PublicClient.

(** A small nonsymmetric example in the nonabelian group ['S_3]: the 3-cycle [c3] is not its own inverse, so
    [[set c3]] is not closed under inverses, yet [1] and [c3^-1] are adjacent through the symmetrised adjacency. *)
Local Notation O3 i := (@Ordinal 3 i isT).

Definition c3 : 'S_3 := (tperm (O3 0) (O3 1) * tperm (O3 1) (O3 2))%g.

Lemma c3_0 : c3 (O3 0) = O3 2.
Proof. by rewrite permM [tperm _ _ (O3 0)]tpermL tpermL. Qed.

Lemma c3_2 : c3 (O3 2) = O3 1.
Proof. by rewrite permM [tperm _ _ (O3 2)]tpermD // tpermR. Qed.

Lemma c3_neq1 : c3 != 1%g.
Proof. by apply/eqP => /(congr1 (fun p : 'S_3 => val (p (O3 0)))); rewrite c3_0 perm1. Qed.

Lemma c3V_neq : (c3^-1)%g != c3.
Proof.
apply/eqP => h; have := congr1 (fun p : 'S_3 => val ((c3 * p)%g (O3 0))) h.
by rewrite mulgV perm1 permM c3_0 c3_2.
Qed.

Example cayley_nonsymmetric_S3 :
  [/\ (c3^-1)%g \notin [set c3], ~ (forall z : 'S_3, (z \in [set c3]) = ((z^-1)%g \in [set c3]))
    & @edge_rel (undirected_cayley_graph [set c3]) 1%g (c3^-1)%g].
Proof.
have nsym : (c3^-1)%g \notin [set c3] by rewrite in_set1 c3V_neq.
split=> //; first by move=> /(_ c3); rewrite set11 (negbTE nsym).
have := @undirected_cayley_edge_mul _ [set c3] 1%g c3 (set11 c3) c3_neq1.
by rewrite !mul1g => /andP[].
Qed.

Print Assumptions cayley_carrier_adjacency.
Print Assumptions cayley_connection_sets.
Print Assumptions cayley_trivial_group.
Print Assumptions cayley_right_multiplication.
Print Assumptions cayley_inverse_closed.
Print Assumptions cayley_nonsymmetric_S3.
