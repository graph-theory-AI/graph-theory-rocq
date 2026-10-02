(** * Packing.examples.matching -- downstream use of the public matching API

    Plan section 11 (downstream import test): this client imports only public
    modules, [GTBase] and [Packing.foundations.matching], never a conjecture
    module, and exercises the upstream primitive
    [GraphTheory.connectivity.matching] through the API of
    theories/foundations/matching.v on positive and negative instances.  It
    is listed in _CoqProject, so the package build and the gate compile it. *)

From GTBase Require Import base common.
From Packing.foundations Require Import matching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

(** Positive: the empty family is a matching of every graph. *)
Example empty_family_is_a_matching : matching (G := G) set0.
Proof. exact: matching0. Qed.

(** Positive: one edge is a matching. *)
Example one_edge_is_a_matching (x y : G) : x -- y -> matching [set [set x; y]].
Proof. exact: matching_edge1. Qed.

(** Positive: matchings are closed under taking subfamilies, so removing a
    member keeps a matching. *)
Example without_one_member (M : {set {set G}}) (e : {set G}) :
  matching M -> matching (M :\ e).
Proof. by move=> mM; exact: matching_sub mM (subD1set _ _). Qed.

(** Every member of a matching is an edge, hence a 2-set. *)
Example member_is_a_two_set (M : {set {set G}}) (e : {set G}) :
  matching M -> e \in M -> #|e| = 2.
Proof. exact: matching_card_edge. Qed.

(** Every vertex lies in at most one member (the X15 presentation). *)
Example vertex_in_at_most_one_member (M : {set {set G}}) (v : G) :
  matching M -> #|[set e in M | v \in e]| <= 1.
Proof. by move=> /matching_at_most_oneP[_ /(_ v)]. Qed.

(** Negative: a family containing a loop [[set x]] is not a matching. *)
Example loop_member_is_not_a_matching (M : {set {set G}}) (x : G) :
  [set x] \in M -> ~ matching M.
Proof. by move=> xM mM; have := not_matching_loop x mM; rewrite xM. Qed.

(** Negative: a family containing the empty set is not a matching. *)
Example empty_member_is_not_a_matching (M : {set {set G}}) :
  set0 \in M -> ~ matching M.
Proof. by move=> zM mM; have := not_matching_set0_member mM; rewrite zM. Qed.

End PublicClient.

(** ** Concrete graphs *)

(** Positive: the edge of [K_2]. *)
Example complete_two_edge : matching [set [set: 'K_2]].
Proof. exact: matching_K2. Qed.

Local Notation k0 := (@Ordinal 3 0 isT : 'K_3).
Local Notation k1 := (@Ordinal 3 1 isT : 'K_3).
Local Notation k2 := (@Ordinal 3 2 isT : 'K_3).

(** Positive: one edge of the triangle. *)
Example triangle_one_edge : matching [set [set k0; k1]].
Proof. exact: matching_K3_edge. Qed.

(** Negative: two edges of the triangle share [k0]. *)
Example triangle_two_adjacent_edges : ~ matching [set [set k0; k1]; [set k0; k2]].
Proof. exact: not_matching_K3_adjacent. Qed.

Local Notation q0 := (@Ordinal 4 0 isT : 'K_4).
Local Notation q1 := (@Ordinal 4 1 isT : 'K_4).
Local Notation q2 := (@Ordinal 4 2 isT : 'K_4).
Local Notation q3 := (@Ordinal 4 3 isT : 'K_4).

(** Positive: two disjoint edges of [K_4], through the pairwise-disjoint
    presentation (the X14 form). *)
Example complete_four_two_disjoint_edges :
  matching [set [set q0; q1]; [set q2; q3]].
Proof.
apply/matching_pairwise_disjointP; split.
- by apply/subsetP => e; rewrite !inE => /orP[] /eqP->; rewrite in_edges.
- move=> e f; rewrite !inE => /orP[] /eqP-> /orP[] /eqP->; rewrite ?eqxx // => _;
    by rewrite disjoints_subset; apply/subsetP => x; rewrite !inE => /orP[] /eqP->.
Qed.

Print Assumptions without_one_member.
Print Assumptions vertex_in_at_most_one_member.
Print Assumptions loop_member_is_not_a_matching.
Print Assumptions complete_four_two_disjoint_edges.
