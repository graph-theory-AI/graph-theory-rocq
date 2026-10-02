(** * GTBase.examples.perfect_matching -- downstream use of the public perfect-matching API

    Plan section 11 (downstream import test): this client imports only
    [GTBase.base], never a conjecture module, and exercises
    [GTBase.common.perfect_matching] through its API on positive and negative
    instances.  It is listed in _CoqProject, so the base build and the gate
    compile it. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicClient.
Variable G : sgraph.

(** A perfect matching is a matching that covers every vertex. *)
Example perfect_matching_is_a_matching (M : {set {set G}}) :
  perfect_matching M -> matching M.
Proof. exact: perfect_matching_matching. Qed.

Example every_vertex_in_exactly_one_member (M : {set {set G}}) (v : G) :
  perfect_matching M -> #|[set e in M | v \in e]| = 1.
Proof. by move=> /perfect_matching_exactly_oneP[_ /(_ v)]. Qed.

(** The members pair the vertices up. *)
Example order_is_twice_the_size (M : {set {set G}}) :
  perfect_matching M -> #|G| = 2 * #|M|.
Proof. exact: card_perfect_matching. Qed.

(** Negative: odd order, a loop member, and the empty family on a nonempty graph. *)
Example odd_order_has_none (M : {set {set G}}) : odd #|G| -> ~ perfect_matching M.
Proof. exact: not_perfect_matching_odd. Qed.

Example loop_member_is_not_perfect (M : {set {set G}}) (x : G) :
  [set x] \in M -> ~ perfect_matching M.
Proof. exact: not_perfect_matching_loop. Qed.

Example empty_family_misses_a_vertex : 0 < #|G| -> ~ perfect_matching (G := G) set0.
Proof. exact: not_perfect_matching0. Qed.

End PublicClient.

(** ** Concrete graphs *)

(** Positive: the edge of [K_2]; the empty family on the empty graph. *)
Example complete_two_edge : perfect_matching (G := 'K_2) [set [set: 'K_2]].
Proof. exact: perfect_matching_K2. Qed.

Example empty_graph_empty_family : perfect_matching (G := 'K_0) set0.
Proof. exact: perfect_matching0_K0. Qed.

(** Positive: two disjoint edges cover the four vertices of [K_4]. *)
Definition complete_four_pairs : {set {set 'K_4}} :=
  [set [set (@Ordinal 4 0 isT : 'K_4); (@Ordinal 4 1 isT : 'K_4)];
       [set (@Ordinal 4 2 isT : 'K_4); (@Ordinal 4 3 isT : 'K_4)]].

Example complete_four_pairs_perfect : perfect_matching complete_four_pairs.
Proof.
split.
- split=> [e|e1 e2]; rewrite /complete_four_pairs !inE.
  + by case/orP=> /eqP->; rewrite in_edges.
  + move=> /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->] // x;
      rewrite !inE; case: x => -[|[|[|[|x]]]] xP //=.
- apply/setP => x.
  rewrite /cover /complete_four_pairs bigcup_setU !big_set1 !inE.
  by case: x => -[|[|[|[|x]]]] xP //=.
Qed.

(** Negative: the triangle has none. *)
Example triangle_has_none (M : {set {set 'K_3}}) : ~ perfect_matching M.
Proof. exact: not_perfect_matching_K3. Qed.

Print Assumptions every_vertex_in_exactly_one_member.
Print Assumptions order_is_twice_the_size.
Print Assumptions complete_four_pairs_perfect.
Print Assumptions triangle_has_none.
