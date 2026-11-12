(** * Minor.conjectures.grounding_X303 -- grounding certificates for wave X303 (2026-11-12)

    Qed-closed, axiom-free certificates for the one row of [X303.v] (Seymour's pathwidth conjecture):
    hyp_inhabited and not_trivially_true.  X303 declares no helper, so no helper_sanity.
    - hyp: for every p, the complete graph on p + 3 vertices is 2-connected with pathwidth above p, and K_1 is an
      apex-forest and outerplanar; the statement then gives, for every apex-forest H1 and outerplanar H2, a
      complete graph containing H1 or H2 as a minor.
    - ntt: the variant "a uniform p" (one p for all H1 and H2) implies the row and is false: at p, the complete
      graph on p + 3 vertices is 2-connected with pathwidth above p, and the graph on p + 4 vertices with no edge
      is an apex-forest and outerplanar with too many vertices to be its minor.
    They validate the statement; they do not prove it. *)

From GTBase Require Import base pathwidth.
From Minor.conjectures Require Import X303.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* ** Complete graphs *)

Lemma g303_complete_clique (n : nat) : clique [set: 'K_n].
Proof. by move=> x y _ _. Qed.

Lemma g303_complete_width (n : nat) (T : forest) (D : T -> {set 'K_n}) :
  sdecomp T 'K_n D -> 0 < n -> n <= width D.
Proof.
move=> dec n0.
have [|t sub] := decomp_clique dec (S := [set: 'K_n]) _ (@g303_complete_clique n).
  by rewrite cardsT card_ord.
have cn : #|[set: 'K_n]| = n by rewrite cardsT card_ord.
apply: leq_trans (leq_bigmax t).
by rewrite -{1}cn; exact: subset_leq_card.
Qed.

Lemma g303_complete_pw (n m : nat) : 0 < n -> pathwidth_at_most ('K_n) m -> n <= m.+1.
Proof.
move=> n0 [T [bag [pt [dec bd]]]].
have tf := path_trees.path_tree_forest pt.
have dec' := (bag_decompositions.bag_decomposition_forest_sdecompP tf bag).1 dec.
apply: leq_trans (g303_complete_width dec' n0) _.
by apply/bigmax_leqP => t _; exact: bd.
Qed.

(* K_(p+3) has pathwidth above p. *)
Lemma g303_complete_above (p : nat) : ~ pathwidth_at_most ('K_(p.+3)) p.
Proof. by move/(g303_complete_pw (isT : 0 < p.+3)); rewrite !ltnS ltnNge leqnSn. Qed.

(* K_(p+3) is 2-connected. *)
Lemma g303_complete_two_connected (p : nat) : k_connected ('K_(p.+3)) 2.
Proof.
split; first by rewrite card_ord.
move=> S _ x y hx hy.
case: (eqVneq x y) => [->|xy]; first exact: connect0.
by apply: connect1; rewrite /= hx hy.
Qed.

(* ** Edgeless graphs and minors *)

Lemma g303_edgeless_no_minor (G H : sgraph) (x y : H) :
  (forall u w : G, ~~ u -- w) -> x -- y -> ~ minor G H.
Proof.
move=> noe xy [phi [_ _ hE]].
by case: (hE x y xy) => x0 [y0 [_ _]]; rewrite (negbTE (noe x0 y0)).
Qed.

Lemma g303_kb0_noedge (n : nat) (x y : KB n 0) : ~~ x -- y.
Proof. by case: x => [x|[]] //; case: y => [y|[]]. Qed.

Lemma g303_kb0_card (n : nat) : #|KB n 0| = n.
Proof. by rewrite card_sum !card_ord addn0. Qed.

(* The graph on n + 1 vertices with no edge is an apex-forest and outerplanar. *)
Lemma g303_kb0_apex_forest (n : nat) : exists v : KB n.+1 0, is_forest ([set: KB n.+1 0] :\ v).
Proof.
exists (inl ord0); apply: sub_forest (subsetDl _ _) _.
apply/minor.K3_free_forest.
exact: (@g303_edgeless_no_minor _ 'K_3 ord0 ord_max (@g303_kb0_noedge n.+1)).
Qed.

Lemma g303_kb0_outerplanar (n : nat) : ~ minor (KB n 0) 'K_4 /\ ~ minor (KB n 0) (KB 2 3).
Proof.
split.
- exact: (@g303_edgeless_no_minor _ 'K_4 ord0 ord_max (@g303_kb0_noedge n)).
- exact: (@g303_edgeless_no_minor _ (KB 2 3) (inl ord0) (inr ord0) (@g303_kb0_noedge n)).
Qed.

(* K_1 is an apex-forest and outerplanar. *)
Lemma g303_K1_apex_forest : exists v : ('K_1), is_forest ([set: 'K_1] :\ v).
Proof.
exists ord0; apply: sub_forest (subsetDl _ _) _.
by apply/minor.K3_free_forest => /minor_card; rewrite !card_ord.
Qed.

Lemma g303_K1_outerplanar : ~ minor 'K_1 'K_4 /\ ~ minor 'K_1 (KB 2 3).
Proof. by split=> /minor_card; rewrite ?card_sum !card_ord. Qed.

(* ** hyp_inhabited *)
Definition g303_hyp_claim : Prop :=
  [/\ (forall p : nat, k_connected ('K_(p.+3)) 2 /\ ~ pathwidth_at_most ('K_(p.+3)) p),
      (exists v : ('K_1), is_forest ([set: 'K_1] :\ v)),
      ~ minor 'K_1 'K_4 /\ ~ minor 'K_1 (KB 2 3)
    & (seymour_two_connected_pathwidth_statement ->
        forall H1 H2 : sgraph,
          (exists v : H1, is_forest ([set: H1] :\ v)) -> ~ minor H2 'K_4 -> ~ minor H2 (KB 2 3) ->
          exists p : nat, minor ('K_(p.+3)) H1 \/ minor ('K_(p.+3)) H2)].

Theorem g303_hyp_inhabited : g303_hyp_claim.
Proof.
split=> [p|||S H1 H2 a o4 o23].
- by split; [exact: g303_complete_two_connected | exact: g303_complete_above].
- exact: g303_K1_apex_forest.
- exact: g303_K1_outerplanar.
- case: (S H1 H2 a o4 o23) => p Hp; exists p.
  exact: Hp _ (g303_complete_two_connected p) (@g303_complete_above p).
Qed.

(* ** not_trivially_true *)
Definition g303_uniform_p : Prop :=
  exists p : nat, forall H1 H2 : sgraph,
    (exists v : H1, is_forest ([set: H1] :\ v)) -> ~ minor H2 'K_4 -> ~ minor H2 (KB 2 3) ->
    forall G : sgraph, k_connected G 2 -> ~ pathwidth_at_most G p -> minor G H1 \/ minor G H2.

Definition g303_ntt_claim : Prop :=
  ~ g303_uniform_p /\ (g303_uniform_p -> seymour_two_connected_pathwidth_statement).

Theorem g303_not_trivially_true : g303_ntt_claim.
Proof.
split.
- case=> p H.
  have [o4 o23] := g303_kb0_outerplanar p.+4.
  case: (H _ _ (g303_kb0_apex_forest p.+3) o4 o23 _ (g303_complete_two_connected p) (@g303_complete_above p))
    => /minor_card; by rewrite g303_kb0_card card_ord ltnn.
- by case=> p H H1 H2 a o4 o23; exists p => G; exact: H.
Qed.

