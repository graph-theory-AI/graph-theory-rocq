(** * Minor.conjectures.grounding_X302 -- grounding certificates for wave X302 (2026-11-11)

    Qed-closed, axiom-free certificates for the one row of [X302.v] (Kawarabayashi and Rossman's conjecture):
    hyp_inhabited and not_trivially_true.  X302 declares no helper, so no helper_sanity.
    - [g302_tree k]: the statement's complete binary tree of height k.
    - hyp: whatever the constants c and a, the complete graph on a * k^c + 2 vertices has pathwidth above a * k^c,
      and the statement gives those graphs treewidth at least k or a subdivision of the tree of height k.
    - ntt: the variant "a constant bound" (the row with c = 0) implies the row and is false: for the bound a, K_n
      with n = a + 2 has pathwidth n - 1 > a, treewidth n - 1 < n and no subdivision of the tree of height n (its
      2^(n+1) - 1 nodes are more than n).
    They validate the statement; they do not prove it. *)

From GTBase Require Import base finite_graph pathwidth.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X302.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** The statement's tree *)

Definition g302_tree (k : nat) : sgraph :=
  fg_mk_sgraph (fun i j : 'I_(2 ^ k.+1).-1 => (0 < j) && (i == j.-1./2 :> nat)).

(* ** Facts *)

Lemma g302_tree_card (k : nat) : #|g302_tree k| = (2 ^ k.+1).-1.
Proof. by rewrite card_ord. Qed.

(* The tree of height k has more than k nodes. *)
Lemma g302_tree_large (k : nat) : k < #|g302_tree k|.
Proof. by rewrite g302_tree_card -ltnS prednK ?expn_gt0 // ltn_expl. Qed.

Lemma g302_complete_clique (n : nat) : clique [set: 'K_n].
Proof. by move=> x y _ _. Qed.

(* Every tree decomposition of K_n (n > 0) has a bag holding all n vertices (coq-graph-theory's decomp_clique). *)
Lemma g302_complete_width (n : nat) (T : forest) (D : T -> {set 'K_n}) :
  sdecomp T 'K_n D -> 0 < n -> n <= width D.
Proof.
move=> dec n0.
have [|t sub] := decomp_clique dec (S := [set: 'K_n]) _ (@g302_complete_clique n).
  by rewrite cardsT card_ord.
have cn : #|[set: 'K_n]| = n by rewrite cardsT card_ord.
apply: leq_trans (leq_bigmax t).
by rewrite -{1}cn; exact: subset_leq_card.
Qed.

(* A path decomposition is a tree decomposition (path_tree_forest), so K_n (n > 0) has pathwidth n - 1. *)
Lemma g302_complete_pw (n m : nat) : 0 < n -> pathwidth_at_most ('K_n) m -> n <= m.+1.
Proof.
move=> n0 [T [bag [pt [dec bd]]]].
have tf := path_trees.path_tree_forest pt.
have dec' := (bag_decompositions.bag_decomposition_forest_sdecompP tf bag).1 dec.
apply: leq_trans (g302_complete_width dec' n0) _.
by apply/bigmax_leqP => t _; exact: bd.
Qed.

(* K_(m+2) has pathwidth above m. *)
Lemma g302_complete_above (m : nat) : ~ pathwidth_at_most ('K_(m.+2)) m.
Proof. by move/(g302_complete_pw (isT : 0 < m.+2)); rewrite ltnn. Qed.

(* K_(n+1) has treewidth below n + 1. *)
Lemma g302_complete_tw_below (n : nat) : ~ tw_ge ('K_(n.+1)) n.+1.
Proof.
move=> tg.
have : tw_le ('K_(n.+1)) n by apply: tw_le_card; rewrite card_ord.
by move/tg; rewrite ltnn.
Qed.

(* ** hyp_inhabited: whatever the constants, a complete graph has pathwidth above a * k^c, and the statement
   gives it treewidth at least k or a subdivision of the tree of height k. *)
Definition g302_hyp_claim : Prop :=
  (forall c a k : nat, ~ pathwidth_at_most ('K_((a * k ^ c).+2)) (a * k ^ c)) /\
  (kawarabayashi_rossman_pathwidth_statement ->
     exists c a : nat, forall k : nat,
       tw_ge ('K_((a * k ^ c).+2)) k \/ has_subdivision ('K_((a * k ^ c).+2)) (g302_tree k)).

Theorem g302_hyp_inhabited : g302_hyp_claim.
Proof.
split=> [c a k|]; first exact: g302_complete_above.
by case=> c [a H]; exists c, a => k; exact: H k _ (@g302_complete_above _).
Qed.

(* ** not_trivially_true: "a constant bound" (the row with c = 0) implies the row and fails on K_(a+2) at
   k = a + 2. *)
Definition g302_constant_bound : Prop :=
  exists a : nat, forall (k : nat) (G : sgraph),
    ~ pathwidth_at_most G a -> tw_ge G k \/ has_subdivision G (g302_tree k).

Definition g302_ntt_claim : Prop :=
  ~ g302_constant_bound /\ (g302_constant_bound -> kawarabayashi_rossman_pathwidth_statement).

Theorem g302_not_trivially_true : g302_ntt_claim.
Proof.
split.
- case=> a H.
  case: (H a.+2 _ (@g302_complete_above a)) => [|/has_subdivision_card].
  + exact: g302_complete_tw_below.
  + by rewrite [#|'K_a.+2|]card_ord leqNgt g302_tree_large.
- by case=> a H; exists 0, a => k G; rewrite expn0 muln1; exact: H k G.
Qed.
