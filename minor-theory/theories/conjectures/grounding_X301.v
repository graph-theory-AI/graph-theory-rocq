(** * Minor.conjectures.grounding_X301 -- grounding certificates for wave X301 (2026-11-11)

    Qed-closed, axiom-free certificates for the one row of [X301.v] (Wood's conjecture): hyp_inhabited and
    not_trivially_true.  X301 declares no helper, so no helper_sanity.
    - [g301_tree h]: the statement's complete binary tree of height h; [g301_class_bounded t h k]: every graph of
      treewidth t without a subdivision of [g301_tree h] has pathwidth at most k.
    - hyp: K_2 has treewidth 1 and no subdivision of the tree of height 1 (three nodes), and the statement bounds
      the pathwidth of that class.
    - ntt: the variant "one constant c gives the bound c * h, whatever the treewidth" implies the row and is
      false: for h = c + 2, K_n with n = c (c + 2) + 2 has treewidth n - 1, no subdivision of the tree (its
      2^(c+3) - 1 nodes are more than n), and pathwidth n - 1 > c * h (every tree decomposition of a complete
      graph has a bag holding all its vertices, and a path decomposition is one).
    They validate the statement; they do not prove it. *)

From mathcomp Require Import zify.
From Stdlib Require Import Lia.
From GTBase Require Import base finite_graph pathwidth.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X301.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** The statement's parts *)

Definition g301_tree (h : nat) : sgraph :=
  fg_mk_sgraph (fun i j : 'I_(2 ^ h.+1).-1 => (0 < j) && (i == j.-1./2 :> nat)).

Definition g301_class_bounded (t h k : nat) : Prop :=
  forall G : sgraph,
    tw_le G t -> tw_ge G t -> ~ has_subdivision G (g301_tree h) -> pathwidth_at_most G k.

(* ** Facts *)

Lemma g301_tree_card (h : nat) : #|g301_tree h| = (2 ^ h.+1).-1.
Proof. by rewrite card_ord. Qed.

Lemma g301_complete_clique (n : nat) : clique [set: 'K_n].
Proof. by move=> x y _ _. Qed.

(* Every tree decomposition of K_n (n > 0) has a bag holding all n vertices (coq-graph-theory's decomp_clique). *)
Lemma g301_complete_width (n : nat) (T : forest) (D : T -> {set 'K_n}) :
  sdecomp T 'K_n D -> 0 < n -> n <= width D.
Proof.
move=> dec n0.
have [|t sub] := decomp_clique dec (S := [set: 'K_n]) _ (@g301_complete_clique n).
  by rewrite cardsT card_ord.
have cn : #|[set: 'K_n]| = n by rewrite cardsT card_ord.
apply: leq_trans (leq_bigmax t).
by rewrite -{1}cn; exact: subset_leq_card.
Qed.

(* K_(n+1) has treewidth n. *)
Lemma g301_complete_tw (n : nat) : tw_le ('K_(n.+1)) n /\ tw_ge ('K_(n.+1)) n.
Proof.
split; first by apply: tw_le_card; rewrite card_ord.
move=> m [T [D [dec w]]].
have h := g301_complete_width dec (isT : 0 < n.+1).
by rewrite -ltnS; exact: leq_trans h w.
Qed.

(* A path decomposition is a tree decomposition (path_tree_forest), so K_n (n > 0) has pathwidth n - 1. *)
Lemma g301_complete_pw (n k : nat) : 0 < n -> pathwidth_at_most ('K_n) k -> n <= k.+1.
Proof.
move=> n0 [T [bag [pt [dec bd]]]].
have tf := path_trees.path_tree_forest pt.
have dec' := (bag_decompositions.bag_decomposition_forest_sdecompP tf bag).1 dec.
apply: leq_trans (g301_complete_width dec' n0) _.
by apply/bigmax_leqP => t _; exact: bd.
Qed.

Lemma g301_arith (c : nat) : (c * c.+2).+3 < 2 ^ c.+3.
Proof.
elim: c => [//|c IH].
rewrite expnS mul2n -addnn.
apply: leq_trans (leq_add IH IH).
rewrite mulSn mulnS.
have h2 : c * 2 <= c * c.+2 by apply: leq_mul.
move: h2; set X := c * c.+2 => h2; clearbody X.
lia.
Qed.

(* ** hyp_inhabited: K_2 has treewidth 1 and no subdivision of the tree of height 1, and the statement bounds the
   pathwidth of the graphs of treewidth 1 without such a subdivision. *)
Definition g301_hyp_claim : Prop :=
  [/\ tw_le ('K_2) 1, tw_ge ('K_2) 1, ~ has_subdivision ('K_2) (g301_tree 1)
    & wood_pathwidth_binary_tree_statement -> exists k, g301_class_bounded 1 1 k].

Theorem g301_hyp_inhabited : g301_hyp_claim.
Proof.
have [tl tg] := g301_complete_tw 1.
split=> //.
- by move/has_subdivision_card; rewrite g301_tree_card card_ord.
- by case=> f Hf; exists (f 1 * 1) => G t1 t2 ns; exact: Hf 1 1 G t1 t2 ns.
Qed.

(* ** not_trivially_true: "one constant c gives the bound c * h, whatever the treewidth" implies the row and fails
   at h = c + 2 on K_(c (c + 2) + 2). *)
Definition g301_uniform : Prop :=
  exists c : nat, forall (t h : nat) (G : sgraph),
    tw_le G t -> tw_ge G t -> ~ has_subdivision G (g301_tree h) -> pathwidth_at_most G (c * h).

Definition g301_ntt_claim : Prop :=
  ~ g301_uniform /\ (g301_uniform -> wood_pathwidth_binary_tree_statement).

Theorem g301_not_trivially_true : g301_ntt_claim.
Proof.
split.
- case=> c Hc.
  have [tl tg] := g301_complete_tw (c * c.+2).+1.
  have ns : ~ has_subdivision ('K_((c * c.+2).+2)) (g301_tree c.+2).
    move/has_subdivision_card; rewrite g301_tree_card card_ord.
    have := g301_arith c; set P := 2 ^ c.+3; set X := c * c.+2; clearbody P X; lia.
  have := g301_complete_pw (isT : 0 < (c * c.+2).+2) (Hc _ c.+2 _ tl tg ns).
  by rewrite ltnn.
- by case=> c Hc; exists (fun _ => c) => t h G; exact: Hc t h G.
Qed.
