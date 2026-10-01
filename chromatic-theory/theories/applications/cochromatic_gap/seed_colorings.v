(** * Exact color parameters of the 13-vertex seed.

    Ordinary colors pair consecutive vertices (seven colors).
    The cochromatic partition is {0,2,4,6}, {1,5,7,11}, {3,10,12}, {8,9}:
    the first three classes are cliques and the last is independent.
    Counting with clique bound four and stable-set bound two proves
    that four and seven colors, respectively, are optimal. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
From GTBase Require Import base.
From Chromatic.conjectures Require Import XE1 XE2 X7.
From Chromatic.applications.cochromatic_gap Require Import mycielski_gap seed_certificates fiber.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma seed_pairs (P : nat -> nat -> bool) :
  all (fun x => all (fun y => P x y) seed_nats) seed_nats ->
  forall x y : seed, P (val x) (val y).
Proof.
move=> h x y.
exact: (allP (allP h (val x) (seed_nats_mem x)) (val y) (seed_nats_mem y)).
Qed.
Definition seed_chi_nat x := x %/ 2.
Lemma seed_chi_bound_check : all (fun x => seed_chi_nat x < 7) seed_nats.
Proof. vm_compute. reflexivity. Qed.
Definition seed_chi_color (x : seed) : 'I_7 :=
  Ordinal (allP seed_chi_bound_check (val x) (seed_nats_mem x)).
Lemma seed_chi_proper_check : all (fun x => all (fun y =>
  seed_nat_rel x y ==> (seed_chi_nat x != seed_chi_nat y)) seed_nats) seed_nats.
Proof. vm_compute. reflexivity. Qed.
Lemma seed_chi_proper : proper_map seed_chi_color.
Proof.
move=> x y hxy; rewrite /seed_chi_color -val_eqE /=.
exact: (implyP (seed_pairs seed_chi_proper_check x y) hxy).
Qed.

Definition seed_co_nat x :=
  if x \in [:: 0; 2; 4; 6] then 0 else
  if x \in [:: 1; 5; 7; 11] then 1 else
  if x \in [:: 3; 10; 12] then 2 else 3.
Lemma seed_co_bound_check : all (fun x => seed_co_nat x < 4) seed_nats.
Proof. vm_compute. reflexivity. Qed.
Definition seed_co_color (x : seed) : 'I_4 :=
  Ordinal (allP seed_co_bound_check (val x) (seed_nats_mem x)).
Definition seed_independent_index : 'I_4 := @Ordinal 4 3 erefl.
Definition seed_co_clique_check i := all (fun x => all (fun y =>
  [&& seed_co_nat x == i, seed_co_nat y == i & x != y] ==>
  seed_nat_rel x y) seed_nats) seed_nats.
Lemma seed_co_cliques_check : all seed_co_clique_check (iota 0 3).
Proof. vm_compute. reflexivity. Qed.
Lemma seed_co_independent_check : all (fun x => all (fun y =>
  ((seed_co_nat x == 3) && (seed_co_nat y == 3)) ==>
  ~~ seed_nat_rel x y) seed_nats) seed_nats.
Proof. vm_compute. reflexivity. Qed.
Lemma seed_co_independent : independent_color seed_co_color seed_independent_index.
Proof.
move=> x y; rewrite !inE /seed_co_color /seed_independent_index -!val_eqE /= => hx hy hxy.
have h := implyP (seed_pairs seed_co_independent_check x y).
have ha : (seed_co_nat (val x) == 3) && (seed_co_nat (val y) == 3) by rewrite hx hy.
exact: (negP (h ha) hxy).
Qed.
Lemma seed_co_homogeneous : homogeneous_map seed_co_color.
Proof.
move=> i; case hi: (i == seed_independent_index).
- move/eqP: hi=> ->; right; exact: seed_co_independent.
- left; move=> x y; rewrite !inE /seed_co_color -!val_eqE /= => hx hy hxy.
  have h3 : val i < 3.
    have hib := ltn_ord i.
    move: hi; rewrite -val_eqE /seed_independent_index /= => hi.
    by rewrite ltn_neqAle hi /= -ltnS.
  have him : val i \in iota 0 3 by rewrite mem_iota add0n leq0n /=.
  have hh := allP seed_co_cliques_check (val i) him.
  rewrite /seed_co_clique_check in hh.
  have h := seed_pairs hh x y.
  apply: (implyP h); by rewrite hx hy hxy.
Qed.

Lemma seed_card : #|seed| = 13.
Proof. exact: card_ord. Qed.
Lemma seed_nonempty : 0 < #|seed|.
Proof. by rewrite seed_card. Qed.
Lemma seed_homogeneous_bounded (A : {set seed}) :
  clique A \/ xe1_stable_set A -> #|A| <= 4.
Proof.
case=> hA; first exact: seed_cliques_bounded.
have hs : stable A.
  apply/stableP=> x y hx hy; apply/negP=> hxy.
  exact: hA x y hx hy hxy.
have hh := seed_stable_bounded hs.
apply: leq_trans hh _; by [].
Qed.
Lemma seed_chromatic_certificate : chromatic_certificate seed 7.
Proof.
exists ([the finType of 'I_7]), seed_chi_color; split; first exact: card_ord.
split; first exact: seed_chi_proper.
move=> D g hg.
have hb c : #|[set x | g x == c]| <= 2.
  apply: seed_stable_bounded; apply/stableP=> x y.
  rewrite !inE=> /eqP hx /eqP hy; apply/negP=> hxy.
  by have := hg x y hxy; rewrite hx hy eqxx.
have h := fiber_card_bound hb; rewrite seed_card in h.
apply/negPn/negP; rewrite -ltnNge=> hd.
have hd6 : #|D| <= 6 by [].
have hm : #|D| * 2 <= 6 * 2 by rewrite leq_mul2r hd6 orbT.
have h12 := leq_trans h hm.
by [].
Qed.
Lemma seed_cochromatic_certificate : cochromatic_certificate seed 4.
Proof.
exists ([the finType of 'I_4]), seed_co_color, seed_independent_index.
split; first exact: card_ord.
split; first exact: seed_co_homogeneous.
split; first exact: seed_co_independent.
move=> D g hg.
have hb c : #|[set x | g x == c]| <= 4 := seed_homogeneous_bounded (hg c).
have h := fiber_card_bound hb; rewrite seed_card in h.
apply/negPn/negP; rewrite -ltnNge=> hd.
have hd3 : #|D| <= 3 by [].
have hm : #|D| * 4 <= 3 * 4 by rewrite leq_mul2r hd3 orbT.
have h12 := leq_trans h hm.
by [].
Qed.
