(** * Verified finite obstructions for the circulant-complement seed.

    On vertices 0,...,12, adjacency excludes absolute differences
    1,5,8,12, exactly the complement of the undirected circulant C_13(1,5).
    Plain natural-number checkers are evaluated by [vm_compute], with
    ordinary kernel checking of the resulting equalities. Each checker
    has a proved bridge to the graph relation; no external computation
    or unchecked conversion is trusted. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
From Chromatic.applications.cochromatic_gap Require Import clique_bounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Definition seed_nat_rel (x y : nat) :=
  (x != y) && ~~ (((x - y) + (y - x)) \in [:: 1; 5; 8; 12]).
Definition seed_rel (x y : 'I_13) := seed_nat_rel (val x) (val y).
Lemma seed_sym : symmetric seed_rel.
Proof. by move=> x y; rewrite /seed_rel /seed_nat_rel eq_sym addnC. Qed.
Lemma seed_irrefl : irreflexive seed_rel.
Proof. by move=> x; rewrite /seed_rel /seed_nat_rel eqxx. Qed.
Definition seed : sgraph := SGraph seed_sym seed_irrefl.
Definition seed_clique5b a b c d e :=
  [&& seed_nat_rel a b, seed_nat_rel a c, seed_nat_rel a d,
      seed_nat_rel a e, seed_nat_rel b c, seed_nat_rel b d,
      seed_nat_rel b e, seed_nat_rel c d, seed_nat_rel c e & seed_nat_rel d e].
Definition seed_nats := iota 0 13.
Lemma seed_no_clique5_check :
  all (fun a => all (fun b => all (fun c => all (fun d => all
    (fun e => ~~ seed_clique5b a b c d e) seed_nats) seed_nats)
    seed_nats) seed_nats) seed_nats.
Proof. vm_compute. reflexivity. Qed.
Lemma seed_no_stable3_check :
  all (fun a => all (fun b => all (fun c =>
    uniq [:: a; b; c] ==> [|| seed_nat_rel a b, seed_nat_rel a c | seed_nat_rel b c])
    seed_nats) seed_nats) seed_nats.
Proof. vm_compute. reflexivity. Qed.
Lemma seed_nats_mem (x : seed) : val x \in seed_nats.
Proof. by rewrite mem_iota add0n leq0n /=; exact: ltn_ord. Qed.
Lemma seed_no_clique5 : forall a b c d e : seed, ~~ clique5b a b c d e.
Proof.
move=> a b c d e.
exact: (allP (allP (allP (allP (allP seed_no_clique5_check (val a) (seed_nats_mem a))
 (val b) (seed_nats_mem b)) (val c) (seed_nats_mem c)) (val d) (seed_nats_mem d))
 (val e) (seed_nats_mem e)).
Qed.
Lemma seed_no_stable3 : forall a b c : seed,
    uniq [:: a; b; c] -> [|| a -- b, a -- c | b -- c].
Proof.
move=> a b c hu.
have h := allP (allP (allP seed_no_stable3_check (val a) (seed_nats_mem a))
 (val b) (seed_nats_mem b)) (val c) (seed_nats_mem c).
apply: (implyP h).
by move: hu; rewrite /= !inE !val_eqE.
Qed.
Lemma seed_cliques_bounded : forall K : {set seed}, clique K -> #|K| <= 4.
Proof. exact: no_clique5_bound seed_no_clique5. Qed.
Lemma seed_stable_bounded : forall A : {set seed}, stable A -> #|A| <= 2.
Proof. exact: no_stable3_bound seed_no_stable3. Qed.
