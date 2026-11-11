(** * Minor.conjectures.grounding_X300 -- grounding certificates for wave X300 (2026-11-11)

    Qed-closed, axiom-free certificates for the one row of [X300.v] (Grytczuk's conjecture): hyp_inhabited and
    not_trivially_true.  X300 declares no helper, so no helper_sanity.
    - [g300_nonrep col]: the statement's nonrepetitive condition on one colouring;
      [g300_class_bounded X k]: the statement's body at one X and one k.
    - hyp: K_1 is K_2-minor-free (minor_card), every K_2-minor-free graph is edgeless and so has a nonrepetitive
      1-colouring (no path on two or more vertices), and the statement gives a bound for X = K_2.
    - ntt: the variant "one k bounds pi of every graph" implies the row and is false: a k-colouring of K_(k+1)
      gives two vertices the same colour, and those two adjacent vertices are a repetitively coloured path.
    They validate the statement; they do not prove it. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.conjectures Require Import X300.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** The statement's parts *)

Definition g300_nonrep (G : sgraph) (k : nat) (col : G -> 'I_k) : Prop :=
  forall (p : seq G) (t : nat),
    seq_simple_path p -> size p = 2 * t -> 0 < t ->
    map col (take t p) != map col (drop t p).

Definition g300_class_bounded (X : sgraph) (k : nat) : Prop :=
  forall G : sgraph, ~ minor G X -> exists col : G -> 'I_k, g300_nonrep col.

(* ** Facts *)

(* No nonrepetitive k-colouring of K_(k+1): two vertices share a colour and form a path on two vertices. *)
Lemma g300_complete_not_nonrep (k : nat) (col : 'K_k.+1 -> 'I_k) : ~ g300_nonrep col.
Proof.
move=> Hc.
have /injectivePn [x [y xy cxy]] : ~~ injectiveb col.
  apply/negP => /injectiveP inj; have := leq_card col inj.
  by rewrite !card_ord ltnn.
have := Hc [:: x; y] 1 _ erefl isT.
move=> H; suff sp : seq_simple_path [:: x; y] by move: (H sp); rewrite /= cxy eqxx.
split; first by rewrite /= inE andbT.
by rewrite /= andbT.
Qed.

(* An edge gives a K_2 minor (branch sets [set x] and [set y]). *)
Lemma g300_edge_K2_minor (G : sgraph) (x y : G) : x -- y -> minor G 'K_2.
Proof.
move=> xy.
have xny : x != y by apply: contraTneq xy => ->; rewrite sgP.
apply: (@minor_of_rmap _ _ (fun i : 'K_2 => if i == ord0 then [set x] else [set y])); split.
- by move=> i; case: ifP => _; apply/set0Pn; [exists x | exists y]; rewrite set11.
- by move=> i; case: ifP => _; exact: connected1.
- move=> [[|[|i]] Hi] [[|[|j]] Hj] //= _; rewrite disjoints1 inE; first exact: xny.
  by rewrite eq_sym.
- move=> [[|[|i]] Hi] [[|[|j]] Hj] //= _.
    by apply/neighborP; exists x, y; rewrite !set11.
  by apply/neighborP; exists y, x; rewrite !set11 sgP.
Qed.

(* In an edgeless graph every colouring is nonrepetitive: a path on 2t >= 2 vertices would start with an edge. *)
Lemma g300_edgeless_nonrep (G : sgraph) (k : nat) (col : G -> 'I_k) :
  (forall x y : G, ~~ (x -- y)) -> g300_nonrep col.
Proof.
move=> E [|x [|y q]] t //=.
  by move=> _; case: t => [|t] //; rewrite muln_eq0.
by case=> _ /andP[xy _]; rewrite (negbTE (E x y)) in xy.
Qed.

(* ** hyp_inhabited: K_1 is K_2-minor-free, every K_2-minor-free graph has a nonrepetitive 1-colouring, and the
   statement gives a bound for X = K_2. *)
Definition g300_hyp_claim : Prop :=
  [/\ ~ minor ('K_1) ('K_2), g300_class_bounded ('K_2) 1
    & grytczuk_minor_free_nonrepetitive_statement -> exists k, g300_class_bounded ('K_2) k].

Theorem g300_hyp_inhabited : g300_hyp_claim.
Proof.
split.
- by move/minor_card; rewrite !card_ord.
- move=> G nK2; exists (fun _ => ord0).
  apply: g300_edgeless_nonrep => x y; apply/negP => xy.
  by apply: nK2; exact: g300_edge_K2_minor xy.
- by move=> S; exact: S.
Qed.

(* ** not_trivially_true: "one k bounds pi of every graph" implies the row and fails at K_(k+1). *)
Definition g300_all_bounded : Prop :=
  exists k : nat, forall G : sgraph, exists col : G -> 'I_k, g300_nonrep col.

Definition g300_ntt_claim : Prop :=
  ~ g300_all_bounded /\ (g300_all_bounded -> grytczuk_minor_free_nonrepetitive_statement).

Theorem g300_not_trivially_true : g300_ntt_claim.
Proof.
split.
- by case=> k Hk; have [col Hc] := Hk ('K_k.+1); exact: g300_complete_not_nonrep Hc.
- by case=> k Hk X; exists k => G _; exact: Hk G.
Qed.
