(** * Minor.conjectures.grounding_X304 -- grounding certificates for wave X304 (2026-11-12)

    Qed-closed, axiom-free certificates for the one row of [X304.v] (Wood's conjecture on the number of
    cliques in K_t-minor-free graphs): hyp_inhabited and not_trivially_true.  X304 declares no helper, so no
    helper_sanity.
    - hyp: for every t >= 2 and every n, the graph on n vertices with no edge is K_t-minor-free (so the
      hypotheses of both halves are met), and it has n + 1 cliques; the statement then gives, at t = 2, a
      K_2-minor-free graph on n vertices with exactly 2^0 (n + 3 - 2) = n + 1 cliques.
    - ntt: the hypothesis "K_t-minor-free" is load-bearing: the statement gives the t = 2 bound n + 1 for
      K_2-minor-free graphs, and without that hypothesis the bound fails, since K_2 has 4 cliques > 3.
    They validate the statement; they do not prove it. *)

From GTBase Require Import base clique_counts.
From Minor.conjectures Require Import X304.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Edgeless graphs and minors *)

Lemma g304_edgeless_no_minor (G H : sgraph) (x y : H) :
  (forall u w : G, ~~ u -- w) -> x -- y -> ~ minor G H.
Proof.
move=> noe xy [phi [_ _ hE]].
by case: (hE x y xy) => x0 [y0 [_ _]]; rewrite (negbTE (noe x0 y0)).
Qed.

Lemma g304_kb0_noedge (n : nat) (x y : KB n 0) : ~~ x -- y.
Proof. by case: x => [x|[]] //; case: y => [y|[]]. Qed.

Lemma g304_kb0_card (n : nat) : #|KB n 0| = n.
Proof. by rewrite card_sum !card_ord addn0. Qed.

Lemma g304_kb0_no_Kt (n t : nat) : 2 <= t -> ~ minor (KB n 0) 'K_t.
Proof.
case: t => [|[|s]] // _.
by apply: (@g304_edgeless_no_minor _ 'K_s.+2 ord0 ord_max (@g304_kb0_noedge n)); rewrite /edge_rel.
Qed.

(* In a graph with no edge the cliques are the empty set and the singletons. *)
Lemma g304_edgeless_clique_count (G : sgraph) :
  (forall u w : G, ~~ u -- w) -> all_clique_count G = #|G|.+1.
Proof.
move=> noe; rewrite /all_clique_count.
have -> : cliques [set: G] = set0 |: [set [set x] | x in G].
  apply/setP => S; rewrite in_cliquesT !inE; apply/idP/idP.
  - move=> /cliqueP cl; have le1 : #|S| <= 1.
      apply/card_le1_eqP => x y xS yS; apply/eqP; apply: contraNT (noe x y) => xy.
      by apply: cl => //; rewrite eq_sym.
    case: (S =P set0) => [->|S0] //=; have /cards1P [x ->] : #|S| == 1.
      by rewrite eqn_leq le1 card_gt0; apply/eqP.
    by apply/imsetP; exists x.
  - by case/orP => [/eqP -> | /imsetP [x _ ->]]; apply/cliqueP; apply: small_clique; rewrite ?cards0 ?cards1.
rewrite cardsU1 (card_imset _ (@set1_inj G)).
have -> : set0 \notin [set [set x] | x in G].
  by apply/imsetP => -[x _ /esym/eqP]; rewrite -cards_eq0 cards1.
by rewrite add1n.
Qed.

(* ** Complete graphs: every set is a clique *)
Lemma g304_complete_clique_count (n : nat) : all_clique_count 'K_n = 2 ^ n.
Proof.
rewrite /all_clique_count; have -> : cliques [set: 'K_n] = powerset [set: 'K_n].
  apply/setP => S; rewrite in_cliquesT inE subsetT; by apply/cliqueP => x y _ _ xy.
by rewrite card_powerset cardsT card_ord.
Qed.

(* ** hyp_inhabited *)
Definition g304_hyp_claim : Prop :=
  [/\ (forall t n : nat, 2 <= t -> exists G : sgraph, #|G| = n /\ ~ minor G 'K_t),
      (forall n : nat, all_clique_count (KB n 0) = n.+1)
    & (wood_kt_minor_clique_count_statement ->
        forall n : nat, exists G : sgraph,
          [/\ #|G| = n, ~ minor G 'K_2 & all_clique_count G = 2 ^ (2 - 2) * (n + 3 - 2)])].

Theorem g304_hyp_inhabited : g304_hyp_claim.
Proof.
split=> [t n t2|n|S n].
- by exists (KB n 0); split; [exact: g304_kb0_card | exact: g304_kb0_no_Kt].
- by rewrite g304_edgeless_clique_count ?g304_kb0_card //; exact: g304_kb0_noedge.
- exact: ((S 2 isT).2 isT n (leq0n n)).2.
Qed.

(* ** not_trivially_true *)
Definition g304_ntt_claim : Prop :=
  (wood_kt_minor_clique_count_statement ->
     forall (n : nat) (G : sgraph), #|G| = n -> ~ minor G 'K_2 ->
       all_clique_count G <= 2 ^ (2 - 2) * (n + 3 - 2)) /\
  ~ (forall (n : nat) (G : sgraph), #|G| = n -> all_clique_count G <= 2 ^ (2 - 2) * (n + 3 - 2)).

Theorem g304_not_trivially_true : g304_ntt_claim.
Proof.
split.
- by move=> S n G cG nm; exact: ((S 2 isT).2 isT n (leq0n n)).1 G cG nm.
- by move=> /(_ 2 'K_2 (card_ord 2)); rewrite g304_complete_clique_count.
Qed.
