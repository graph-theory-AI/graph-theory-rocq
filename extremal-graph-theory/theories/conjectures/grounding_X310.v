(** * Extremal.conjectures.grounding_X310 -- grounding certificates of wave X310.

    hyp_inhabited and not_trivially_true (the contract form: a variant obtained from the body by deleting one hypothesis
    is false and implies the row) for the one row; the wave adds no helper, so there is no helper_sanity.
    - Hypotheses: the 5-cycle C_5 (GTBase cycle_graph 5) is triangle-free and subcubic and contains none of the six
      graphs (grounding_X309's g309_C5_triangle_free, g309_C5_subcubic and g309_C5_no_forbidden), and it has the
      (5:2)-fold colouring v |-> {2v, 2v + 1} (mod 5), checked by vm_compute on grounding_X309's explicit vertex list:
      5 * 3 <= 8 * 2, so the conclusion holds for it, and the statement gives it too.
    - Without the forbidden-subgraph hypothesis the statement fails at F_11 (x287_bb_graph ord0), which is
      triangle-free and subcubic with alpha(F_11) <= 4 (X287's g287_f11_triangle_free, g287_f11_subcubic and
      g287_f11_alpha): every (a:b)-fold colouring of a graph G has #|G| * b <= a * alpha(G) ([g310_bfold_n_alpha]:
      the a colour classes are stable and cover every vertex b times; the proof of Atlas.foundations.fractional's
      bfold_n_alpha, which extremal-graph-theory cannot import), so 11 b <= 4 a, and with 3 a <= 8 b that forces
      b = 0. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base common bfold_colourings.
From Extremal.conjectures Require Import X287 grounding_X287 grounding_X309 X310.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** C_5 and its (5:2)-fold colouring *)

Local Notation C5 := (cycle_graph 5).

Definition g310_c (k : nat) : 'I_5 := Ordinal (ltn_pmod k (isT : 0 < 5)).

Definition g310_col (v : C5) : {set 'I_5} := [set g310_c (2 * (v : 'I_5)); g310_c (2 * (v : 'I_5)).+1].

Lemma g310_col_bfold : bfold_colouring 2 g310_col.
Proof.
rewrite /bfold_colouring /g310_col; split=> [v | x y xy].
  have h : all (fun v : C5 => g310_c (2 * (v : 'I_5)) != g310_c (2 * (v : 'I_5)).+1) g309_c5
    by vm_compute.
  by rewrite cards2 (allP h v (g309_c5_all v)).
have h : all (fun x : C5 => all (fun y : C5 => (x -- y) ==>
           [&& g310_c (2 * (x : 'I_5)) != g310_c (2 * (y : 'I_5)),
               g310_c (2 * (x : 'I_5)) != g310_c (2 * (y : 'I_5)).+1,
               g310_c (2 * (x : 'I_5)).+1 != g310_c (2 * (y : 'I_5)) &
               g310_c (2 * (x : 'I_5)).+1 != g310_c (2 * (y : 'I_5)).+1])
           g309_c5) g309_c5 by vm_compute.
move: h => /allP/(_ x (g309_c5_all x))/allP/(_ y (g309_c5_all y))/implyP/(_ xy).
case/and4P => /negbTE h1 /negbTE h2 /negbTE h3 /negbTE h4.
apply/disjointP => c; rewrite !inE => /orP [] /eqP -> /orP [] /eqP E;
  [by rewrite E eqxx in h1 | by rewrite E eqxx in h2 | by rewrite E eqxx in h3 | by rewrite E eqxx in h4].
Qed.

(** hyp_inhabited: C_5 meets the three hypotheses, its (5:2)-fold colouring witnesses the conclusion, and the
    statement gives the conclusion for it. *)
Definition g310_hyp_claim : Prop :=
  [/\ triangle_free C5, subcubic C5, (forall i : 'I_6, ~ has_subgraph C5 (x287_bb_graph i)),
      exists (a b : nat) (f : C5 -> {set 'I_a}), [/\ 0 < b, bfold_colouring b f & a * 3 <= 8 * b] &
      (cames_van_batenburg_forbidden_subgraph_fractional_statement ->
         exists (a b : nat) (f : C5 -> {set 'I_a}), [/\ 0 < b, bfold_colouring b f & a * 3 <= 8 * b])].

Theorem g310_hyp_inhabited : g310_hyp_claim.
Proof.
split; [exact: g309_C5_triangle_free | exact: g309_C5_subcubic | exact: g309_C5_no_forbidden | |].
- by exists 5, 2, g310_col; split=> //; exact: g310_col_bfold.
- by move=> h; apply: h; [exact: g309_C5_triangle_free | exact: g309_C5_subcubic | exact: g309_C5_no_forbidden].
Qed.

(** ** not_trivially_true: the forbidden-subgraph hypothesis is needed *)

(** An (a:b)-fold colouring has #|G| * b <= a * alpha(G): the colour classes are stable and cover every vertex b
    times (Atlas.foundations.fractional's bfold_n_alpha, the same proof). *)
Lemma g310_bfold_n_alpha (G : sgraph) a b (f : G -> {set 'I_a}) :
  bfold_colouring b f -> #|G| * b <= a * α([set: G]).
Proof.
case=> cf df.
have stab (c : 'I_a) : stable [set v | c \in f v].
  apply/stableP => x y; rewrite !inE => cx cy; apply/negP => xy.
  by rewrite (disjointFr (df x y xy) cx) in cy.
have e : #|G| * b = \sum_(c < a) #|[set v | c \in f v]|.
  transitivity (\sum_(v : G) #|f v|).
    by under eq_bigr => v _ do rewrite cf; rewrite sum_nat_const.
  under eq_bigr => v _ do rewrite -sum1_card big_mkcond.
  rewrite exchange_big; apply: eq_bigr => c _.
  by rewrite -sum1_card [RHS]big_mkcond; apply: eq_bigr => v _; rewrite inE.
rewrite e -[X in _ <= X * _](card_ord a) -sum_nat_const.
by apply: leq_sum => c _; apply: stabset_bound; apply/stabsetsP; split => //; exact: stab.
Qed.

Definition g310_without_forbidden : Prop :=
  forall G : sgraph, triangle_free G -> subcubic G ->
    exists (a b : nat) (f : G -> {set 'I_a}), [/\ 0 < b, bfold_colouring b f & a * 3 <= 8 * b].

Definition g310_ntt_claim : Prop :=
  ~ g310_without_forbidden /\
  (g310_without_forbidden -> cames_van_batenburg_forbidden_subgraph_fractional_statement).

Theorem g310_not_trivially_true : g310_ntt_claim.
Proof.
split; last by move=> h G t s _; exact: h.
move=> h; have [a [b [f [b0 hf ab]]]] := h _ g287_f11_triangle_free g287_f11_subcubic.
have cnt := g310_bfold_n_alpha hf; rewrite g287_f11_card in cnt.
have c11 : 11 * b <= a * 4.
  by apply: leq_trans cnt _; rewrite leq_mul2l g287_f11_alpha orbT.
clear cnt hf; lia.
Qed.
