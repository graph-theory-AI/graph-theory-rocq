(** * Formal solution to arXiv:2408.02400, Problem 1.5.

    The seed is the complement of C_13(1,5). Iterated Mycielski
    constructions preserve clique number four and increase the exact
    chromatic and cochromatic numbers together.

    Source: Graph-Theory-LLM-Proofs/attacks/2408.02400__00/output.md.
    The final theorem has exactly the existing X7 statement type. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
From GTBase Require Import base.
From Chromatic.conjectures Require Import XE1 XE2 X7.
From Chromatic.applications.cochromatic_gap Require Import mycielski_gap seed_certificates seed_colorings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition has_clique_four (G : sgraph) :=
  exists K : {set G}, clique K /\ #|K| = 4.
Definition s0 : seed := @Ordinal 13 0 erefl.
Definition s2 : seed := @Ordinal 13 2 erefl.
Definition s4 : seed := @Ordinal 13 4 erefl.
Definition s6 : seed := @Ordinal 13 6 erefl.
Definition seed_four : {set seed} := s0 |: (s2 |: (s4 |: [set s6])).
Lemma seed_four_card : #|seed_four| = 4.
Proof. by rewrite /seed_four !cardsU1 cards1 !inE. Qed.
Lemma seed_four_clique : clique seed_four.
Proof.
move=> x y; rewrite /seed_four !inE=> /or4P hx /or4P hy.
by case: hx=> /eqP ->; case: hy=> /eqP ->.
Qed.
Lemma seed_has_clique_four : has_clique_four seed.
Proof. by exists seed_four; split; [exact: seed_four_clique|exact: seed_four_card]. Qed.
Lemma mycielski_has_clique_four G : has_clique_four G -> has_clique_four (mycielski G).
Proof.
move=> [K [hK hk]]; exists ((@old G) @: K); split.
- move=> _ _ /imsetP[x hx ->] /imsetP[y hy ->] hxy.
  rewrite old_edge; apply: hK=> //.
- by rewrite (card_imset K (@old_inj G)) hk.
Qed.
Lemma omega_four (G : sgraph) :
  (forall K : {set G}, clique K -> #|K| <= 4) ->
  has_clique_four G -> ω([set: G]) = 4.
Proof.
move=> hb [K [hK hk]]; apply/eqP; rewrite eqn_leq.
apply/andP; split; first exact: omega_from_cliques hb.
rewrite -hk; apply: clique_bound.
by rewrite inE subsetT /=; apply/cliqueP.
Qed.

Fixpoint gap_graph (n : nat) : sgraph :=
  if n is n'.+1 then mycielski (gap_graph n') else seed.
Lemma gap_graph_nonempty n : 0 < #|gap_graph n|.
Proof.
case: n=> [|n]; first exact: seed_nonempty.
apply/card_gt0P; exists (@root (gap_graph n)); by rewrite inE.
Qed.
Lemma gap_graph_clique_bound n :
  forall K : {set gap_graph n}, clique K -> #|K| <= 4.
Proof.
elim: n=> [|n ih]; first exact: seed_cliques_bounded.
apply: mycielski_cliques_bounded=> //.
exact: gap_graph_nonempty.
Qed.
Lemma gap_graph_clique_four n : has_clique_four (gap_graph n).
Proof.
elim: n=> [|n ih]; first exact: seed_has_clique_four.
exact: mycielski_has_clique_four.
Qed.
Lemma gap_graph_cochromatic_certificate n :
  cochromatic_certificate (gap_graph n) (n + 4).
Proof.
elim: n=> [|n ih]; first exact: seed_cochromatic_certificate.
rewrite addSn; exact: mycielski_cochromatic_certificate.
Qed.
Lemma gap_graph_chromatic_certificate n :
  chromatic_certificate (gap_graph n) (n + 7).
Proof.
elim: n=> [|n ih]; first exact: seed_chromatic_certificate.
rewrite addSn; apply: mycielski_chromatic_certificate=> //.
exact: gap_graph_nonempty.
Qed.
Theorem gap_graph_parameters n :
  ω([set: gap_graph n]) = 4 /\
  xe2_cochromatic_number (gap_graph n) (n + 4) /\
  χ([set: gap_graph n]) = n + 7.
Proof.
split.
- apply: omega_four; [exact: gap_graph_clique_bound|exact: gap_graph_clique_four].
split.
- exact: cochromatic_certificate_exact (gap_graph_cochromatic_certificate n).
- exact: chromatic_certificate_exact (gap_graph_chromatic_certificate n).
Qed.

Theorem cochromatic_gap_three_proved : cochromatic_gap_three_statement.
Proof.
move=> k hk; exists (gap_graph (k - 4)).
have [ho [hz hc]] := gap_graph_parameters (k - 4).
have hk4 : 4 <= k := leq_trans (leqnSn 4) hk.
have he : k - 4 + 4 = k by rewrite subnK.
split; first by rewrite ho.
split; first by rewrite he in hz.
by rewrite -[7]/(4 + 3) addnA he in hc.
Qed.

Print Assumptions cochromatic_gap_three_proved.
Print Assumptions gap_graph_parameters.
