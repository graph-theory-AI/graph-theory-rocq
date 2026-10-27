(** * Chromatic.conjectures.grounding_X249 -- grounding certificates of wave X249.

    For the one row (arxiv:2202.09118#02, a synonym of X218's every_forest_is_good_statement):
    hyp_inhabited (the one-vertex graph is a forest, and the statement then yields its conclusion
    there) and not_trivially_true in the contract form of meta/EXPANSION_PLAN.md 4.4: the variant
    dropping the forest hypothesis is false and implies the row.  The variant fails at H = K_5:
    the iterated Mycielski graphs of Chromatic.applications.cochromatic_gap have every clique of
    size at most 4 ([gap_graph_clique_bound]), so no induced K_5, clique number 4 and chromatic
    number n + 7 ([gap_graph_parameters]), and n = c * 4^d beats any bound c * omega^d.  The wave
    has no local helper, so no helper_sanity certificate. *)

From GraphTheory Require Import bij.
From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U8 X218 X249.
From Chromatic.applications.cochromatic_gap Require Import mycielski_gap cochromatic_gap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** An induced complete graph is a clique *)

(** An induced copy of K_n is a clique on n vertices. *)
Lemma g249_induced_Kn_clique (G : sgraph) (n : nat) (S : {set G}) :
  'K_n ≃ induced S -> clique S /\ #|S| = n.
Proof.
move=> i; split.
- move=> x y xS yS xy.
  have -> : x -- y = (Sub x xS : induced S) -- (Sub y yS) by rewrite induced_edge.
  rewrite -(edge_diso' i) /=; apply/negP => /eqP h; move/eqP: xy; apply.
  by have := congr1 (bij_fwd i) h; rewrite !bijK' => /(congr1 val); rewrite !SubK.
- have := card_bij (diso_v i); rewrite card_ord card_sig => ->.
  by apply: eq_card => x; rewrite !inE.
Qed.

(** The iterated Mycielski graphs are K_5-free. *)
Lemma g249_gap_graph_K5_free (n : nat) : ~ has_induced 'K_5 (gap_graph n).
Proof.
case=> S [i]; have [cS eS] := g249_induced_Kn_clique i.
by have := gap_graph_clique_bound cS; rewrite eS.
Qed.

(** ** hyp_inhabited *)

Definition g249_hyp_claim : Prop :=
  is_forest [set: sunit] /\
  (every_forest_is_good_duplicate_statement ->
     poly_chi_bounded (fun G : sgraph => ~ has_induced sunit G)).

Theorem g249_hyp_inhabited : g249_hyp_claim.
Proof. by split; [exact: unit_forest | move=> h; exact: h _ unit_forest]. Qed.

(** ** not_trivially_true: the forest hypothesis dropped *)

Definition g249_any_graph_good : Prop :=
  forall H : sgraph, poly_chi_bounded (fun G : sgraph => ~ has_induced H G).

Definition g249_ntt_claim : Prop :=
  ~ g249_any_graph_good /\ (g249_any_graph_good -> every_forest_is_good_duplicate_statement).

Theorem g249_not_trivially_true : g249_ntt_claim.
Proof.
split; last by move=> h H _; exact: h H.
move=> h; have [c [d hb]] := h 'K_5.
have := hb _ (g249_gap_graph_K5_free (c * 4 ^ d)).
case: (gap_graph_parameters (c * 4 ^ d)) => -> [_ ->].
by rewrite -{2}[c * 4 ^ d]addn0 leq_add2l.
Qed.
