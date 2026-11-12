(** * Minor.conjectures.implications_X271 -- two Rocq-only edges from X214's rows into X271's.

    Wave X271 encodes, among its rows, Hajos' conjecture at five (studies:std_haj_s_conjecture_k_5,
    [hajos_k5_subdivision_statement]) and Seymour's H-Hadwiger conjecture (studies:std_h_hadwiger_conjecture,
    [h_hadwiger_minor_free_colourable_statement]).  Wave X214 encodes the Bondy-Murty rows bm:bm-042 (Hajos for
    k = 5 and k = 6, [hajos_k5_k6_subdivision_statement]) and bm:bm-041 (Hadwiger,
    [hadwiger_chromatic_clique_minor_statement]).  The theorems below record two Rocq-only implication edges
    (meta/corpus_relations.json joins neither pair):
    - Hajos at k = 5 and 6 => Hajos at k = 5: the instance k = 5, with the same exact chromatic number and the same
      subdivision containment (X271's Notes name it a candidate edge);
    - Hadwiger => H-Hadwiger, which Fischer and Steiner note (arXiv:2304.04246v1, text l.73): if G has no H minor
      and #|H| <= chi(G), Hadwiger at chi(G) gives a minor of the complete graph on chi(G) vertices, which has H as
      a subgraph, so G would have an H minor; hence chi(G) <= #|H| - 1.
    Neither converse is claimed (over all H, the converse of the second needs minor to be decidable).
    Axiom-free: only [Qed]-closed results, and no helper of its own. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.conjectures Require Import X214 X271.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Hajos at k = 5 and 6 (X214, bm:bm-042) ==> Hajos at k = 5 (X271) *)

(*@EDGE from=hajos_k5_k6_subdivision_statement to=hajos_k5_subdivision_statement kind=implies status=verified proof=hajos_k5_k6_subdivision_implies_hajos_k5_subdivision note="Rocq-only edge (no corpus relation), routed after wave X271 (Lancelot's (685), (686)): bm:bm-042 states Hajos' conjecture for k = 5 and k = 6; its instance k = 5 is studies:std_haj_s_conjecture_k_5, with the same exact chromatic number and the same subdivision containment (has_subdivision); X271's Notes name it a candidate edge." *)
Theorem hajos_k5_k6_subdivision_implies_hajos_k5_subdivision :
  hajos_k5_k6_subdivision_statement -> hajos_k5_subdivision_statement.
Proof.
move=> hajos G chiG.
exact: (hajos 5 G (or_introl erefl) chiG).
Qed.

(** ** Hadwiger (X214, bm:bm-041) ==> H-Hadwiger (X271) *)

(*@EDGE from=hadwiger_chromatic_clique_minor_statement to=h_hadwiger_minor_free_colourable_statement kind=implies status=verified proof=hadwiger_chromatic_clique_minor_implies_h_hadwiger_minor_free_colourable note="Rocq-only edge (no corpus relation), routed after wave X271 (Lancelot's (685), (686)): Hadwiger's conjecture implies Seymour's H-Hadwiger conjecture for every H (Fischer and Steiner, arXiv:2304.04246v1, text l.73). If G has no H minor and #|H| <= chi(G), Hadwiger at chi(G) gives a minor of the complete graph on chi(G) vertices; H is a subgraph of it (widen_ord after enum_rank, injective, and distinct vertices are adjacent there), so sub_minor and minor_trans give an H minor, a contradiction; otherwise chi(G) <= #|H| - 1. The H with no vertex falls in the first case." *)
Theorem hadwiger_chromatic_clique_minor_implies_h_hadwiger_minor_free_colourable :
  hadwiger_chromatic_clique_minor_statement -> h_hadwiger_minor_free_colourable_statement.
Proof.
move=> had H G nHG.
case: (leqP #|H| χ([set: G])) => [le|lt]; last by move: lt; case: #|H|.
exfalso; apply: nHG; apply: (minor_trans (had _ G erefl)); apply: sub_minor.
exists (fun x : H => widen_ord le (enum_rank x)).
  by move=> x y /(congr1 val) /= /val_inj /enum_rank_inj.
by move=> x y _ ne.
Qed.
