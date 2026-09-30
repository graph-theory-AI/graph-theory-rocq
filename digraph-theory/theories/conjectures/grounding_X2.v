(** * Digraph.conjectures.grounding_X2 — guard-repair grounding for the X2 Mader rows

    GROUNDING for the wave-E4 GUARD REPAIR of the two rows arxiv:1610.00876#00
    ([mader_delta0_transitive_tournament_statement]) and arxiv:1610.00876#01
    ([oriented_trees_delta_plus_maderian_statement]): both quantify their host
    digraph through [mader_delta_zero_bound] / [mader_delta_plus_bound], which now
    carry the guard [0 < #|D|].

    Two things must be shown for a guard to be legitimate:

    1. THE GUARD HAS TEETH — without it the rows are refutable.  The pointwise
       minimum-degree conditions hold VACUOUSLY on the EMPTY digraph, which admits
       no injective branch map out of a nonempty [F]; so the UNGUARDED bodies
       (spelled out in full here, to keep this file free of any refutation of a
       committed row) are FALSE:
       [x2_delta0_unguarded_false], [x2_delta_plus_unguarded_false].
       These are the wave-E3 scratch refutations X2_mader_delta0_false and
       X2_trees_delta_plus_false, ported.

    2. THE GUARD IS NOT VACUOUS — the guarded hypothesis class is inhabited at
       EVERY degree threshold, witnessed by the complete digraph
       ([foundations/subdivision.v: dense_dg]):
       [x2_delta0_hyps_nonvacuous], [x2_delta_plus_hyps_nonvacuous];
       and the antecedent [oriented_tree] of row #01 is inhabited by the one-vertex
       and the one-arc oriented trees: [x2_oriented_tree_TT1], [x2_oriented_tree_TT2].

    Every lemma is closed by [Qed] and axiom-free (audit at the end). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import subdivision.
From Digraph Require Import classic_core chi_bounded heroes path_fas X2.
From Digraph Require Import grounding_heroes_dichotomy grounding_degreewidth_c3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The empty digraph: the host the pointwise degree conditions admit *)

Definition x2_emptyD : Type := 'I_0.
HB.instance Definition _ := Finite.on x2_emptyD.
HB.instance Definition _ := HasArc.Build x2_emptyD (fun _ _ : 'I_0 => false).

Lemma x2_emptyD_card : #|{: x2_emptyD}| = 0.
Proof. exact: card_ord. Qed.

(** No subdivision of a NONEMPTY digraph fits in it: [contains_subdivision]
    requires an injective branch map. *)
Lemma no_subdiv_emptyD (F : diGraphType) : (0 < #|F|)%N ->
  ~ contains_subdivision F (x2_emptyD : diGraphType).
Proof.
move=> hF [branch _]; move/card_gt0P: hF => [x _].
by case: (branch x) => m; rewrite ltn0.
Qed.

Lemma semideg_emptyD (m : nat) : min_semidegree_at_least (x2_emptyD : diGraphType) m.
Proof. by case. Qed.

Lemma outdeg_emptyD (m : nat) : min_outdegree_at_least (x2_emptyD : diGraphType) m.
Proof. by case. Qed.

(** ** 1. The guard has teeth: the UNGUARDED bodies are false *)

(** Row arxiv:1610.00876#00 with [mader_delta_zero_bound] spelled out WITHOUT the
    [0 < #|D|] guard: no [m] is a bound at all, because the empty digraph passes
    every semidegree requirement. *)
Lemma x2_delta0_unguarded_false :
  ~ (forall k : nat, exists m : nat,
       (forall D : diGraphType,
          min_semidegree_at_least D m -> contains_subdivision (TT k) D) /\
       (forall c : nat,
          (forall D : diGraphType,
             min_semidegree_at_least D c -> contains_subdivision (TT k) D) ->
          (m <= c)%N)).
Proof.
move=> H; have [m [hm _]] := H 1.
apply: (no_subdiv_emptyD (F := (TT 1 : diGraphType))) (hm _ (semideg_emptyD m)).
by rewrite card_TT.
Qed.

(** Row arxiv:1610.00876#01 with [mader_delta_plus_bound] spelled out WITHOUT the
    guard: already the one-vertex oriented tree refutes it. *)
Lemma x2_oriented_tree_TT1 : oriented_tree (TT 1 : orientedDigraph).
Proof.
split.
- by rewrite card_TT.
- by move=> u v /arc_asymm ->.
- move=> x y p1 p2.
  have Exy : x = y by apply: I1_eq.
  by case: y / Exy p1 p2 => p1 p2 [/irredxx -> _] [/irredxx -> _].
- by move=> x y _ _; rewrite (I1_eq x y); exact: connect0.
Qed.

Lemma x2_delta_plus_unguarded_false :
  ~ (forall F : orientedDigraph, oriented_tree F ->
       exists m : nat,
         forall D : diGraphType,
           min_outdegree_at_least D m -> contains_subdivision F D).
Proof.
move=> H; have [m hm] := H (TT 1 : orientedDigraph) x2_oriented_tree_TT1.
apply: (no_subdiv_emptyD (F := (TT 1 : diGraphType))) (hm _ (outdeg_emptyD m)).
by rewrite card_TT.
Qed.

(** ** 2. The guarded hypotheses are inhabited at every threshold *)

Lemma x2_delta0_hyps_nonvacuous (m : nat) :
  exists D : diGraphType, (0 < #|D|)%N /\ min_semidegree_at_least D m.
Proof.
exists (dense_dg m : diGraphType); split; first by rewrite card_dense.
by move=> v; rewrite /indeg /Nin outdeg_dense indeg_dense.
Qed.

Lemma x2_delta_plus_hyps_nonvacuous (m : nat) :
  exists D : diGraphType, (0 < #|D|)%N /\ min_outdegree_at_least D m.
Proof.
exists (dense_dg m : diGraphType); split; first by rewrite card_dense.
by move=> v; rewrite outdeg_dense.
Qed.

(** ** The one-arc oriented tree: a non-degenerate witness for [oriented_tree] *)

(** In a two-vertex graph the complement of a vertex is a singleton. *)
Lemma x2_card_TT2_C1 (x : chi_bounded.underlying (TT 2 : diGraphType)) :
  #|[set~ x]| = 1%N.
Proof. by rewrite cardsC1 card_ord. Qed.

Lemma TT2_sdeg_le1 (x : chi_bounded.underlying (TT 2 : diGraphType)) :
  (sdeg x <= 1)%N.
Proof.
have hsub : [set y | x -- y] \subset [set~ x].
  by apply/subsetP=> y; rewrite !inE /chi_bounded.urel => /andP[hxy _]; rewrite eq_sym.
by rewrite /sdeg; apply: (leq_trans (subset_leq_card hsub)); rewrite x2_card_TT2_C1.
Qed.

(** The single arc [0 -> 1] is an oriented tree: its underlying graph is a
    matching, hence a forest ([grounding_degreewidth_c3.v: sdeg_le1_is_forest]),
    and it is connected. *)
Lemma x2_oriented_tree_TT2 : oriented_tree (TT 2 : orientedDigraph).
Proof.
split.
- by rewrite card_TT.
- by move=> u v /arc_asymm ->.
- by apply: sdeg_le1_is_forest => x; exact: TT2_sdeg_le1.
- apply: connectedTI => x y; have [->|hxy] := eqVneq x y; first exact: connect0.
  apply: connect1.
  by rewrite /edge_rel/= /chi_bounded.urel hxy /= !arcTTE -neq_ltn val_eqE.
Qed.

(** ** Print Assumptions audit *)

Print Assumptions no_subdiv_emptyD.
Print Assumptions x2_delta0_unguarded_false.
Print Assumptions x2_delta_plus_unguarded_false.
Print Assumptions x2_delta0_hyps_nonvacuous.
Print Assumptions x2_delta_plus_hyps_nonvacuous.
Print Assumptions x2_oriented_tree_TT1.
Print Assumptions x2_oriented_tree_TT2.
