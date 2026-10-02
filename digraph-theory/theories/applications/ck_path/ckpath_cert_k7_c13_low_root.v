(** * A low-cycle-degree root for the k=7 C13 certificates

    The raw C13 formulas leave the active set unspecified, while fixing all
    active-set bits creates 22, 55, and 99 separate cyclic-orbit obligations.
    There is a stronger normalization that avoids both extremes.  The
    thirteen-cycle sends at least thirteen arcs outside, all from active
    gateways.  Since every vertex has outdegree seven, the active gateways
    have total cycle outdegree at most [7 * #|A| - 13].  Consequently one
    active gateway has cycle outdegree at most [#|A| - 1].  Rooting there
    bounds its ten-variable internal row by [#|A| - 2].  Choosing the outside
    witness of that active root additionally fixes covered vertex zero. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import prelude digraph oriented dipath strong
  ckpath_cycle_tools ckpath_odd_gateway ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_clause_tools ckpath_cert_k7_base
  ckpath_cert_graph_common ckpath_cert_graph_k7_c13_semantics.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The certificate base appends the forced root mark and the cardinality
    encoding for row zero. *)
Definition c13_k7_low_root_base (active_size : nat) : cnf :=
  c13_k7_cover_base active_size ++
  [[positive_literal (mark_var 13 0)]] ++
  at_most_comb [] (active_size - 2) (internal_row 13 0).

Lemma c13_k7_low_root3_base_clause_count :
  List.length (c13_k7_low_root_base 3) = 13944.
Proof. vm_compute. reflexivity. Qed.

Lemma c13_k7_low_root4_base_clause_count :
  List.length (c13_k7_low_root_base 4) = 14799.
Proof. vm_compute. reflexivity. Qed.

Lemma c13_k7_low_root5_base_clause_count :
  List.length (c13_k7_low_root_base 5) = 15747.
Proof. vm_compute. reflexivity. Qed.

Section C13LowRootGraphBridge.
Variable D : orientedDigraph.
Variables (c : list D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D < 14.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 13.
Hypothesis HScard : #|S| = 7.
Hypothesis HSsub : S \subset odd_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in odd_cycle_set c.
Hypothesis Horder : 15 <= #|D|.

Local Notation C := (odd_cycle_set c).
Local Notation R := (odd_outside c).
Local Notation A := (odd_active_set c).
Local Notation eCR := (odd_cross_arcs c).

Lemma c13_k7_low_root_active_subset_cycle : A \subset C.
Proof.
apply: (subset_trans
  (@odd_active_subset_gateway D c S HSclosed)).
apply/subsetP=> q.
by rewrite /odd_gateway_set inE => /andP[].
Qed.

Lemma c13_k7_low_root_cycle_card : #|C| = 13.
Proof.
by rewrite /C /odd_cycle_set (dicycle_set_card Hcycle) Hcsize.
Qed.

(** Inactive cycle vertices send no arcs outside, so every cross arc is
    contributed by an active gateway. *)
Lemma c13_k7_low_root_cross_active_sum :
  eCR = \sum_(q in A) outdeg_in R q.
Proof.
rewrite /eCR /odd_cross_arcs (bigID (mem A)) /=.
have firstE :
    \sum_(q in C | q \in A) outdeg_in R q =
    \sum_(q in A) outdeg_in R q.
  apply: eq_bigl => q.
  case qA: (q \in A).
  - have qC := subsetP c13_k7_low_root_active_subset_cycle q qA.
    by rewrite qC.
  - by rewrite andbF.
rewrite firstE.
have -> : \sum_(q in C | q \notin A) outdeg_in R q = 0.
  apply: big1 => q /andP[qC qNA].
  case hqR: (outdeg_in R q) => [|r] //.
  exfalso; move: qNA.
  rewrite /A /odd_active_set inE qC hqR /=.
  by [].
by rewrite addn0.
Qed.

(** Sum the seven-outregular degree equation over the active gateways. *)
Lemma c13_k7_low_root_active_degree_balance :
  (\sum_(q in A) outdeg_in C q) +
  (\sum_(q in A) outdeg_in R q) = 7 * #|A|.
Proof.
rewrite -big_split /=.
under eq_bigr do rewrite -outdeg_split_set Hreg.
by rewrite sum_nat_const mulnC.
Qed.

(** The thirteen-cycle sends at least thirteen arcs outside. *)
Lemma c13_k7_low_root_cross_lower : 13 <= eCR.
Proof.
have hsplit :
    (\sum_(q in C) 7) = (\sum_(q in C) outdeg_in C q) + eCR.
  rewrite /eCR /odd_cross_arcs -big_split /=.
  apply: eq_bigr => q qC.
  rewrite -(Hreg q).
  exact: outdeg_split_set C q.
have hbound :
    2 * (\sum_(q in C) outdeg_in C q) <= #|C| * (#|C| - 1) :=
  oriented_arcs_bound C.
rewrite sum_nat_const c13_k7_low_root_cycle_card in hsplit.
rewrite c13_k7_low_root_cycle_card in hbound.
apply/leP.
by lia.
Qed.

Lemma c13_k7_low_root_active_internal_plus13 :
  (\sum_(q in A) outdeg_in C q) + 13 <= 7 * #|A|.
Proof.
have hcross : 13 <= \sum_(q in A) outdeg_in R q.
  rewrite -c13_k7_low_root_cross_active_sum.
  exact: c13_k7_low_root_cross_lower.
have h := leq_add (leqnn (\sum_(q in A) outdeg_in C q)) hcross.
by rewrite c13_k7_low_root_active_degree_balance in h.
Qed.

(** Some active gateway has cycle outdegree at most [#|A| - 1]. *)
Lemma c13_k7_low_active_root :
  exists2 q, q \in A & outdeg_in C q <= #|A| - 1.
Proof.
have rangeA : 3 <= #|A| <= 5.
  exact: (@odd_gateway_d7_active345 D 7 c S isT Hreg Hstr Hell
            Hcycle Hcsize HScard HSsub HSclosed Horder erefl).
move/andP: rangeA => [lowerA upperA].
case: (boolP [exists q in A, outdeg_in C q <= #|A| - 1]) =>
    [/exists_inP[q qA qle] | Hnone].
- by exists q.
rewrite negb_exists_in in Hnone.
move/forall_inP: Hnone => Hgt.
exfalso.
have Apos : 0 < #|A|.
  by lia.
have sumlo :
    #|A| * (#|A| - 1).+1 <= \sum_(q in A) outdeg_in C q.
  rewrite -sum_nat_const.
  apply: leq_sum => q qA.
  move: (Hgt q qA).
  by rewrite -ltnNge.
rewrite subn1 (prednK Apos) in sumlo.
have totalLo := leq_add sumlo (leqnn 13).
have totalHi := c13_k7_low_root_active_internal_plus13.
have impossible := leq_trans totalLo totalHi.
by nia.
Qed.

(** The graph counterexample realizes one of the three strengthened bases. *)
Theorem ckpath_k7_c13_graph_satisfies_low_root_base :
  exists m rho,
    [ /\ m = 3 \/ m = 4 \/ m = 5,
        #|A| = m
      & satisfies_cnf rho (c13_k7_low_root_base m) ].
Proof.
have rangeA : 3 <= #|A| <= 5.
  exact: (@odd_gateway_d7_active345 D 7 c S isT Hreg Hstr Hell
            Hcycle Hcsize HScard HSsub HSclosed Horder erefl).
move/andP: rangeA => [lowerA upperA].
have cardA345 : #|A| = 3 \/ #|A| = 4 \/ #|A| = 5 by lia.
have [root rootA rootDeg] := c13_k7_low_active_root.
have rootC := subsetP c13_k7_low_root_active_subset_cycle root rootA.
have rootc : root \in c by move: rootC; rewrite /C /odd_cycle_set inE.
have [y yR rooty] : exists2 y, y \in R & root --> y.
  exact: (@odd_active_witness D c root rootA).
set rho := c13_k7_graph_valuation c root y.
have Hbase : satisfies_cnf rho (c13_k7_cover_base #|A|).
  exact: (@ckpath_k7_c13_graph_cover_base_satisfied_at_root
    D c S Hreg Hstr Hell Hcycle Hcsize HScard HSsub HSclosed Horder
    root y rootc rootA yR).
have Hmark0Val : rho (mark_var 13 0) = true.
  rewrite /rho /c13_k7_graph_valuation
    (@cycle_graph_valuation_mark D c root 13 _ _ 0)
    (ckpath_rotation_paths.rooted_cycle_root rootc)
    (arc_asymm _ _ rooty).
  reflexivity.
have Hmark0 : satisfies_cnf rho [[positive_literal (mark_var 13 0)]].
  unfold satisfies_cnf, eval_cnf, eval_clause, eval_literal,
    positive_literal.
  simpl.
  by rewrite Hmark0Val.
have rowE :
    count_true rho (internal_row 13 0) = outdeg_in C root - 1.
  rewrite /rho /c13_k7_graph_valuation.
  apply: (@cycle_graph_valuation_internal_row_count_in
    D c root 13 0
    (fun i => ckpath_rotation_paths.cycle_label c root i \in A)
    (fun i => ~~ (y --> ckpath_rotation_paths.cycle_label c root i))
    (outdeg_in C root)).
  - lia.
  - exact Hcycle.
  - exact Hcsize.
  - exact rootc.
  - lia.
  - by rewrite (ckpath_rotation_paths.rooted_cycle_root rootc).
have rowLe : count_true rho (internal_row 13 0) <= #|A| - 2.
  rewrite rowE.
  lia.
have Hrow : satisfies_cnf rho
    (at_most_comb [] (#|A| - 2) (internal_row 13 0)).
  apply: at_most_comb_complete.
  right; apply/leP; exact rowLe.
have Hstrength : satisfies_cnf rho (c13_k7_low_root_base #|A|).
  change (satisfies_cnf rho
    (c13_k7_cover_base #|A| ++
      [[positive_literal (mark_var 13 0)]] ++
      at_most_comb [] (#|A| - 2) (internal_row 13 0))).
  apply: (proj2 (satisfies_cnf_app rho _ _)); split; first exact Hbase.
  apply: (proj2 (satisfies_cnf_app rho _ _)); split.
  - exact Hmark0.
  - exact Hrow.
exists #|A|, rho.
by split.
Qed.

End C13LowRootGraphBridge.
