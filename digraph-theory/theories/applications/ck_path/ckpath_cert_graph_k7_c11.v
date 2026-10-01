(** * Graph-to-certificate bridge for the CK k=7 C11, a=3 endgame *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cycle_tools ckpath_kernel_prefix_adapters ckpath_k7_c11_hand
  ckpath_cert_base ckpath_cnf ckpath_cert_clause_tools
  ckpath_cert_k7_base ckpath_cert_k7_clause_tools ckpath_cert_projection_k7
  ckpath_rotation_paths ckpath_cert_graph_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Lemma c11_k7_internal_row_length endpoint :
  (endpoint < 11)%coq_nat -> List.length (internal_row 11 endpoint) = 8.
Proof.
intros Hlt.
do 11 (destruct endpoint as [|endpoint]; [vm_compute; reflexivity |]).
lia.
Qed.

Section C11GraphBridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}) (v0 v1 v2 : D).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hell : ell D = 13.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 11.
Hypothesis HScard : #|S| = 6.
Hypothesis Hprefix : ckpath_prefix3_data c S v0 v1 v2.

Local Lemma HSsub : S \subset c11_k7_cycle_set c.
Proof. exact: prefix3_S_subset Hprefix. Qed.

Local Lemma HSclosed :
  forall s z, s \in S -> s --> z -> z \in c11_k7_cycle_set c.
Proof. exact: prefix3_S_closed Hprefix. Qed.

Local Lemma Hv0R : v0 \in c11_k7_outside c.
Proof. exact: prefix3_v0_outside Hprefix. Qed.

Local Lemma Hv1R : v1 \in c11_k7_outside c.
Proof. exact: prefix3_v1_outside Hprefix. Qed.

Local Lemma Hv2R : v2 \in c11_k7_outside c.
Proof. exact: prefix3_v2_outside Hprefix. Qed.

Local Notation Bad := (c11_k7_bad_endpoints c S).
Local Notation B := (c11_k7_successor_set c S).

Definition c11_k7_graph_valuation (root : D) : valuation :=
  cycle_graph_valuation c root 11
    (fun i => cycle_label c root i \in S)
    (fun i => cycle_label c root i \in Bad).

Local Lemma c11_k7_bad_subset_cycle : Bad \subset [set z in c].
Proof.
apply/subsetP=> q.
rewrite /c11_k7_bad_endpoints /c11_k7_gateway_set
        /c11_k7_cycle_set !inE.
move=> h.
move/andP: h => [h1 h2].
exact: (andP h1).2.
Qed.

Local Lemma c11_k7_graph_rotation_clause root endpoint path :
  root \in c ->
  (endpoint < 11)%coq_nat ->
  path \in two_chord_paths 11 endpoint ->
  satisfies_clause (c11_k7_graph_valuation root)
    (c11_k7_bad_rotation_clause endpoint path).
Proof.
move=> rootc endlt pathin.
apply: c11_k7_bad_rotation_clause_complete.
move=> Hmark Hpred Hall.
have endltB : endpoint < 11 by exact/ltP.
have hpB : numeric_hamilton_pathb 11 endpoint path.
  exact: (allP (two_chord_paths11_numeric endltB) path pathin).
have hpnum : numeric_hamilton_path 11 endpoint path :=
  elimT (@numeric_hamilton_pathP 11 endpoint path) hpB.
clear hpB.
case: path hpnum pathin Hpred Hall => [|start ntail].
- by move=> [sizep _ _ _].
- move=> [sizep uniqp allp lastp] pathin Hpred Hall.
  have startltB : start < 11 by case/andP: allp.
  have startlt : (start < 11)%coq_nat by exact/ltP.
  have predlt : (cycle_predecessor 11 start < 11)%coq_nat.
    rewrite /cycle_predecessor.
    apply PeanoNat.Nat.mod_upper_bound.
    by [].
  have endpointBad : cycle_label c root endpoint \in Bad.
    move: Hmark.
    by rewrite /c11_k7_graph_valuation cycle_graph_valuation_mark.
  have predS :
      cycle_label c root (cycle_predecessor 11 start) \in S.
    move: Hpred.
    by rewrite /c11_k7_graph_valuation cycle_graph_valuation_set.
  have chords : path_chords_realized c root 11 (start :: ntail).
    apply: concrete_valuation_path_chords_realized; first by [].
    exact: Hall.
  have [x [tail [labE hpath hset hlast]]] :=
    two_chord_path11_hamilton Hcycle Hcsize rootc endltB pathin chords.
  have firstE : cycle_label c root start = x.
    move: (congr1 (List.hd root) labE).
    by rewrite /labelled_numeric_path /=.
  have sizetail : size tail = 10.
    move: (congr1 size labE).
    rewrite /labelled_numeric_path size_map sizep /=.
    by move=> [=].
  have uc : uniq c by case/and3P: Hcycle.
  have startB : cycle_label c root start \in B.
    rewrite /B /c11_k7_successor_set.
    apply/imsetP.
    exists (cycle_label c root (cycle_predecessor 11 start)).
    * exact predS.
    * have elevenpos : 0 < 11 by [].
      rewrite (cycle_label_predecessor uc rootc Hcsize elevenpos startltB).
      by rewrite next_prev.
  have xB : x \in B by rewrite -firstE.
  have horder : c11_k7_hamilton_order c x tail
      (cycle_label c root endpoint).
    split.
    * exact hpath.
    * exact hlast.
    * exact sizetail.
    * move=> z.
      by rewrite -[z \in x :: tail]in_set -[z \in c]in_set hset.
  apply: (@c11_k7_bad_no_hamilton D c S Hell
            v0 v1 v2 Hv0R Hv1R Hv2R
            (prefix3_v0_v1_distinct Hprefix)
            (prefix3_v0_v2_distinct Hprefix)
            (prefix3_v1_v2_distinct Hprefix)
            (prefix3_arc01 Hprefix) (prefix3_arc12 Hprefix)
            (prefix3_next Hprefix)
            (cycle_label c root endpoint) endpointBad).
  exists x, tail.
  by split.
Qed.

Local Lemma c11_k7_graph_endpoint_clauses root endpoint :
  root \in c ->
  (endpoint < 11)%coq_nat ->
  satisfies_cnf (c11_k7_graph_valuation root)
    (c11_k7_bad_endpoint_clauses endpoint).
Proof.
move=> rootc endlt.
rewrite /c11_k7_bad_endpoint_clauses !satisfies_cnf_app.
split.
- have Hlen : (6 <= List.length (internal_row 11 endpoint))%coq_nat.
    rewrite (c11_k7_internal_row_length endlt).
    lia.
  have Hcase :
      c11_k7_graph_valuation root (set_var 11 endpoint) = false \/
      ckpath_cardinality.count_true (c11_k7_graph_valuation root)
        (internal_row 11 endpoint) = 6.
    case setE: (c11_k7_graph_valuation root (set_var 11 endpoint)).
    + right.
      have endpointS : cycle_label c root endpoint \in S.
        move: setE.
        by rewrite /c11_k7_graph_valuation cycle_graph_valuation_set.
      rewrite /c11_k7_graph_valuation.
      apply: (@cycle_graph_valuation_internal_row_count_closed
          D c root 11 endpoint
          (fun i => cycle_label c root i \in S)
          (fun i => cycle_label c root i \in Bad) 7).
      * lia.
      * exact Hcycle.
      * exact Hcsize.
      * exact rootc.
      * exact endlt.
      * exact: Hreg _.
      * move=> z az.
        exact: HSclosed endpointS az.
    + by left.
  have Hexact :=
    negative_guard_exactly_complete
      (c11_k7_graph_valuation root) (set_var 11 endpoint) 6
      (internal_row 11 endpoint) Hlen Hcase.
  move: Hexact.
  by rewrite /exactly_comb satisfies_cnf_app.
- split.
  * have mark_not_set :
        c11_k7_graph_valuation root (mark_var 11 endpoint) = true ->
        c11_k7_graph_valuation root (set_var 11 endpoint) = false.
      move=> markE.
      have endpointBad : cycle_label c root endpoint \in Bad.
        move: markE.
        by rewrite /c11_k7_graph_valuation cycle_graph_valuation_mark.
      have endpointNS : cycle_label c root endpoint \notin S.
        move: endpointBad.
        rewrite /c11_k7_bad_endpoints /c11_k7_gateway_set
                /c11_k7_cycle_set !inE.
        move=> h.
        exact: (andP (andP h).1).1.
      rewrite /c11_k7_graph_valuation cycle_graph_valuation_set //.
      exact: negbTE endpointNS.
    unfold satisfies_cnf, eval_cnf, satisfies_clause, eval_clause.
    simpl.
    rewrite !eval_negative_literal.
    case markE: (c11_k7_graph_valuation root (mark_var 11 endpoint));
      simpl; last by [].
    by rewrite (mark_not_set markE).
  * apply: satisfies_cnf_map=> path pathin.
    have ListIn_mem_seqnat : forall (z : seq nat) s,
        List.In z s -> z \in s.
      move=> z; elim=> [|a s IH] /=.
      - by [].
      - move=> [<-|zin].
        + by rewrite mem_head.
        + by rewrite inE (IH zin) orbT.
    have pinB : path \in two_chord_paths 11 endpoint :=
      ListIn_mem_seqnat _ _ pathin.
    exact: c11_k7_graph_rotation_clause rootc endlt pinB.
Qed.

(** The graph realizes every semantic component of the checked k=7 C11 CNF;
    its independently replayed certificate therefore eliminates the shape. *)
Theorem ckpath_k7_c11_graph_certificate_impossible : False.
Proof.
have bad3 : 3 <= #|Bad|.
  exact: c11_k7_bad_card_ge3 Hreg Hcycle Hcsize HScard HSsub HSclosed.
have zero2 : 0 < 2 by [].
have Badpos : 0 < #|Bad| := ltn_trans zero2 bad3.
have Badn0 : Bad != set0 by rewrite -card_gt0.
move/set0Pn: Badn0 => [root rootBad].
have rootC : root \in [set z in c] :=
  subsetP c11_k7_bad_subset_cycle root rootBad.
have rootc : root \in c by move: rootC; rewrite inE.
set rho := c11_k7_graph_valuation root.
have base : satisfies_cnf rho (cycle_base_clauses 11).
  rewrite /rho /c11_k7_graph_valuation.
  apply: (@cycle_graph_valuation_cycle_base D c root 11 _ _).
  - lia.
  - exact Hcycle.
  - exact Hcsize.
  - exact rootc.
have Ssubc : S \subset [set z in c].
  apply/subsetP=> z zS.
  move: (subsetP HSsub z zS).
  by rewrite /c11_k7_cycle_set inE.
have setcount : ckpath_cardinality.count_true rho
    (List.map (set_var 11) (vertex_list 11)) = 6.
  rewrite /rho /c11_k7_graph_valuation.
  rewrite (@cycle_graph_valuation_set_count D c root 11 S
             (fun i => cycle_label c root i \in Bad)
             Hcycle Hcsize Ssubc).
  exact HScard.
have rootzero : rho (mark_var 11 0) = true.
  rewrite /rho /c11_k7_graph_valuation cycle_graph_valuation_mark.
  by rewrite (rooted_cycle_root rootc) rootBad.
have endpoints : satisfies_cnf rho
    (List.flat_map c11_k7_bad_endpoint_clauses (vertex_list 11)).
  apply: satisfies_cnf_flat_map=> endpoint endpointin.
  have endlt : (endpoint < 11)%coq_nat.
    move: endpointin; rewrite /vertex_list => /List.in_seq.
    lia.
  exact: c11_k7_graph_endpoint_clauses rootc endlt.
have markcount : ckpath_cardinality.count_true rho
    (List.map (mark_var 11) (vertex_list 11)) = #|Bad|.
  rewrite /rho /c11_k7_graph_valuation.
  exact: (@cycle_graph_valuation_mark_count D c root 11 Bad
            (fun i => cycle_label c root i \in S)
            Hcycle Hcsize c11_k7_bad_subset_cycle).
have markcountP :
    (2 <= ckpath_cardinality.count_true rho
      (List.map (mark_var 11) (vertex_list 11)))%coq_nat.
  rewrite markcount.
  apply/leP.
  exact: ltnW bad3.
exact: (@c11_k7_bad_projection_impossible rho
          base setcount rootzero endpoints markcountP).
Qed.

End C11GraphBridge.
