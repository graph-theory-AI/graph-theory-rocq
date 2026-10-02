(** * Graph-to-certificate bridge for the CK C10, a=2 endgame *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cycle_tools ckpath_c10_hand ckpath_cert_base
  ckpath_cnf
  ckpath_cert_clause_tools ckpath_cert_projection_small
  ckpath_rotation_paths ckpath_cert_graph_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Lemma c10_internal_row_length endpoint :
  (endpoint < 10)%coq_nat -> List.length (internal_row 10 endpoint) = 7.
Proof.
intros Hlt.
do 10 (destruct endpoint as [|endpoint]; [vm_compute; reflexivity |]).
lia.
Qed.

Section C10GraphBridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}) (v0 v1 : D).

Hypothesis Hreg : forall v : D, outdeg v = 6.
Hypothesis Hell : ell D = 11.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 10.
Hypothesis HScard : #|S| = 6.
Hypothesis HSsub : S \subset c10_cycle_set c.
Hypothesis HSclosed :
  forall s z, s \in S -> s --> z -> z \in c10_cycle_set c.
Hypothesis Horder : 13 <= #|D|.
Hypothesis Hv0R : v0 \in c10_outside c.
Hypothesis Hv1R : v1 \in c10_outside c.
Hypothesis Hv0Dv1 : v0 != v1.
Hypothesis Hv0v1 : v0 --> v1.
Hypothesis Hv1next : forall s, s \in S -> v1 --> next c s.

Local Notation Bad := (c10_bad_endpoints c S).
Local Notation B := (c10_successor_set c S).

Definition c10_graph_valuation (root : D) : valuation :=
  cycle_graph_valuation c root 10
    (fun i => cycle_label c root i \in S)
    (fun i => cycle_label c root i \in Bad).

Local Lemma c10_bad_subset_cycle : Bad \subset [set z in c].
Proof.
apply/subsetP=> q.
rewrite /c10_bad_endpoints /c10_gateway_set
        /c10_cycle_set !inE.
move=> h.
move/andP: h => [h1 h2].
exact: (andP h1).2.
Qed.

Local Lemma c10_graph_rotation_clause root endpoint path :
  root \in c ->
  (endpoint < 10)%coq_nat ->
  path \in two_chord_paths 10 endpoint ->
  satisfies_clause (c10_graph_valuation root)
    (c10_rotation_clause endpoint path).
Proof.
move=> rootc endlt pathin.
apply: c10_rotation_clause_complete.
move=> Hmark Hpred Hall.
have endltB : endpoint < 10 by exact/ltP.
have hpB : numeric_hamilton_pathb 10 endpoint path.
  exact: (allP (two_chord_paths10_numeric endltB) path pathin).
have hpnum : numeric_hamilton_path 10 endpoint path :=
  elimT (@numeric_hamilton_pathP 10 endpoint path) hpB.
clear hpB.
case: path hpnum pathin Hpred Hall => [|start ntail].
- by move=> [sizep _ _ _].
- move=> [sizep uniqp allp lastp] pathin Hpred Hall.
  have startltB : start < 10 by case/andP: allp.
  have startlt : (start < 10)%coq_nat by exact/ltP.
  have predlt : (cycle_predecessor 10 start < 10)%coq_nat.
    rewrite /cycle_predecessor.
    apply PeanoNat.Nat.mod_upper_bound.
    by [].
  have endpointBad : cycle_label c root endpoint \in Bad.
    move: Hmark.
    by rewrite /c10_graph_valuation cycle_graph_valuation_mark.
  have predS :
      cycle_label c root (cycle_predecessor 10 start) \in S.
    move: Hpred.
    by rewrite /c10_graph_valuation cycle_graph_valuation_set.
  have chords : path_chords_realized c root 10 (start :: ntail).
    apply: concrete_valuation_path_chords_realized; first by [].
    exact: Hall.
  have [x [tail [labE hpath hset hlast]]] :=
    two_chord_path10_hamilton Hcycle Hcsize rootc endltB pathin chords.
  have firstE : cycle_label c root start = x.
    move: (congr1 (List.hd root) labE).
    by rewrite /labelled_numeric_path /=.
  have sizetail : size tail = 9.
    move: (congr1 size labE).
    rewrite /labelled_numeric_path size_map sizep /=.
    by move=> [=].
  have uc : uniq c by case/and3P: Hcycle.
  have startB : cycle_label c root start \in B.
    rewrite /B /c10_successor_set.
    apply/imsetP.
    exists (cycle_label c root (cycle_predecessor 10 start)).
    * exact predS.
    * have tenpos : 0 < 10 by [].
      rewrite (cycle_label_predecessor uc rootc Hcsize tenpos startltB).
      by rewrite next_prev.
  have xB : x \in B by rewrite -firstE.
  have horder : c10_hamilton_order c x tail
      (cycle_label c root endpoint).
    split.
    * exact hpath.
    * exact hlast.
    * exact sizetail.
    * move=> z.
      by rewrite -[z \in x :: tail]in_set -[z \in c]in_set hset.
  apply: (@c10_bad_no_hamilton D c S Hell v0 v1
            Hv0R Hv1R Hv0Dv1 Hv0v1 Hv1next
            (cycle_label c root endpoint) endpointBad).
  exists x, tail.
  by split.
Qed.

Local Lemma c10_graph_endpoint_clauses root endpoint :
  root \in c ->
  (endpoint < 10)%coq_nat ->
  satisfies_cnf (c10_graph_valuation root)
    (c10_endpoint_clauses endpoint).
Proof.
move=> rootc endlt.
rewrite /c10_endpoint_clauses !satisfies_cnf_app.
split.
- have Hlen : (5 <= List.length (internal_row 10 endpoint))%coq_nat.
    rewrite (c10_internal_row_length endlt).
    lia.
  have Hcase :
      c10_graph_valuation root (set_var 10 endpoint) = false \/
      ckpath_cardinality.count_true (c10_graph_valuation root)
        (internal_row 10 endpoint) = 5.
    case setE: (c10_graph_valuation root (set_var 10 endpoint)).
    + right.
      have endpointS : cycle_label c root endpoint \in S.
        move: setE.
        by rewrite /c10_graph_valuation cycle_graph_valuation_set.
      rewrite /c10_graph_valuation.
      apply: (@cycle_graph_valuation_internal_row_count_closed
          D c root 10 endpoint
          (fun i => cycle_label c root i \in S)
          (fun i => cycle_label c root i \in Bad) 6).
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
      (c10_graph_valuation root) (set_var 10 endpoint) 5
      (internal_row 10 endpoint) Hlen Hcase.
  move: Hexact.
  by rewrite /exactly_comb satisfies_cnf_app.
- split.
  * have mark_not_set :
        c10_graph_valuation root (mark_var 10 endpoint) = true ->
        c10_graph_valuation root (set_var 10 endpoint) = false.
      move=> markE.
      have endpointBad : cycle_label c root endpoint \in Bad.
        move: markE.
        by rewrite /c10_graph_valuation cycle_graph_valuation_mark.
      have endpointNS : cycle_label c root endpoint \notin S.
        move: endpointBad.
        rewrite /c10_bad_endpoints /c10_gateway_set
                /c10_cycle_set !inE.
        move=> h.
        exact: (andP (andP h).1).1.
      rewrite /c10_graph_valuation cycle_graph_valuation_set //.
      exact: negbTE endpointNS.
    unfold satisfies_cnf, eval_cnf, satisfies_clause, eval_clause.
    simpl.
    rewrite !eval_negative_literal.
    case markE: (c10_graph_valuation root (mark_var 10 endpoint));
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
    have pinB : path \in two_chord_paths 10 endpoint :=
      ListIn_mem_seqnat _ _ pathin.
    exact: c10_graph_rotation_clause rootc endlt pinB.
Qed.

(** The graph realizes every semantic component of the checked C10 CNF;
    its independently replayed certificate therefore eliminates the shape. *)
Theorem ckpath_c10_graph_certificate_impossible : False.
Proof.
have bad3 : 3 <= #|Bad|.
  exact: c10_bad_card_ge3 Hreg Hcycle Hcsize HScard HSsub HSclosed.
have zero2 : 0 < 2 by [].
have Badpos : 0 < #|Bad| := ltn_trans zero2 bad3.
have Badn0 : Bad != set0 by rewrite -card_gt0.
move/set0Pn: Badn0 => [root rootBad].
have rootC : root \in [set z in c] :=
  subsetP c10_bad_subset_cycle root rootBad.
have rootc : root \in c by move: rootC; rewrite inE.
set rho := c10_graph_valuation root.
have base : satisfies_cnf rho (cycle_base_clauses 10).
  rewrite /rho /c10_graph_valuation.
  apply: (@cycle_graph_valuation_cycle_base D c root 10 _ _).
  - lia.
  - exact Hcycle.
  - exact Hcsize.
  - exact rootc.
have Ssubc : S \subset [set z in c].
  apply/subsetP=> z zS.
  move: (subsetP HSsub z zS).
  by rewrite /c10_cycle_set inE.
have setcount : ckpath_cardinality.count_true rho
    (List.map (set_var 10) (vertex_list 10)) = 6.
  rewrite /rho /c10_graph_valuation.
  rewrite (@cycle_graph_valuation_set_count D c root 10 S
             (fun i => cycle_label c root i \in Bad)
             Hcycle Hcsize Ssubc).
  exact HScard.
have rootzero : rho (mark_var 10 0) = true.
  rewrite /rho /c10_graph_valuation cycle_graph_valuation_mark.
  by rewrite (rooted_cycle_root rootc) rootBad.
have endpoints : satisfies_cnf rho
    (List.flat_map c10_endpoint_clauses (vertex_list 10)).
  apply: satisfies_cnf_flat_map=> endpoint endpointin.
  have endlt : (endpoint < 10)%coq_nat.
    move: endpointin; rewrite /vertex_list => /List.in_seq.
    lia.
  exact: c10_graph_endpoint_clauses rootc endlt.
have markcount : ckpath_cardinality.count_true rho
    (List.map (mark_var 10) (vertex_list 10)) = #|Bad|.
  rewrite /rho /c10_graph_valuation.
  exact: (@cycle_graph_valuation_mark_count D c root 10 Bad
            (fun i => cycle_label c root i \in S)
            Hcycle Hcsize c10_bad_subset_cycle).
have markcountP :
    (2 <= ckpath_cardinality.count_true rho
      (List.map (mark_var 10) (vertex_list 10)))%coq_nat.
  rewrite markcount.
  apply/leP.
  exact: ltnW bad3.
exact: (@c10_projection_impossible rho
          base setcount rootzero endpoints markcountP).
Qed.

End C10GraphBridge.
