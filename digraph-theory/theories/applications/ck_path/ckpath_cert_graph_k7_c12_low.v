(** * Graph semantics for the k=7 C12, a=2 low-endpoint endgame *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cycle_tools ckpath_kernel_prefix_adapters ckpath_k7_c12_low_hand
  ckpath_k7_c12_low_ge3
  ckpath_cnf ckpath_cardinality ckpath_cert_base ckpath_cert_k7_base
  ckpath_cert_k7_c12_low3_base
  ckpath_cert_clause_tools ckpath_cert_k7_clause_tools
  ckpath_cert_k7_semantics ckpath_cert_k7_c12_low3_semantics
  ckpath_cert_k7_c12_low3_reduction
  ckpath_rotation_paths
  ckpath_rotation_paths_k7 ckpath_cert_graph_common ckpath_k7_orbits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Lemma c12_k7_low_internal_row_length endpoint :
  (endpoint < 12)%coq_nat -> List.length (internal_row 12 endpoint) = 9.
Proof.
intros hlt.
do 12 (destruct endpoint as [|endpoint]; [vm_compute; reflexivity |]).
lia.
Qed.

Section C12LowGraphBridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}) (v0 v1 : D).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hell : ell D = 13.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 12.
Hypothesis HScard : #|S| = 7.
Hypothesis Hprefix : ckpath_prefix2_data c S v0 v1.

Local Notation C := (ckpath_cycle_set c).
Local Notation Low := (c12_k7_low_endpoints c).
Local Notation B := (ckpath_successor_set c S).

Definition c12_k7_low_graph_valuation (root : D) : valuation :=
  cycle_graph_valuation c root 12
    (fun i => cycle_label c root i \in S)
    (fun i => cycle_label c root i \in Low).

Local Lemma c12_k7_low_subset_cycle : Low \subset C.
Proof.
apply/subsetP=> q.
by rewrite /Low /c12_k7_low_endpoints inE => /andP[].
Qed.

Local Lemma c12_k7_low_graph_rotation_clause root endpoint path :
  root \in c ->
  (endpoint < 12)%coq_nat ->
  path \in two_chord_paths 12 endpoint ->
  satisfies_clause (c12_k7_low_graph_valuation root)
    (c12_k7_low_rotation_clause endpoint path).
Proof.
move=> rootc endlt pathin.
apply: c12_k7_low_rotation_clause_complete.
move=> Hset Hmark Hpred Hall.
have endltB : endpoint < 12 by exact/ltP.
have hpB : numeric_hamilton_pathb 12 endpoint path.
  exact: (allP (two_chord_paths12_numeric endltB) path pathin).
have hpnum : numeric_hamilton_path 12 endpoint path :=
  elimT (@numeric_hamilton_pathP 12 endpoint path) hpB.
clear hpB.
case: path hpnum pathin Hpred Hall => [|start ntail].
- by move=> [sizep _ _ _].
- move=> [sizep uniqp allp lastp] pathin Hpred Hall.
  have startltB : start < 12 by case/andP: allp.
  have predlt : (cycle_predecessor 12 start < 12)%coq_nat.
    rewrite /cycle_predecessor.
    apply PeanoNat.Nat.mod_upper_bound.
    by [].
  have endpointLow : cycle_label c root endpoint \in Low.
    move: Hmark.
    by rewrite /c12_k7_low_graph_valuation cycle_graph_valuation_mark.
  have predS :
      cycle_label c root (cycle_predecessor 12 start) \in S.
    move: Hpred.
    by rewrite /c12_k7_low_graph_valuation cycle_graph_valuation_set.
  have chords : path_chords_realized c root 12 (start :: ntail).
    apply: concrete_valuation_path_chords_realized; first by [].
    exact: Hall.
  have [x [tail [labE hpath hset hlast]]] :=
    two_chord_path12_hamilton Hcycle Hcsize rootc endltB pathin chords.
  have firstE : cycle_label c root start = x.
    move: (congr1 (List.hd root) labE).
    by rewrite /labelled_numeric_path /=.
  have sizetail : size tail = 11.
    move: (congr1 size labE).
    rewrite /labelled_numeric_path size_map sizep /=.
    by move=> [=].
  have uc : uniq c by case/and3P: Hcycle.
  have startB : cycle_label c root start \in B.
    rewrite /B /ckpath_successor_set.
    apply/imsetP.
    exists (cycle_label c root (cycle_predecessor 12 start)).
    * exact predS.
    * have twelvepos : 0 < 12 by [].
      rewrite (cycle_label_predecessor uc rootc Hcsize twelvepos startltB).
      by rewrite next_prev.
  have xB : x \in B by rewrite -firstE.
  have horder : c12_k7_hamilton_order c x tail
      (cycle_label c root endpoint).
    split.
    * exact hpath.
    * exact hlast.
    * exact sizetail.
    * move=> z.
      by rewrite -[z \in x :: tail]in_set -[z \in c]in_set hset.
  apply: (@c12_k7_low_no_hamilton D c S v0 v1 Hell Hprefix
            (cycle_label c root endpoint) endpointLow).
  exists x, tail.
  by split.
Qed.

Local Lemma c12_k7_low_graph_endpoint_clauses root endpoint :
  root \in c ->
  (endpoint < 12)%coq_nat ->
  satisfies_cnf (c12_k7_low_graph_valuation root)
    (c12_k7_low_endpoint_clauses endpoint).
Proof.
move=> rootc endlt.
rewrite /c12_k7_low_endpoint_clauses !satisfies_cnf_app.
split.
- have Hlen : (6 <= List.length (internal_row 12 endpoint))%coq_nat.
    rewrite (c12_k7_low_internal_row_length endlt).
    lia.
  have Hcase :
      c12_k7_low_graph_valuation root (set_var 12 endpoint) = false \/
      count_true (c12_k7_low_graph_valuation root)
        (internal_row 12 endpoint) = 6.
    case qS: (cycle_label c root endpoint \in S).
    * right.
      rewrite /c12_k7_low_graph_valuation.
      apply: (@cycle_graph_valuation_internal_row_count_closed
          D c root 12 endpoint
          (fun i => cycle_label c root i \in S)
          (fun i => cycle_label c root i \in Low) 7).
      -- lia.
      -- exact Hcycle.
      -- exact Hcsize.
      -- exact rootc.
      -- exact endlt.
      -- exact: Hreg _.
      -- move=> z az.
         exact: (prefix2_S_closed Hprefix qS az).
    * left.
      rewrite /c12_k7_low_graph_valuation
        (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt) qS.
      by [].
  have Hexact := negative_guard_exactly_complete
    (c12_k7_low_graph_valuation root) (set_var 12 endpoint) 6
    (internal_row 12 endpoint) Hlen Hcase.
  move: Hexact.
  by rewrite /exactly_comb satisfies_cnf_app.
- split.
  * apply: positive_guard_at_most_complete.
    case qS: (cycle_label c root endpoint \in S).
    -- left.
       rewrite /c12_k7_low_graph_valuation
         (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt) qS.
       by [].
    -- right.
       have qC : cycle_label c root endpoint \in C.
         rewrite /C /ckpath_cycle_set inE.
         apply: cycle_label_mem.
         rewrite Hcsize; exact/ltP.
       have outCle : outdeg_in C (cycle_label c root endpoint) <= 7.
         have split := outdeg_split_set C (cycle_label c root endpoint).
         rewrite Hreg in split.
         rewrite split.
         exact: leq_addr.
       have n3 : (3 <= 12)%coq_nat by lia.
       have rowE :=
         (@cycle_graph_valuation_internal_row_count_in
           D c root 12 endpoint
           (fun i => cycle_label c root i \in S)
           (fun i => cycle_label c root i \in Low)
           (outdeg_in C (cycle_label c root endpoint))
           n3 Hcycle Hcsize rootc endlt erefl).
       rewrite /c12_k7_low_graph_valuation rowE.
       lia.
  * split.
    -- have Hlen : (4 <= List.length (internal_row 12 endpoint))%coq_nat.
         rewrite (c12_k7_low_internal_row_length endlt).
         lia.
       apply: (@two_positive_guard_at_least_complete
         (c12_k7_low_graph_valuation root)
         (set_var 12 endpoint) (mark_var 12 endpoint) 4
         (internal_row 12 endpoint) Hlen).
       case qS: (cycle_label c root endpoint \in S).
       ++ left.
          rewrite /c12_k7_low_graph_valuation
            (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt) qS.
          by [].
       ++ case qLow: (cycle_label c root endpoint \in Low).
          ** right; left.
             rewrite /c12_k7_low_graph_valuation
               (@cycle_graph_valuation_mark D c root 12 _ _ endpoint) qLow.
             by [].
          ** right; right.
             have qC : cycle_label c root endpoint \in C.
               rewrite /C /ckpath_cycle_set inE.
               apply: cycle_label_mem.
               rewrite Hcsize; exact/ltP.
             have qgt : 4 < outdeg_in C (cycle_label c root endpoint).
               move: qLow.
               rewrite (@c12_k7_low_endpointP D c Hreg
                         (cycle_label c root endpoint)) qC /=.
               move=> hle.
               by rewrite ltnNge hle.
             have n3 : (3 <= 12)%coq_nat by lia.
             have rowE :=
               (@cycle_graph_valuation_internal_row_count_in
                 D c root 12 endpoint
                 (fun i => cycle_label c root i \in S)
                 (fun i => cycle_label c root i \in Low)
                 (outdeg_in C (cycle_label c root endpoint))
                 n3 Hcycle Hcsize rootc endlt erefl).
             rewrite /c12_k7_low_graph_valuation rowE.
             lia.
    -- apply: satisfies_cnf_map=> path pathin.
       have ListIn_mem_seqnat : forall (z : seq nat) s,
           List.In z s -> z \in s.
         move=> z; elim=> [|a s IH] /=.
         ++ by [].
         ++ move=> [<-|zin].
            ** by rewrite mem_head.
            ** by rewrite inE (IH zin) orbT.
       have pinB : path \in two_chord_paths 12 endpoint :=
         ListIn_mem_seqnat _ _ pathin.
       exact: c12_k7_low_graph_rotation_clause rootc endlt pinB.
Qed.

(** Before choosing either a selected or a low root, the graph valuation
    satisfies the rotation-invariant part of the finite model. *)
Theorem ckpath_k7_c12_low_graph_raw_base_satisfied_at_root root :
  root \in c ->
  satisfies_cnf (c12_k7_low_graph_valuation root) c12_k7_low_raw_base.
Proof.
move=> rootc.
have SsubC : S \subset C := prefix2_S_subset Hprefix.
set rho := c12_k7_low_graph_valuation root.
have base : satisfies_cnf rho (cycle_base_clauses 12).
  rewrite /rho /c12_k7_low_graph_valuation.
  have n2 : (2 <= 12)%coq_nat by lia.
  exact: (@cycle_graph_valuation_cycle_base D c root 12 _ _
            n2 Hcycle Hcsize rootc).
have setcount : count_true rho
    (map (set_var 12) (vertex_list 12)) = 7.
  rewrite /rho /c12_k7_low_graph_valuation.
  rewrite (@cycle_graph_valuation_set_count D c root 12 S
             (fun i => cycle_label c root i \in Low)
             Hcycle Hcsize SsubC).
  exact HScard.
have endpoints : satisfies_cnf rho
    (List.flat_map c12_k7_low_endpoint_clauses (vertex_list 12)).
  apply: satisfies_cnf_flat_map=> endpoint endpointin.
  have endlt : (endpoint < 12)%coq_nat.
    move: endpointin; rewrite /vertex_list => /List.in_seq.
    lia.
  exact: c12_k7_low_graph_endpoint_clauses rootc endlt.
exact: (@c12_k7_low_raw_base_satisfied rho base setcount endpoints).
Qed.

(** Rooting at a low endpoint realizes all four strengthenings in
    [c12_k7_low3_base]: the root mark, disjointness from [S], at least three
    marks, and the guarded internal-row upper bound. *)
Theorem ckpath_k7_c12_low_graph_low3_base_satisfied_at_root root :
  root \in c -> root \in Low ->
  satisfies_cnf (c12_k7_low_graph_valuation root) c12_k7_low3_base.
Proof.
move=> rootc rootLow.
set rho := c12_k7_low_graph_valuation root.
apply: (@c12_k7_low3_base_satisfied rho).
- exact: ckpath_k7_c12_low_graph_raw_base_satisfied_at_root rootc.
- rewrite /rho /c12_k7_low_graph_valuation
          (@cycle_graph_valuation_mark D c root 12 _ _ 0).
  by rewrite (rooted_cycle_root rootc) rootLow.
- move=> i iin imark.
  have ilt : (i < 12)%coq_nat.
    move: iin; rewrite /vertex_list => /List.in_seq; lia.
  have labelLow : cycle_label c root i \in Low.
    move: imark.
    rewrite /rho /c12_k7_low_graph_valuation
            (@cycle_graph_valuation_mark D c root 12 _ _ i).
    by case: (cycle_label c root i \in Low).
  have labelQ := subsetP
    (@c12_k7_low_subset_complement D c S v0 v1 Hreg Hprefix)
    _ labelLow.
  have labelNS : cycle_label c root i \notin S.
    by move: labelQ; rewrite !inE => /andP[].
  rewrite /rho /c12_k7_low_graph_valuation
          (@cycle_graph_valuation_set D c root 12 _ _ i ilt).
  exact: negbTE labelNS.
- have LowSubc : Low \subset [set z in c].
    move: c12_k7_low_subset_cycle.
    by rewrite /C /ckpath_cycle_set.
  rewrite /rho /c12_k7_low_graph_valuation
    (@cycle_graph_valuation_mark_count D c root 12 Low
       (fun i => cycle_label c root i \in S)
       Hcycle Hcsize LowSubc).
  apply/leP.
  exact: (@c12_k7_low_card_ge3 D c S v0 v1 Hreg Hell Hprefix
            Hcycle Hcsize HScard).
- move=> i iin.
  have ilt : (i < 12)%coq_nat.
    move: iin; rewrite /vertex_list => /List.in_seq; lia.
  case labelLow: (cycle_label c root i \in Low).
  * right.
    have /andP[_ labelDegree] :
        (cycle_label c root i \in C) &&
        (outdeg_in C (cycle_label c root i) <= 4).
      by move: labelLow; rewrite c12_k7_low_endpointP.
    have n3 : (3 <= 12)%coq_nat by lia.
    have rowE :=
      (@cycle_graph_valuation_internal_row_count_in
        D c root 12 i
        (fun j => cycle_label c root j \in S)
        (fun j => cycle_label c root j \in Low)
        (outdeg_in C (cycle_label c root i))
        n3 Hcycle Hcsize rootc ilt erefl).
    rewrite /rho /c12_k7_low_graph_valuation rowE.
    lia.
  * left.
    rewrite /rho /c12_k7_low_graph_valuation
            (@cycle_graph_valuation_mark D c root 12 _ _ i) labelLow.
    by [].
Qed.

(** Fixing any selected subset of the graph-theoretic low endpoints agrees
    with the two-pass partial assignment used by the certificate reducer. *)
Theorem ckpath_k7_c12_low_graph_subset_assignment_extends
    root (T : {set D}) :
  T \subset Low ->
  extends (c12_k7_low_graph_valuation root)
    (c12_k7_low_subset_assignment (cycle_set_mask c root 12 T)).
Proof.
move=> TsubLow.
rewrite /cycle_set_mask.
apply: c12_k7_low_subset_assignment_bits_extends.
- move=> i ilt selected.
  have labelT : cycle_label c root i \in T.
    by move: selected; case: (cycle_label c root i \in T).
  have labelLow := subsetP TsubLow _ labelT.
  have labelQ := subsetP
    (@c12_k7_low_subset_complement D c S v0 v1 Hreg Hprefix)
    _ labelLow.
  have labelNS : cycle_label c root i \notin S.
    by move: labelQ; rewrite !inE => /andP[].
  rewrite /c12_k7_low_graph_valuation
    (@cycle_graph_valuation_set D c root 12 _ _ i ilt).
  exact: negbTE labelNS.
- move=> i _ selected.
  have labelT : cycle_label c root i \in T.
    by move: selected; case: (cycle_label c root i \in T).
  have labelLow := subsetP TsubLow _ labelT.
  rewrite /c12_k7_low_graph_valuation
    (@cycle_graph_valuation_mark D c root 12 _ _ i).
  by rewrite labelLow.
Qed.

(** The complete finite base is satisfied at every root belonging to [S].
    Keeping the root explicit lets the orbit-normalization theorem choose it. *)
Theorem ckpath_k7_c12_low_graph_base_satisfied_at_root root :
  root \in c -> root \in S ->
  satisfies_cnf (c12_k7_low_graph_valuation root) c12_k7_low_base.
Proof.
move=> rootc rootS.
have SsubC : S \subset C := prefix2_S_subset Hprefix.
set rho := c12_k7_low_graph_valuation root.
have base : satisfies_cnf rho (cycle_base_clauses 12).
  rewrite /rho /c12_k7_low_graph_valuation.
  have n2 : (2 <= 12)%coq_nat by lia.
  exact: (@cycle_graph_valuation_cycle_base D c root 12 _ _
            n2 Hcycle Hcsize rootc).
have setcount : count_true rho
    (map (set_var 12) (vertex_list 12)) = 7.
  rewrite /rho /c12_k7_low_graph_valuation.
  rewrite (@cycle_graph_valuation_set_count D c root 12 S
             (fun i => cycle_label c root i \in Low)
             Hcycle Hcsize SsubC).
  exact HScard.
have rootzero : rho (set_var 12 0) = true.
  rewrite /rho /c12_k7_low_graph_valuation.
  have zeroLt : (0 < 12)%coq_nat by lia.
  rewrite (@cycle_graph_valuation_set D c root 12 _ _ 0 zeroLt).
  by rewrite (rooted_cycle_root rootc) rootS.
have endpoints : satisfies_cnf rho
    (List.flat_map c12_k7_low_endpoint_clauses (vertex_list 12)).
  apply: satisfies_cnf_flat_map=> endpoint endpointin.
  have endlt : (endpoint < 12)%coq_nat.
    move: endpointin; rewrite /vertex_list => /List.in_seq.
    lia.
  exact: c12_k7_low_graph_endpoint_clauses rootc endlt.
exact: (@c12_k7_low_base_satisfied rho base setcount rootzero endpoints).
Qed.

(** Every graph in the C12, a=2 low-endpoint branch realizes the complete
    finite CNF used by the independently checked refutation.  This interface
    is retained for the certificate-parameterized k=7 assembly. *)
Theorem ckpath_k7_c12_low_graph_base_satisfied :
  exists rho, satisfies_cnf rho c12_k7_low_base.
Proof.
have Spos : 0 < #|S| by rewrite HScard.
have Sn0 : S != set0 by rewrite -card_gt0.
move/set0Pn: Sn0 => [root rootS].
have SsubC : S \subset C := prefix2_S_subset Hprefix.
have rootC : root \in C := subsetP SsubC root rootS.
have rootc : root \in c by move: rootC; rewrite /C /ckpath_cycle_set inE.
exists (c12_k7_low_graph_valuation root).
exact: ckpath_k7_c12_low_graph_base_satisfied_at_root rootc rootS.
Qed.

(** Orbit-normalized realization used by the fixed-set certificate family. *)
Theorem ckpath_k7_c12_low_graph_fixed_instance_satisfied :
  exists mask rho,
    List.In mask (orbit_representatives 12 7) /\
    satisfies_cnf rho
      (fixed_set_instance c12_k7_low_base 12 mask).
Proof.
have uc : uniq c by case/and3P: Hcycle.
have Ssubc : S \subset [set z in c].
  move: (prefix2_S_subset Hprefix).
  by rewrite /ckpath_cycle_set.
have sevenpos : (0 < 7)%coq_nat by lia.
have [root [rootc [rootS [Hrep Hmask]]]] :=
  @choose_cycle_set_orbit_root D c S 12 7 uc Hcsize Ssubc HScard
    sevenpos k7_orbit_representatives_12_7_rooted.
have Hbase : satisfies_cnf
    (c12_k7_low_graph_valuation root) c12_k7_low_base.
  exact: ckpath_k7_c12_low_graph_base_satisfied_at_root rootc rootS.
have Hfixed : satisfies_cnf
    (c12_k7_low_graph_valuation root)
    (fixed_set_instance c12_k7_low_base 12
      (cycle_set_mask c root 12 S)).
  exact: (@cycle_graph_valuation_fixed_set_instance
    D c root 12 S
    (fun i => cycle_label c root i \in Low)
    c12_k7_low_base Hbase).
exists (cycle_set_mask c root 12 S),
  (c12_k7_low_graph_valuation root).
split; [exact Hrep | exact Hfixed].
Qed.

(** Select three graph-theoretic low endpoints, then rotate the cycle so the
    membership word of that triple is one of the nineteen checked orbit
    representatives.  The graph valuation satisfies the corresponding
    reduced certificate instance. *)
Theorem ckpath_k7_c12_low_graph_low3_instance_satisfied :
  exists mask rho,
    List.In mask (orbit_representatives 12 3) /\
    satisfies_cnf rho (c12_k7_low3_instance mask).
Proof.
have LowCard : 3 <= #|Low| :=
  @c12_k7_low_card_ge3 D c S v0 v1 Hreg Hell Hprefix
    Hcycle Hcsize HScard.
pose T : {set D} := [set x in take 3 (enum Low)].
have TsubLow : T \subset Low.
  apply/subsetP=> x.
  move=> xT.
  have xTake : x \in take 3 (enum Low).
    by move: xT; rewrite /T inE.
  move: (mem_take xTake).
  by rewrite mem_enum.
have Tcard : #|T| = 3.
  rewrite /T cardsE /=.
  rewrite (card_uniqP _) ?size_take.
  - apply/minn_idPl.
    by rewrite -cardE.
  - by rewrite take_uniq // enum_uniq.
have LowSubc : Low \subset [set z in c].
  move: c12_k7_low_subset_cycle.
  by rewrite /C /ckpath_cycle_set.
have Tsubc : T \subset [set z in c] := subset_trans TsubLow LowSubc.
have uc : uniq c by case/and3P: Hcycle.
have threepos : (0 < 3)%coq_nat by lia.
have [root [rootc [rootT [maskRep _]]]] :=
  @choose_cycle_set_orbit_root D c T 12 3 uc Hcsize Tsubc Tcard
    threepos k7_orbit_representatives_12_3_rooted.
have rootLow := subsetP TsubLow root rootT.
set mask := cycle_set_mask c root 12 T.
set rho := c12_k7_low_graph_valuation root.
have base : satisfies_cnf rho c12_k7_low3_base.
  exact: ckpath_k7_c12_low_graph_low3_base_satisfied_at_root rootc rootLow.
have assignment_ok : extends rho (c12_k7_low_subset_assignment mask).
  rewrite /rho /mask.
  exact: ckpath_k7_c12_low_graph_subset_assignment_extends TsubLow.
exists mask, rho; split.
- exact maskRep.
- exact: (@c12_k7_low3_instance_satisfied rho mask assignment_ok base).
Qed.

Corollary ckpath_k7_c12_low_graph_nineteen_instance_family_satisfied :
  List.length (orbit_representatives 12 3) = 19 /\
  exists mask rho,
    List.In mask (orbit_representatives 12 3) /\
    satisfies_cnf rho (c12_k7_low3_instance mask).
Proof.
split.
- exact: k7_orbit_representatives_12_3_count.
- exact: ckpath_k7_c12_low_graph_low3_instance_satisfied.
Qed.

End C12LowGraphBridge.
