(** * Graph-to-certificate bridge for the k=7 C12, a=1 endgame *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath strong
  ckpath_cycle_tools ckpath_even_gateway ckpath_k7_even_gateway
  ckpath_cnf ckpath_cardinality ckpath_cert_base ckpath_cert_k7_base
  ckpath_cert_k7_semantics
  ckpath_cert_clause_tools ckpath_cert_k7_clause_tools
  ckpath_rotation_paths ckpath_rotation_paths_k7 ckpath_cert_graph_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Lemma c12_k7_internal_row_length endpoint :
  (endpoint < 12)%coq_nat -> List.length (internal_row 12 endpoint) = 9.
Proof.
intros hlt.
do 12 (destruct endpoint as [|endpoint]; [vm_compute; reflexivity |]).
lia.
Qed.

Section C12GraphBridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Hypothesis Hreg : forall v : D, outdeg v = 7.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D = 12.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 12.
Hypothesis HScard : #|S| = 7.
Hypothesis HSsub : S \subset even_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in even_cycle_set c.
Hypothesis Horder : 15 <= #|D|.

Local Notation C := (even_cycle_set c).
Local Notation R := (even_outside c).
Local Notation A := (even_active_set c).

Definition c12_k7_graph_valuation (root y : D) : valuation :=
  cycle_graph_valuation c root 12
    (fun i => cycle_label c root i \in A)
    (fun i => ~~ (y --> cycle_label c root i)).

Local Lemma c12_k7_active_subset_cycle : A \subset C.
Proof.
apply: (subset_trans
  (@c12_active_subset_gateway D c S HSclosed)).
apply/subsetP=> q.
by rewrite /even_gateway_set inE => /andP[_].
Qed.

Local Lemma c12_k7_graph_endpoint_clauses root y endpoint :
  root \in c -> y \in R ->
  (endpoint < 12)%coq_nat ->
  satisfies_cnf (c12_k7_graph_valuation root y)
    (c12_k7_cover_endpoint_clauses endpoint).
Proof.
move=> rootc yR endlt.
have endltB : endpoint < 12 by exact/ltP.
rewrite /c12_k7_cover_endpoint_clauses !satisfies_cnf_app.
split.
- unfold satisfies_cnf, eval_cnf, satisfies_clause, eval_clause.
  simpl.
  rewrite eval_negative_literal eval_positive_literal.
  rewrite /c12_k7_graph_valuation
    (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt)
    (@cycle_graph_valuation_mark D c root 12 _ _
       (cycle_successor 12 endpoint)).
  case qA: (cycle_label c root endpoint \in A); simpl; last by [].
  have uc : uniq c by case/and3P: Hcycle.
  have succE : cycle_label c root (cycle_successor 12 endpoint) =
      next c (cycle_label c root endpoint).
    exact: (cycle_label_successor uc rootc Hcsize isT endltB).
  have omit : y --> next c (cycle_label c root endpoint) = false.
    exact: (@c12_active_successor_omitted D c S Hstr Hell Hcycle Hcsize
              HScard HSsub Horder _ _ qA yR).
  by rewrite succE omit.
- split.
  * have Hlen : (6 <= List.length (internal_row 12 endpoint))%coq_nat.
      rewrite (c12_k7_internal_row_length endlt).
      lia.
    have Hcase :
        c12_k7_graph_valuation root y (set_var 12 endpoint) = true \/
        count_true (c12_k7_graph_valuation root y)
          (internal_row 12 endpoint) = 6.
      case qA: (cycle_label c root endpoint \in A).
      - left.
        rewrite /c12_k7_graph_valuation
          (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt) qA.
        by [].
      - right.
        have qC : cycle_label c root endpoint \in C.
          rewrite /even_cycle_set inE.
          apply: cycle_label_mem.
          by rewrite Hcsize.
        have outR0 : outdeg_in R (cycle_label c root endpoint) = 0.
          apply/eqP; rewrite -leqn0.
          move: qA; rewrite /even_active_set inE qC /=.
          move=> hzero; apply/leP.
          have hnot : ~ (0 < outdeg_in R
              (cycle_label c root endpoint))%coq_nat.
            move=> hposP.
            have hpos : 0 < outdeg_in R
                (cycle_label c root endpoint) by exact/ltP.
            by rewrite hpos in hzero.
          lia.
        have split := outdeg_split_set C
          (cycle_label c root endpoint).
        rewrite (Hreg (cycle_label c root endpoint)) outR0 addn0 in split.
        rewrite /c12_k7_graph_valuation.
        apply: (@cycle_graph_valuation_internal_row_count_in
                  D c root 12 endpoint _ _ 7).
        + lia.
        + exact Hcycle.
        + exact Hcsize.
        + exact rootc.
        + exact endlt.
        + by rewrite /even_cycle_set -split.
    have Hexact := positive_guard_exactly_complete
      (c12_k7_graph_valuation root y) (set_var 12 endpoint) 6
      (internal_row 12 endpoint) Hlen Hcase.
    move: Hexact.
    by rewrite /exactly_comb satisfies_cnf_app.
  * split.
    + apply: negative_guard_at_most_complete.
      case qA: (cycle_label c root endpoint \in A).
      -- right.
         have qC : cycle_label c root endpoint \in C.
           exact: subsetP c12_k7_active_subset_cycle _ qA.
         have qpos : 0 < outdeg_in R (cycle_label c root endpoint).
           by move: qA; rewrite /even_active_set inE qC.
         have split := outdeg_split_set C
           (cycle_label c root endpoint).
         rewrite (Hreg (cycle_label c root endpoint)) in split.
         have outCle : (outdeg_in C
             (cycle_label c root endpoint) <= 6)%coq_nat.
           move/ltP: qpos => qposP.
           rewrite /even_outside in qposP.
           apply/leP; lia.
         have n12ge3 : (3 <= 12)%coq_nat by lia.
         have rowE :=
           (@cycle_graph_valuation_internal_row_count_in
             D c root 12 endpoint
             (fun i => cycle_label c root i \in A)
             (fun i => ~~ (y --> cycle_label c root i))
             (outdeg_in C (cycle_label c root endpoint))
             n12ge3 Hcycle Hcsize rootc endlt erefl).
         rewrite /c12_k7_graph_valuation rowE.
         lia.
      -- left.
         rewrite /c12_k7_graph_valuation
           (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt) qA.
         by [].
    + apply: satisfies_cnf_map=> path pin.
      apply: cover_rotation_clause_complete=> settrue chordtrue.
      have qA : cycle_label c root endpoint \in A.
        move: settrue.
        rewrite /c12_k7_graph_valuation
          (@cycle_graph_valuation_set D c root 12 _ _ endpoint endlt).
        by [].
      have realized : path_chords_realized c root 12 path.
        apply: (@concrete_valuation_path_chords_realized D 12 c root path
                  (fun i => cycle_label c root i \in A)
                  (fun i => ~~ (y --> cycle_label c root i))).
        -- by [].
        -- move=> z zin.
           move: (chordtrue z zin).
           by rewrite /c12_k7_graph_valuation /cycle_graph_valuation.
      have ListIn_mem_seqnat : forall (z : seq nat) s,
          List.In z s -> z \in s.
        move=> z; elim=> [|a s IH] /=.
        -- by [].
        -- move=> [<-|zin].
           ++ by rewrite mem_head.
           ++ by rewrite inE (IH zin) orbT.
      have pinB : path \in two_chord_paths 12 endpoint :=
        ListIn_mem_seqnat _ _ pin.
      have hpB : numeric_hamilton_pathb 12 endpoint path.
        exact: (allP (two_chord_paths12_numeric endltB) path pinB).
      have hp : numeric_hamilton_path 12 endpoint path :=
        elimT (@numeric_hamilton_pathP 12 endpoint path) hpB.
      have pathsz : size path = 12 by case: hp.
      have [x [tail [labE hpath hset hlast]]] :=
        two_chord_path12_hamilton Hcycle Hcsize rootc endltB pinB realized.
      have pathszc : size path = size c by rewrite pathsz Hcsize.
      have omitx : y --> x = false.
        exact: (@c12_hamilton_start_omitted D c S Hstr Hell Hcycle Hcsize
                  HScard HSsub Horder root y endpoint path x tail
                  rootc yR qA pathszc labE hpath hset hlast).
      rewrite /c12_k7_graph_valuation
        (@cycle_graph_valuation_mark D c root 12 _ _ (List.hd 0 path)).
      case pathE : path pathsz labE => [|h t].
      -- move=> pathsz _; discriminate pathsz.
      -- move=> _ labE'.
         have hx : cycle_label c root h = x.
           move: (congr1 (fun s : seq D => head root s) labE').
           rewrite /labelled_numeric_path /=.
           by [].
         by rewrite /= hx omitx.
Qed.

Theorem ckpath_c12_cover4_graph_base_satisfied :
  #|A| = 4 ->
  exists rho, satisfies_cnf rho (c12_k7_cover_base 4).
Proof.
move=> cardA.
have An0 : A != set0 by rewrite -card_gt0 cardA.
move/set0Pn: An0 => [root rootA].
have rootC : root \in C := subsetP c12_k7_active_subset_cycle root rootA.
have rootc : root \in c by move: rootC; rewrite /even_cycle_set inE.
have R3 : 3 <= #|R|.
  exact: (@c12_outside_card_ge3 D c Hcycle Hcsize Horder).
have Rn0 : R != set0 by rewrite -card_gt0; lia.
move/set0Pn: Rn0 => [y yR].
set rho := c12_k7_graph_valuation root y.
have base : satisfies_cnf rho (cycle_base_clauses 12).
  rewrite /rho /c12_k7_graph_valuation.
  have n12ge2 : (2 <= 12)%coq_nat by lia.
  exact: (@cycle_graph_valuation_cycle_base D c root 12 _ _
            n12ge2 Hcycle Hcsize rootc).
have setcount : count_true rho
    (map (set_var 12) (vertex_list 12)) = 4.
  rewrite /rho /c12_k7_graph_valuation.
  rewrite (@cycle_graph_valuation_set_count D c root 12 A
             (fun i => ~~ (y --> cycle_label c root i))
             Hcycle Hcsize c12_k7_active_subset_cycle).
  exact cardA.
have markcount : (count_true rho
    (map (mark_var 12) (vertex_list 12)) <= 5)%coq_nat.
  have hmark : count_true rho
      (map (mark_var 12) (vertex_list 12)) =
      12 - outdeg_in C y.
    rewrite /rho /c12_k7_graph_valuation /even_cycle_set.
    exact: (@cycle_graph_valuation_nonarc_mark_count D c root 12 y
              (fun i => cycle_label c root i \in A) Hcycle Hcsize).
  have youtd : outdeg_in C y = 7.
    exact: (@c12_outside_outdeg_cycle D c S Hreg Hstr Hell Hcycle Hcsize
              HScard HSsub y yR).
  rewrite hmark youtd.
  lia.
have rootzero : rho (set_var 12 0) = true.
  rewrite /rho /c12_k7_graph_valuation.
  have zero_lt12 : (0 < 12)%coq_nat by lia.
  rewrite (@cycle_graph_valuation_set D c root 12 _ _ 0 zero_lt12).
  by rewrite (rooted_cycle_root rootc) rootA.
have endpoints : satisfies_cnf rho
    (List.flat_map c12_k7_cover_endpoint_clauses (vertex_list 12)).
  apply: satisfies_cnf_flat_map=> endpoint endpointin.
  have endlt : (endpoint < 12)%coq_nat.
    move: endpointin; rewrite /vertex_list => /List.in_seq.
    lia.
  exact: c12_k7_graph_endpoint_clauses rootc yR endlt.
have four_le12 : (4 <= 12)%coq_nat by lia.
exists rho.
exact: (@c12_k7_cover_base_satisfied rho 4 four_le12
          base setcount markcount rootzero endpoints).
Qed.

Theorem ckpath_c12_graph_base_satisfied :
  exists rho, satisfies_cnf rho (c12_k7_cover_base 4).
Proof.
apply: ckpath_c12_cover4_graph_base_satisfied.
exact: (@c12_active_card4 D c S Hreg Hstr Hell Hcycle Hcsize
          HScard HSsub HSclosed Horder).
Qed.

End C12GraphBridge.
