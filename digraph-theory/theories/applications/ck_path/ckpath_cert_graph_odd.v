(** * Odd-cycle graph-to-certificate bridges for C9 and C11. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath strong
  ckpath_cycle_tools ckpath_odd_gateway ckpath_cnf ckpath_cardinality
  ckpath_cert_base
  ckpath_cert_clause_tools ckpath_cert_projection
  ckpath_rotation_paths ckpath_cert_graph_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OddHamiltonOmission.
Variable D : orientedDigraph.
Variables (d : nat) (c : seq D) (S : {set D}).

Hypothesis Hd2 : 2 <= d.
Hypothesis Hreg : forall v : D, outdeg v = d.
Hypothesis Hstr : strongb D.
Hypothesis Hell : ell D < 2 * d.
Hypothesis Hcycle : dicycle c.
Hypothesis Hcsize : size c = 2 * d - 1.
Hypothesis HScard : #|S| = d.
Hypothesis HSsub : S \subset odd_cycle_set c.
Hypothesis HSclosed :
  forall u v, u \in S -> u --> v -> v \in odd_cycle_set c.
Hypothesis Horder : 2 * d + 1 <= #|D|.

Local Notation C := (odd_cycle_set c).
Local Notation R := (odd_outside c).
Local Notation A := (odd_active_set c).

Lemma odd_certificate_hamilton_start_omitted root y endpoint path x tail :
  root \in c -> y \in R -> cycle_label c root endpoint \in A ->
  size path = size c ->
  labelled_numeric_path c root path = x :: tail ->
  dipath x tail -> [set z in x :: tail] = C ->
  last x tail = cycle_label c root endpoint ->
  y --> x = false.
Proof.
move=> rootc yR qA pathsz labE hpath hset hlast.
move: (odd_active_witness qA) => [u uR qu].
have uout : u \notin x :: tail.
  apply/negP => uin.
  have uC : u \in C by rewrite -hset in_set uin.
  move: uR; rewrite /odd_outside inE uC /=.
  by [].
have yout : y \notin x :: tail.
  apply/negP => yin.
  have yC : y \in C by rewrite -hset in_set yin.
  move: yR; rewrite /odd_outside inE yC /=.
  by [].
have tailsz : (size tail).+1 = size c.
  move: (congr1 size labE).
  rewrite /labelled_numeric_path size_map /= pathsz.
  by [].
have elltail : ell D < (size tail).+2 by lia.
case: (eqVneq y u) => [->|yu].
- move: (odd_outside_second Hd2 Hstr Hell Hcycle Hcsize HScard HSsub
           Horder uR) => [v vR vu].
  move: (odd_outside_points_cycle Hd2 Hstr Hell Hcycle Hcsize HScard
           HSsub vR) => [z zC vz].
  have vout : v \notin x :: tail.
    apply/negP => vin.
    have vC : v \in C by rewrite -hset in_set vin.
    move: vR; rewrite /odd_outside inE vC /=.
    by [].
  have zinset : z \in [set z in x :: tail] by rewrite hset.
  have zin : z \in x :: tail by move: zinset; rewrite in_set.
  have uv : u != v by rewrite eq_sym.
  exact: (hamilton_active_start_omitted hpath hlast uout vout uv qu zin vz
            elltail).
- have uy : u != y by rewrite eq_sym.
  exact: (hamilton_start_omitted hpath hlast uout yout uy qu elltail).
Qed.

End OddHamiltonOmission.

Section C9Bridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Theorem ckpath_c9_graph_certificate_impossible :
  (forall v : D, outdeg v = 5) ->
  strongb D -> ell D < 10 -> dicycle c -> size c = 9 ->
  #|S| = 5 -> S \subset odd_cycle_set c ->
  (forall u v, u \in S -> u --> v -> v \in odd_cycle_set c) ->
  11 <= #|D| -> False.
Proof.
move=> reg str ell dc sizec Scard Ssub Sclosed order.
have cardA : #|odd_active_set c| = 3.
  exact: (@odd_gateway_d5_active3 D 5 c S isT reg str ell dc sizec
            Scard Ssub Sclosed order erefl).
have An0 : odd_active_set c != set0.
  rewrite -card_gt0 cardA.
  by [].
move/set0Pn: An0 => [root rootA].
have AsubC : odd_active_set c \subset odd_cycle_set c.
  apply: (subset_trans (odd_active_subset_gateway Sclosed)).
  apply/subsetP=> q.
  by rewrite /odd_gateway_set inE => /andP[_].
have rootC : root \in odd_cycle_set c := subsetP AsubC root rootA.
have rootc : root \in c by move: rootC; rewrite /odd_cycle_set inE.
have cardR : 1 < #|odd_outside c|.
  exact: (@odd_outside_card_ge2 D 5 c S isT str ell dc sizec Scard
            Ssub order).
have Rn0 : odd_outside c != set0 by rewrite -card_gt0; lia.
move/set0Pn: Rn0 => [y yR].
set rho := @cycle_graph_valuation D c root 9
  (fun i => cycle_label c root i \in odd_active_set c)
  (fun i => ~~ (y --> cycle_label c root i)).
have base : satisfies_cnf rho (cycle_base_clauses 9).
  rewrite /rho.
  apply: (@cycle_graph_valuation_cycle_base D c root 9 _ _).
  - lia.
  - exact dc.
  - exact sizec.
  - exact rootc.
have setcount : count_true rho
    (map (set_var 9) (vertex_list 9)) = 3.
  rewrite /rho.
  rewrite (@cycle_graph_valuation_set_count D c root 9
             (odd_active_set c)
             (fun i => ~~ (y --> cycle_label c root i)) dc sizec AsubC).
  exact cardA.
have markcount : count_true rho
    (map (mark_var 9) (vertex_list 9)) <= 5.
  have hmark : count_true rho
      (map (mark_var 9) (vertex_list 9)) =
      9 - outdeg_in (odd_cycle_set c) y.
    rewrite /rho /odd_cycle_set.
    exact: (@cycle_graph_valuation_nonarc_mark_count D c root 9 y
              (fun i => cycle_label c root i \in odd_active_set c)
              dc sizec).
  have youtd : outdeg_in (odd_cycle_set c) y = 5.
    exact: (@odd_outside_outdeg_cycle D 5 c S isT reg str ell dc sizec
              Scard Ssub y yR).
  rewrite hmark youtd.
  by [].
have zero9 : (0 < 9)%coq_nat by lia.
have rootzero : rho (set_var 9 0) = true.
  rewrite /rho (@cycle_graph_valuation_set D c root 9 _ _ 0 zero9).
  rewrite (rooted_cycle_root rootc) rootA.
  by [].
have markcountP : (count_true rho
    (map (mark_var 9) (vertex_list 9)) <= 5)%coq_nat by exact/leP.
apply: (@c9_projection_impossible rho base setcount markcountP rootzero).
apply: satisfies_cnf_flat_map=> e ein.
have eltP : (e < 9)%coq_nat.
  move: ein; rewrite /vertex_list => /List.in_seq.
  by lia.
have elt : e < 9 by exact/ltP.
rewrite /c9_endpoint_clauses satisfies_cnf_app.
split.
- unfold satisfies_cnf, eval_cnf, satisfies_clause, eval_clause.
  simpl.
  rewrite eval_negative_literal eval_positive_literal.
  rewrite /rho (@cycle_graph_valuation_set D c root 9 _ _ e eltP)
          (@cycle_graph_valuation_mark D c root 9 _ _
             (cycle_successor 9 e)).
  case qA: (cycle_label c root e \in odd_active_set c); simpl; last by [].
  have uc : uniq c by case/and3P: dc.
  have succE : cycle_label c root (cycle_successor 9 e) =
      next c (cycle_label c root e).
    exact: (cycle_label_successor uc rootc sizec isT elt).
  have omit : y --> next c (cycle_label c root e) = false.
    exact: (@odd_active_successor_omitted D 5 c S isT str ell dc sizec
              Scard Ssub order _ _ qA yR).
  by rewrite succE omit.
- rewrite satisfies_cnf_app.
  split.
  + apply: positive_guard_exactly_complete.
    * have rowlen : (4 <= List.length (internal_row 9 e))%coq_nat.
        clear ein elt.
        have rowlen_all : forall j, (j < 9)%coq_nat ->
            (4 <= List.length (internal_row 9 j))%coq_nat.
          move=> j jlt.
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          lia.
        exact: rowlen_all e eltP.
      exact rowlen.
    * case qA: (cycle_label c root e \in odd_active_set c).
      -- left.
         rewrite /rho (@cycle_graph_valuation_set D c root 9 _ _ e eltP)
                 qA.
         by [].
      -- right.
         have qC : cycle_label c root e \in odd_cycle_set c.
           rewrite /odd_cycle_set inE.
           apply: cycle_label_mem.
           by rewrite sizec.
         have outR0 : outdeg_in (odd_outside c)
             (cycle_label c root e) = 0.
           apply/eqP; rewrite -leqn0.
           move: qA; rewrite /odd_active_set inE qC /=.
           move=> hzero.
           apply/leP.
           have hnot : ~ (0 < outdeg_in (odd_outside c)
               (cycle_label c root e))%coq_nat.
             move=> hposP.
             have hpos : 0 < outdeg_in (odd_outside c)
                 (cycle_label c root e) by exact/ltP.
             by rewrite hpos in hzero.
           lia.
         have split := outdeg_split_set (odd_cycle_set c)
           (cycle_label c root e).
         rewrite (reg (cycle_label c root e)) outR0 addn0 in split.
         rewrite /rho.
         apply: (@cycle_graph_valuation_internal_row_count_in
                   D c root 9 e _ _ 5).
         ++ lia.
         ++ exact dc.
         ++ exact sizec.
         ++ exact rootc.
         ++ exact eltP.
         ++ by rewrite /odd_cycle_set -split.
  + apply: satisfies_cnf_map=> path pin.
    apply: cover_rotation_clause_complete=> settrue chordtrue.
    have qA : cycle_label c root e \in odd_active_set c.
      move: settrue.
      rewrite /rho (@cycle_graph_valuation_set D c root 9 _ _ e eltP).
      by [].
    have realized : path_chords_realized c root 9 path.
      apply: (@concrete_valuation_path_chords_realized D 9 c root path
                (fun i => cycle_label c root i \in odd_active_set c)
                (fun i => ~~ (y --> cycle_label c root i))).
      -- by [].
      -- move=> z zin.
         move: (chordtrue z zin).
         by rewrite /rho /cycle_graph_valuation.
    have ListIn_mem_seqnat : forall (z : seq nat) s,
        List.In z s -> z \in s.
      move=> z; elim=> [|a s IH] /=.
      -- by [].
      -- move=> [<-|zin].
         ++ by rewrite mem_head.
         ++ by rewrite inE (IH zin) orbT.
    have pinB : path \in two_chord_paths 9 e :=
      ListIn_mem_seqnat _ _ pin.
    have hpB : numeric_hamilton_pathb 9 e path.
      exact: (allP (two_chord_paths9_numeric elt) path pinB).
    have hp : numeric_hamilton_path 9 e path :=
      elimT (@numeric_hamilton_pathP 9 e path) hpB.
    have pathsz : size path = 9 by case: hp.
    have [x [tail [labE hpath hset hlast]]] :=
      two_chord_path9_hamilton dc sizec rootc elt pinB realized.
    have pathszc : size path = size c by rewrite pathsz sizec.
    have omitx : y --> x = false.
      exact: (@odd_certificate_hamilton_start_omitted D 5 c S isT str ell
                dc sizec Scard Ssub order root y e path x tail
                rootc yR qA pathszc labE hpath hset hlast).
    rewrite /rho (@cycle_graph_valuation_mark D c root 9 _ _
                    (List.hd 0 path)).
    case pathE : path pathsz labE => [|h t].
    * move=> pathsz _; discriminate pathsz.
    * move=> _ labE'.
      have hx : cycle_label c root h = x.
        move: (congr1 (fun s : seq D => head root s) labE').
        rewrite /labelled_numeric_path /=.
        by [].
      by rewrite /= hx omitx.
Qed.

End C9Bridge.

Section C11Bridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

Theorem ckpath_c11_graph_certificate_impossible :
  (forall v : D, outdeg v = 6) ->
  strongb D -> ell D < 12 -> dicycle c -> size c = 11 ->
  #|S| = 6 -> S \subset odd_cycle_set c ->
  (forall u v, u \in S -> u --> v -> v \in odd_cycle_set c) ->
  13 <= #|D| -> False.
Proof.
move=> reg str ell dc sizec Scard Ssub Sclosed order.
have rangeA : 3 <= #|odd_active_set c| <= 4.
  exact: (@odd_gateway_d6_active34 D 6 c S isT reg str ell dc sizec
            Scard Ssub Sclosed order erefl).
move/andP: rangeA => [lowerA upperA].
have cardA34 : #|odd_active_set c| = 3 \/ #|odd_active_set c| = 4 by lia.
have An0 : odd_active_set c != set0.
  rewrite -card_gt0.
  by lia.
move/set0Pn: An0 => [root rootA].
have AsubC : odd_active_set c \subset odd_cycle_set c.
  apply: (subset_trans (odd_active_subset_gateway Sclosed)).
  apply/subsetP=> q.
  by rewrite /odd_gateway_set inE => /andP[_].
have rootC : root \in odd_cycle_set c := subsetP AsubC root rootA.
have rootc : root \in c by move: rootC; rewrite /odd_cycle_set inE.
have cardR : 1 < #|odd_outside c|.
  exact: (@odd_outside_card_ge2 D 6 c S isT str ell dc sizec Scard
            Ssub order).
have Rn0 : odd_outside c != set0 by rewrite -card_gt0; lia.
move/set0Pn: Rn0 => [y yR].
set rho := @cycle_graph_valuation D c root 11
  (fun i => cycle_label c root i \in odd_active_set c)
  (fun i => ~~ (y --> cycle_label c root i)).
have base : satisfies_cnf rho (cycle_base_clauses 11).
  rewrite /rho.
  apply: (@cycle_graph_valuation_cycle_base D c root 11 _ _).
  - lia.
  - exact dc.
  - exact sizec.
  - exact rootc.
have setcountA : count_true rho
    (map (set_var 11) (vertex_list 11)) = #|odd_active_set c|.
  rewrite /rho.
  exact: (@cycle_graph_valuation_set_count D c root 11
            (odd_active_set c)
            (fun i => ~~ (y --> cycle_label c root i)) dc sizec AsubC).
have markcount : count_true rho
    (map (mark_var 11) (vertex_list 11)) <= 5.
  have hmark : count_true rho
      (map (mark_var 11) (vertex_list 11)) =
      11 - outdeg_in (odd_cycle_set c) y.
    rewrite /rho /odd_cycle_set.
    exact: (@cycle_graph_valuation_nonarc_mark_count D c root 11 y
              (fun i => cycle_label c root i \in odd_active_set c)
              dc sizec).
  have youtd : outdeg_in (odd_cycle_set c) y = 6.
    exact: (@odd_outside_outdeg_cycle D 6 c S isT reg str ell dc sizec
              Scard Ssub y yR).
  rewrite hmark youtd.
  by [].
have zero11 : (0 < 11)%coq_nat by lia.
have rootzero : rho (set_var 11 0) = true.
  rewrite /rho (@cycle_graph_valuation_set D c root 11 _ _ 0 zero11).
  rewrite (rooted_cycle_root rootc) rootA.
  by [].
have markcountP : (count_true rho
    (map (mark_var 11) (vertex_list 11)) <= 5)%coq_nat by exact/leP.
have endpoints : forall m, (m = 3 \/ m = 4) ->
    satisfies_cnf rho
      (List.flat_map (c11_endpoint_clauses m) (vertex_list 11)).
  move=> m mcase.
  apply: satisfies_cnf_flat_map=> e ein.
  have eltP : (e < 11)%coq_nat.
    move: ein; rewrite /vertex_list => /List.in_seq.
    by lia.
  have elt : e < 11 by exact/ltP.
  rewrite /c11_endpoint_clauses satisfies_cnf_app.
  split.
  - unfold satisfies_cnf, eval_cnf, satisfies_clause, eval_clause.
    simpl.
    rewrite eval_negative_literal eval_positive_literal.
    rewrite /rho (@cycle_graph_valuation_set D c root 11 _ _ e eltP)
            (@cycle_graph_valuation_mark D c root 11 _ _
               (cycle_successor 11 e)).
    case qA: (cycle_label c root e \in odd_active_set c); simpl; last by [].
    have uc : uniq c by case/and3P: dc.
    have succE : cycle_label c root (cycle_successor 11 e) =
        next c (cycle_label c root e).
      exact: (cycle_label_successor uc rootc sizec isT elt).
    have omit : y --> next c (cycle_label c root e) = false.
      exact: (@odd_active_successor_omitted D 6 c S isT str ell dc sizec
                Scard Ssub order _ _ qA yR).
    by rewrite succE omit.
  - rewrite satisfies_cnf_app.
    split.
    + apply: positive_guard_exactly_complete.
      * have rowlen_all : forall j, (j < 11)%coq_nat ->
            (5 <= List.length (internal_row 11 j))%coq_nat.
          move=> j jlt.
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          destruct j as [|j]; [vm_compute; lia|].
          lia.
        exact: rowlen_all e eltP.
      * case qA: (cycle_label c root e \in odd_active_set c).
        -- left.
           rewrite /rho
             (@cycle_graph_valuation_set D c root 11 _ _ e eltP) qA.
           by [].
        -- right.
           have qC : cycle_label c root e \in odd_cycle_set c.
             rewrite /odd_cycle_set inE.
             apply: cycle_label_mem.
             by rewrite sizec.
           have outR0 : outdeg_in (odd_outside c)
               (cycle_label c root e) = 0.
             apply/eqP; rewrite -leqn0.
             move: qA; rewrite /odd_active_set inE qC /=.
             move=> hzero.
             apply/leP.
             have hnot : ~ (0 < outdeg_in (odd_outside c)
                 (cycle_label c root e))%coq_nat.
               move=> hposP.
               have hpos : 0 < outdeg_in (odd_outside c)
                   (cycle_label c root e) by exact/ltP.
               by rewrite hpos in hzero.
             lia.
           have split := outdeg_split_set (odd_cycle_set c)
             (cycle_label c root e).
           rewrite (reg (cycle_label c root e)) outR0 addn0 in split.
           rewrite /rho.
           apply: (@cycle_graph_valuation_internal_row_count_in
                     D c root 11 e _ _ 6).
           ++ lia.
           ++ exact dc.
           ++ exact sizec.
           ++ exact rootc.
           ++ exact eltP.
           ++ by rewrite /odd_cycle_set -split.
    + apply: satisfies_cnf_map=> path pin.
      apply: cover_rotation_clause_complete=> settrue chordtrue.
      have qA : cycle_label c root e \in odd_active_set c.
        move: settrue.
        rewrite /rho (@cycle_graph_valuation_set D c root 11 _ _ e eltP).
        by [].
      have realized : path_chords_realized c root 11 path.
        apply: (@concrete_valuation_path_chords_realized D 11 c root path
                  (fun i => cycle_label c root i \in odd_active_set c)
                  (fun i => ~~ (y --> cycle_label c root i))).
        -- by [].
        -- move=> z zin.
           move: (chordtrue z zin).
           by rewrite /rho /cycle_graph_valuation.
      have pin23 : List.In path (two_chord_paths 11 e) \/
          List.In path (three_chord_paths e).
        destruct mcase as [m3|m4].
        -- subst m.
           change (List.In path
             (two_chord_paths 11 e ++ three_chord_paths e)%list) in pin.
           exact: (List.in_app_or _ _ _ pin).
        -- subst m.
           change (List.In path
             (two_chord_paths 11 e ++ [::])%list) in pin.
           move: (List.in_app_or _ _ _ pin) => [p2|p0].
           ++ by left.
           ++ by [].
      have ListIn_mem_seqnat : forall (z : seq nat) s,
          List.In z s -> z \in s.
        move=> z; elim=> [|a s IH] /=.
        -- by [].
        -- move=> [<-|zin].
           ++ by rewrite mem_head.
           ++ by rewrite inE (IH zin) orbT.
      have ham : exists x : D, exists tail : seq D,
          size path = 11 /\
          labelled_numeric_path c root path = x :: tail /\
          dipath x tail /\
          [set z in x :: tail] = [set z in c] /\
          last x tail = cycle_label c root e.
        case: pin23 => pin2.
        -- have pinB : path \in two_chord_paths 11 e :=
             ListIn_mem_seqnat _ _ pin2.
           have hpB : numeric_hamilton_pathb 11 e path.
             exact: (allP (two_chord_paths11_numeric elt) path pinB).
           have hp : numeric_hamilton_path 11 e path :=
             elimT (@numeric_hamilton_pathP 11 e path) hpB.
           have pathsz : size path = 11 by case: hp.
           have [x [tail [labE hpath hset hlast]]] :=
             two_chord_path11_hamilton dc sizec rootc elt pinB realized.
           exists x, tail.
           by repeat split.
        -- have pinB : path \in three_chord_paths e :=
             ListIn_mem_seqnat _ _ pin2.
           have hpB : numeric_hamilton_pathb 11 e path.
             exact: (allP (three_chord_paths11_numeric elt) path pinB).
           have hp : numeric_hamilton_path 11 e path :=
             elimT (@numeric_hamilton_pathP 11 e path) hpB.
           have pathsz : size path = 11 by case: hp.
           have [x [tail [labE hpath hset hlast]]] :=
             three_chord_path11_hamilton dc sizec rootc elt pinB realized.
           exists x, tail.
           by repeat split.
      move: ham => [x [tail [pathsz [labE [hpath [hset hlast]]]]]].
      have pathszc : size path = size c by rewrite pathsz sizec.
      have omitx : y --> x = false.
        exact: (@odd_certificate_hamilton_start_omitted D 6 c S isT str ell
                  dc sizec Scard Ssub order root y e path x tail
                  rootc yR qA pathszc labE hpath hset hlast).
      rewrite /rho (@cycle_graph_valuation_mark D c root 11 _ _
                      (List.hd 0 path)).
      case pathE : path pathsz labE => [|h t].
      * move=> pathsz _; discriminate pathsz.
      * move=> _ labE'.
        have hx : cycle_label c root h = x.
          move: (congr1 (fun s : seq D => head root s) labE').
          rewrite /labelled_numeric_path /=.
          by [].
        by rewrite /= hx omitx.
case: cardA34 => cardA.
- have setcount3 : count_true rho
      (map (set_var 11) (vertex_list 11)) = 3 by
      rewrite setcountA cardA.
  apply: (@c11_m3_projection_impossible rho base setcount3 markcountP
            rootzero).
  exact: (endpoints 3 (or_introl erefl)).
- have setcount4 : count_true rho
      (map (set_var 11) (vertex_list 11)) = 4 by
      rewrite setcountA cardA.
  apply: (@c11_m4_projection_impossible rho base setcount4 markcountP
            rootzero).
  exact: (endpoints 4 (or_intror erefl)).
Qed.

End C11Bridge.
