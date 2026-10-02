(** * Graph semantics for the k=7 C13, a=1 finite endgame *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath strong
  ckpath_cycle_tools ckpath_odd_gateway
  ckpath_cnf ckpath_cardinality ckpath_cert_base ckpath_cert_k7_base
  ckpath_cert_clause_tools ckpath_cert_k7_clause_tools
  ckpath_cert_k7_semantics ckpath_rotation_paths
  ckpath_rotation_paths_k7 ckpath_cert_graph_common ckpath_k7_orbits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Lemma c13_k7_internal_row_length endpoint :
  (endpoint < 13)%coq_nat -> List.length (internal_row 13 endpoint) = 10.
Proof.
intros hlt.
do 13 (destruct endpoint as [|endpoint]; [vm_compute; reflexivity |]).
lia.
Qed.

Section C13GraphBridge.
Variable D : orientedDigraph.
Variables (c : seq D) (S : {set D}).

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

Definition c13_k7_graph_valuation (root y : D) : valuation :=
  cycle_graph_valuation c root 13
    (fun i => cycle_label c root i \in A)
    (fun i => ~~ (y --> cycle_label c root i)).

Local Lemma c13_k7_active_subset_cycle : A \subset C.
Proof.
apply: (subset_trans (odd_active_subset_gateway HSclosed)).
apply/subsetP=> q.
by rewrite /odd_gateway_set inE => /andP[_].
Qed.

(** A listed Hamilton path ending at an active gateway cannot start at an
    out-neighbour of an outside vertex.  This is the generic odd-cycle
    splice, kept local so the semantic bridge does not depend on any older
    generated certificate module. *)
Local Lemma c13_k7_hamilton_start_omitted
    root y endpoint path x tail :
  root \in c -> y \in R -> cycle_label c root endpoint \in A ->
  size path = size c ->
  labelled_numeric_path c root path = x :: tail ->
  dipath x tail -> [set z in x :: tail] = C ->
  last x tail = cycle_label c root endpoint ->
  y --> x = false.
Proof.
move=> rootc yR qA pathsz labE hpath hset hlast.
have [u uR qu] : exists2 u, u \in R &
    cycle_label c root endpoint --> u.
  move: qA; rewrite /A /odd_active_set inE => /andP[_ qpos].
  move: qpos; rewrite /outdeg_in card_gt0 => /set0Pn[u].
  rewrite inE => /andP[uR qu].
  by exists u.
have uout : u \notin x :: tail.
  apply/negP=> uin.
  have uC : u \in C by rewrite -hset in_set uin.
  by move: uR; rewrite /R /odd_outside inE uC.
have yout : y \notin x :: tail.
  apply/negP=> yin.
  have yC : y \in C by rewrite -hset in_set yin.
  by move: yR; rewrite /R /odd_outside inE yC.
have tailsz : (size tail).+1 = size c.
  move: (congr1 size labE).
  rewrite /labelled_numeric_path size_map /= pathsz.
  by [].
have elltail : ell D < (size tail).+2 by lia.
case: (eqVneq y u) => [->|yu].
- have [v vR vu] :=
    @odd_outside_second D 7 c S isT Hstr Hell Hcycle Hcsize
      HScard HSsub Horder u uR.
  have [z zC vz] :=
    @odd_outside_points_cycle D 7 c S isT Hstr Hell Hcycle Hcsize
      HScard HSsub v vR.
  have vout : v \notin x :: tail.
    apply/negP=> vin.
    have vC : v \in C by rewrite -hset in_set vin.
    by move: vR; rewrite /R /odd_outside inE vC.
  have zinset : z \in [set z in x :: tail] by rewrite hset.
  have zin : z \in x :: tail by move: zinset; rewrite in_set.
  have uv : u != v by rewrite eq_sym.
  exact: (hamilton_active_start_omitted hpath hlast uout vout uv qu
            zin vz elltail).
- have uy : u != y by rewrite eq_sym.
  exact: (hamilton_start_omitted hpath hlast uout yout uy qu elltail).
Qed.

Local Lemma c13_k7_graph_endpoint_clauses root y endpoint :
  root \in c -> y \in R ->
  (endpoint < 13)%coq_nat ->
  satisfies_cnf (c13_k7_graph_valuation root y)
    (c13_k7_cover_endpoint_clauses endpoint).
Proof.
move=> rootc yR endlt.
have endltB : endpoint < 13 by exact/ltP.
rewrite /c13_k7_cover_endpoint_clauses !satisfies_cnf_app.
split.
- unfold satisfies_cnf, eval_cnf, satisfies_clause, eval_clause.
  simpl.
  rewrite eval_negative_literal eval_positive_literal.
  rewrite /c13_k7_graph_valuation
    (@cycle_graph_valuation_set D c root 13 _ _ endpoint endlt)
    (@cycle_graph_valuation_mark D c root 13 _ _
       (cycle_successor 13 endpoint)).
  case qA: (cycle_label c root endpoint \in A); simpl; last by [].
  have uc : uniq c by case/and3P: Hcycle.
  have succE : cycle_label c root (cycle_successor 13 endpoint) =
      next c (cycle_label c root endpoint).
    exact: (cycle_label_successor uc rootc Hcsize isT endltB).
  have omit : y --> next c (cycle_label c root endpoint) = false.
    exact: (@odd_active_successor_omitted D 7 c S isT Hstr Hell Hcycle
              Hcsize HScard HSsub Horder _ _ qA yR).
  by rewrite succE omit.
- split.
  * have Hlen : (6 <= List.length (internal_row 13 endpoint))%coq_nat.
      rewrite (c13_k7_internal_row_length endlt).
      lia.
    have Hcase :
        c13_k7_graph_valuation root y (set_var 13 endpoint) = true \/
        count_true (c13_k7_graph_valuation root y)
          (internal_row 13 endpoint) = 6.
      case qA: (cycle_label c root endpoint \in A).
      -- left.
         rewrite /c13_k7_graph_valuation
           (@cycle_graph_valuation_set D c root 13 _ _ endpoint endlt) qA.
         by [].
      -- right.
         have qC : cycle_label c root endpoint \in C.
           rewrite /odd_cycle_set inE.
           apply: cycle_label_mem.
           by rewrite Hcsize.
         have outR0 : outdeg_in R (cycle_label c root endpoint) = 0.
           apply/eqP; rewrite -leqn0.
           move: qA; rewrite /odd_active_set inE qC /=.
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
         rewrite /c13_k7_graph_valuation.
         apply: (@cycle_graph_valuation_internal_row_count_in
                   D c root 13 endpoint _ _ 7).
         ++ lia.
         ++ exact Hcycle.
         ++ exact Hcsize.
         ++ exact rootc.
         ++ exact endlt.
         ++ by rewrite /odd_cycle_set -split.
    have Hexact := positive_guard_exactly_complete
      (c13_k7_graph_valuation root y) (set_var 13 endpoint) 6
      (internal_row 13 endpoint) Hlen Hcase.
    move: Hexact.
    by rewrite /exactly_comb satisfies_cnf_app.
  * split.
    + apply: negative_guard_at_most_complete.
      case qA: (cycle_label c root endpoint \in A).
      -- right.
         have qC : cycle_label c root endpoint \in C.
           exact: subsetP c13_k7_active_subset_cycle _ qA.
         have qpos : 0 < outdeg_in R (cycle_label c root endpoint).
           by move: qA; rewrite /odd_active_set inE qC.
         have split := outdeg_split_set C
           (cycle_label c root endpoint).
         rewrite (Hreg (cycle_label c root endpoint)) in split.
         have outCle : (outdeg_in C
             (cycle_label c root endpoint) <= 6)%coq_nat.
           move/ltP: qpos => qposP.
           rewrite /R /odd_outside in qposP.
           apply/leP; lia.
         have n3 : (3 <= 13)%coq_nat by lia.
         have rowE :=
           (@cycle_graph_valuation_internal_row_count_in
             D c root 13 endpoint
             (fun i => cycle_label c root i \in A)
             (fun i => ~~ (y --> cycle_label c root i))
             (outdeg_in C (cycle_label c root endpoint))
             n3 Hcycle Hcsize rootc endlt erefl).
         rewrite /c13_k7_graph_valuation rowE.
         lia.
      -- left.
         rewrite /c13_k7_graph_valuation
           (@cycle_graph_valuation_set D c root 13 _ _ endpoint endlt) qA.
         by [].
    + apply: satisfies_cnf_map=> path pin.
      apply: cover_rotation_clause_complete=> settrue chordtrue.
      have qA : cycle_label c root endpoint \in A.
        move: settrue.
        rewrite /c13_k7_graph_valuation
          (@cycle_graph_valuation_set D c root 13 _ _ endpoint endlt).
        by [].
      have realized : path_chords_realized c root 13 path.
        apply: (@concrete_valuation_path_chords_realized D 13 c root path
                  (fun i => cycle_label c root i \in A)
                  (fun i => ~~ (y --> cycle_label c root i))).
        -- by [].
        -- move=> z zin.
           move: (chordtrue z zin).
           by rewrite /c13_k7_graph_valuation /cycle_graph_valuation.
      have ListIn_mem_seqnat : forall (z : seq nat) s,
          List.In z s -> z \in s.
        move=> z; elim=> [|a s IH] /=.
        -- by [].
        -- move=> [<-|zin].
           ++ by rewrite mem_head.
           ++ by rewrite inE (IH zin) orbT.
      have pin23 : List.In path (two_chord_paths 13 endpoint) \/
          List.In path (reverse_three_block_paths 13 endpoint).
        change (List.In path
          (two_chord_paths 13 endpoint ++
           reverse_three_block_paths 13 endpoint)%list) in pin.
        exact: (List.in_app_or _ _ _ pin).
      have ham : exists x : D, exists tail : seq D,
          size path = 13 /\
          labelled_numeric_path c root path = x :: tail /\
          dipath x tail /\
          [set z in x :: tail] = [set z in c] /\
          last x tail = cycle_label c root endpoint.
        case: pin23 => pin0.
        -- have pinB : path \in two_chord_paths 13 endpoint :=
             ListIn_mem_seqnat _ _ pin0.
           have hpB : numeric_hamilton_pathb 13 endpoint path.
             exact: (allP (two_chord_paths13_numeric endltB) path pinB).
           have hp : numeric_hamilton_path 13 endpoint path :=
             elimT (@numeric_hamilton_pathP 13 endpoint path) hpB.
           have pathsz : size path = 13 by case: hp.
           have [x [tail [labE hpath hset hlast]]] :=
             two_chord_path13_hamilton Hcycle Hcsize rootc endltB
               pinB realized.
           exists x, tail.
           by repeat split.
        -- have pinB : path \in reverse_three_block_paths 13 endpoint :=
             ListIn_mem_seqnat _ _ pin0.
           have hpB : numeric_hamilton_pathb 13 endpoint path.
             exact: (allP (reverse_three_block_paths13_numeric endltB)
                       path pinB).
           have hp : numeric_hamilton_path 13 endpoint path :=
             elimT (@numeric_hamilton_pathP 13 endpoint path) hpB.
           have pathsz : size path = 13 by case: hp.
           have [x [tail [labE hpath hset hlast]]] :=
             reverse_three_block_path13_hamilton Hcycle Hcsize rootc endltB
               pinB realized.
           exists x, tail.
           by repeat split.
      move: ham => [x [tail [pathsz [labE [hpath [hset hlast]]]]]].
      have pathszc : size path = size c by rewrite pathsz Hcsize.
      have omitx : y --> x = false.
        exact: c13_k7_hamilton_start_omitted rootc yR qA pathszc labE
          hpath hset hlast.
      rewrite /c13_k7_graph_valuation
        (@cycle_graph_valuation_mark D c root 13 _ _ (List.hd 0 path)).
      case pathE : path pathsz labE => [|h t].
      -- move=> pathsz _; discriminate pathsz.
      -- move=> _ labE'.
         have hx : cycle_label c root h = x.
           move: (congr1 (fun s : seq D => head root s) labE').
           rewrite /labelled_numeric_path /=.
           by [].
         by rewrite /= hx omitx.
Qed.

(** The cover base is satisfied at every active root, for any chosen outside
    vertex [y].  The explicit root is the interface needed by cyclic orbit
    normalization. *)
Theorem ckpath_k7_c13_graph_cover_base_satisfied_at_root root y :
  root \in c -> root \in A -> y \in R ->
  satisfies_cnf (c13_k7_graph_valuation root y)
    (c13_k7_cover_base #|A|).
Proof.
move=> rootc rootA yR.
have rangeA : 3 <= #|A| <= 5.
  exact: (@odd_gateway_d7_active345 D 7 c S isT Hreg Hstr Hell
            Hcycle Hcsize HScard HSsub HSclosed Horder erefl).
move/andP: rangeA => [lowerA upperA].
set rho := c13_k7_graph_valuation root y.
have n2 : (2 <= 13)%coq_nat by lia.
have base : satisfies_cnf rho (cycle_base_clauses 13).
  rewrite /rho /c13_k7_graph_valuation.
  exact: (@cycle_graph_valuation_cycle_base D c root 13 _ _
            n2 Hcycle Hcsize rootc).
have setcount : count_true rho
    (map (set_var 13) (vertex_list 13)) = #|A|.
  rewrite /rho /c13_k7_graph_valuation.
  exact: (@cycle_graph_valuation_set_count D c root 13 A
            (fun i => ~~ (y --> cycle_label c root i))
            Hcycle Hcsize c13_k7_active_subset_cycle).
have markcount : (count_true rho
    (map (mark_var 13) (vertex_list 13)) <= 6)%coq_nat.
  have hmark : count_true rho
      (map (mark_var 13) (vertex_list 13)) =
      13 - outdeg_in C y.
    rewrite /rho /c13_k7_graph_valuation /odd_cycle_set.
    exact: (@cycle_graph_valuation_nonarc_mark_count D c root 13 y
              (fun i => cycle_label c root i \in A) Hcycle Hcsize).
  have youtd : outdeg_in C y = 7.
    exact: (@odd_outside_outdeg_cycle D 7 c S isT Hreg Hstr Hell Hcycle
              Hcsize HScard HSsub y yR).
  rewrite hmark youtd.
  lia.
have rootzero : rho (set_var 13 0) = true.
  rewrite /rho /c13_k7_graph_valuation.
  have zeroLt : (0 < 13)%coq_nat by lia.
  rewrite (@cycle_graph_valuation_set D c root 13 _ _ 0 zeroLt).
  by rewrite (rooted_cycle_root rootc) rootA.
have endpoints : satisfies_cnf rho
    (List.flat_map c13_k7_cover_endpoint_clauses (vertex_list 13)).
  apply: satisfies_cnf_flat_map=> endpoint endpointin.
  have endlt : (endpoint < 13)%coq_nat.
    move: endpointin; rewrite /vertex_list => /List.in_seq.
    lia.
  exact: c13_k7_graph_endpoint_clauses rootc yR endlt.
have sat : satisfies_cnf rho (c13_k7_cover_base #|A|).
  apply: (@c13_k7_cover_base_satisfied rho #|A|).
  - lia.
  - exact base.
  - exact setcount.
  - exact markcount.
  - exact rootzero.
  - exact endpoints.
exact sat.
Qed.

(** Existing graph-to-base interface retained for the k=7 assembly. *)
Theorem ckpath_k7_c13_graph_satisfies_cover_base :
  exists m rho,
    [ /\ m = 3 \/ m = 4 \/ m = 5,
        #|A| = m
      & satisfies_cnf rho (c13_k7_cover_base m) ].
Proof.
have rangeA : 3 <= #|A| <= 5.
  exact: (@odd_gateway_d7_active345 D 7 c S isT Hreg Hstr Hell
            Hcycle Hcsize HScard HSsub HSclosed Horder erefl).
move/andP: rangeA => [lowerA upperA].
have cardA345 : #|A| = 3 \/ #|A| = 4 \/ #|A| = 5 by lia.
have An0 : A != set0 by rewrite -card_gt0; lia.
move/set0Pn: An0 => [root rootA].
have rootC : root \in C := subsetP c13_k7_active_subset_cycle root rootA.
have rootc : root \in c by move: rootC; rewrite /odd_cycle_set inE.
have cardR : 1 < #|R|.
  exact: (@odd_outside_card_ge2 D 7 c S isT Hstr Hell Hcycle Hcsize
            HScard HSsub Horder).
have Rn0 : R != set0 by rewrite -card_gt0; lia.
move/set0Pn: Rn0 => [y yR].
have sat : satisfies_cnf (c13_k7_graph_valuation root y)
    (c13_k7_cover_base #|A|).
  exact: ckpath_k7_c13_graph_cover_base_satisfied_at_root
    rootc rootA yR.
exists #|A|, (c13_k7_graph_valuation root y).
by split.
Qed.

(** Orbit-normalized realization used by the three fixed-set C13 certificate
    families. *)
Theorem ckpath_k7_c13_graph_fixed_instance_satisfied :
  exists m mask rho,
    [ /\ m = 3 \/ m = 4 \/ m = 5,
        #|A| = m,
        List.In mask (orbit_representatives 13 m)
      & satisfies_cnf rho
          (fixed_set_instance (c13_k7_cover_base m) 13 mask) ].
Proof.
have rangeA : 3 <= #|A| <= 5.
  exact: (@odd_gateway_d7_active345 D 7 c S isT Hreg Hstr Hell
            Hcycle Hcsize HScard HSsub HSclosed Horder erefl).
move/andP: rangeA => [lowerA upperA].
have cardA345 : #|A| = 3 \/ #|A| = 4 \/ #|A| = 5 by lia.
have Hrooted : representatives_rootedb 13 #|A| = true.
  case: cardA345 => [cardA3 | [cardA4 | cardA5]].
  - rewrite cardA3.
    exact k7_orbit_representatives_13_3_rooted.
  - rewrite cardA4.
    exact k7_orbit_representatives_13_4_rooted.
  - rewrite cardA5.
    exact k7_orbit_representatives_13_5_rooted.
have Apos : (0 < #|A|)%coq_nat by lia.
have uc : uniq c by case/and3P: Hcycle.
have Asubc : A \subset [set z in c].
  move: c13_k7_active_subset_cycle.
  by rewrite /C /odd_cycle_set.
have [root [rootc [rootA [Hrep Hmask]]]] :=
  @choose_cycle_set_orbit_root D c A 13 #|A| uc Hcsize Asubc erefl
    Apos Hrooted.
have cardR : 1 < #|R|.
  exact: (@odd_outside_card_ge2 D 7 c S isT Hstr Hell Hcycle Hcsize
            HScard HSsub Horder).
have Rn0 : R != set0 by rewrite -card_gt0; lia.
move/set0Pn: Rn0 => [y yR].
have Hbase : satisfies_cnf
    (c13_k7_graph_valuation root y) (c13_k7_cover_base #|A|).
  exact: ckpath_k7_c13_graph_cover_base_satisfied_at_root
    rootc rootA yR.
have Hfixed : satisfies_cnf
    (c13_k7_graph_valuation root y)
    (fixed_set_instance (c13_k7_cover_base #|A|) 13
      (cycle_set_mask c root 13 A)).
  exact: (@cycle_graph_valuation_fixed_set_instance
    D c root 13 A
    (fun i => ~~ (y --> cycle_label c root i))
    (c13_k7_cover_base #|A|) Hbase).
exists #|A|, (cycle_set_mask c root 13 A),
  (c13_k7_graph_valuation root y).
by split.
Qed.

End C13GraphBridge.
