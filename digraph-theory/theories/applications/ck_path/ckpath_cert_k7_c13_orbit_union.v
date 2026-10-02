(** * One certificate per C13 active-set size

    A canonical cyclic representative can be enforced without fixing a
    particular active-set mask.  The normalized base already makes vertex
    zero active.  We append one blocking clause for each other rooted
    fixed-weight mask, leaving exactly the 22, 55, or 99 canonical necklaces
    in the formula.  Thus each active-set size needs one certificate rather
    than one certificate per necklace. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import prelude digraph oriented dipath strong
  ckpath_cycle_tools ckpath_odd_gateway ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_clause_tools ckpath_cert_k7_base
  ckpath_cert_graph_common ckpath_rotation_paths ckpath_k7_orbits
  ckpath_cert_graph_k7_c13_semantics.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Executable orbit-union clauses *)

Definition rooted_fixed_weight_words (n k : nat) : list (list bool) :=
  List.filter (fun s => List.hd false s) (fixed_weight_words n k).

Definition nonrepresentative_rooted_words
    (n k : nat) : list (list bool) :=
  List.filter
    (fun s => negb (word_mem s (orbit_representatives n k)))
    (rooted_fixed_weight_words n k).

Definition set_mask_vars (n : nat) : list nat :=
  List.map (set_var n) (vertex_list n).

Definition orbit_representative_blockers (n k : nat) : cnf :=
  List.map (blocking_clause (set_mask_vars n))
    (nonrepresentative_rooted_words n k).

Definition c13_k7_orbit_union_base (active_size : nat) : cnf :=
  c13_k7_cover_base active_size ++
  [[positive_literal (mark_var 13 0)]] ++
  orbit_representative_blockers 13 active_size.

(** ** Generic Boolean and blocking-clause plumbing *)

Lemma bit_vectors_member_length n bits :
  List.In bits (bit_vectors n) -> List.length bits = n.
Proof.
revert bits.
induction n as [|n IH]; intros bits Hbits; simpl in Hbits.
- destruct Hbits as [<- | []]. reflexivity.
- apply List.in_app_or in Hbits.
  destruct Hbits as [Hbits | Hbits];
    apply List.in_map_iff in Hbits;
    destruct Hbits as [tail [<- Htail]];
    simpl; now rewrite (IH tail Htail).
Qed.

Lemma fixed_weight_words_member_length n k bits :
  List.In bits (fixed_weight_words n k) -> List.length bits = n.
Proof.
rewrite /fixed_weight_words List.filter_In.
move=> [Hbits _].
exact: bit_vectors_member_length Hbits.
Qed.

Lemma bool_word_eqb_refl bits : bool_word_eqb bits bits = true.
Proof.
induction bits as [|b bits IH]; simpl; first reflexivity.
by destruct b; simpl; rewrite IH.
Qed.

Lemma word_mem_complete bits words :
  List.In bits words -> word_mem bits words = true.
Proof.
move=> Hbits.
rewrite /word_mem List.existsb_exists.
exists bits; split; [exact Hbits | exact: bool_word_eqb_refl].
Qed.

Lemma blocking_clause_false_map rho xs bits :
  List.length xs = List.length bits ->
  eval_clause rho (blocking_clause xs bits) = false ->
  List.map rho xs = bits.
Proof.
revert bits.
induction xs as [|x xs IH]; intros [|b bits] Hlen Hfalse;
    simpl in Hlen; try lia.
- reflexivity.
- change
    (eval_literal rho (x, negb b) ||
       eval_clause rho (blocking_clause xs bits) = false) in Hfalse.
  apply Bool.orb_false_iff in Hfalse as [Hhead Htail].
  have Hxb : rho x = b.
    move: Hhead.
    unfold eval_literal; simpl.
    by destruct (rho x), b.
  simpl.
  rewrite Hxb.
  f_equal.
  apply: IH Htail.
  lia.
Qed.

Lemma blocking_clause_other_true rho xs bits :
  List.length xs = List.length bits ->
  List.map rho xs <> bits ->
  satisfies_clause rho (blocking_clause xs bits).
Proof.
move=> Hlen Hneq.
unfold satisfies_clause.
case Heval: (eval_clause rho (blocking_clause xs bits)); first reflexivity.
exfalso; apply Hneq.
exact: blocking_clause_false_map Hlen Heval.
Qed.

Lemma set_mask_vars_length n : List.length (set_mask_vars n) = n.
Proof.
by rewrite /set_mask_vars List.length_map /vertex_list List.length_seq.
Qed.

Lemma orbit_representative_blockers_satisfied rho n k mask :
  List.In mask (orbit_representatives n k) ->
  List.map rho (set_mask_vars n) = mask ->
  satisfies_cnf rho (orbit_representative_blockers n k).
Proof.
move=> Hrep Hmask.
rewrite /orbit_representative_blockers.
apply: satisfies_cnf_map => bad Hbad.
rewrite /nonrepresentative_rooted_words List.filter_In in Hbad.
move: Hbad=> [Hrooted Hnotmem].
rewrite /rooted_fixed_weight_words List.filter_In in Hrooted.
move: Hrooted=> [Hweight _].
have Hbadlen : List.length bad = n.
  exact: fixed_weight_words_member_length Hweight.
have HbadNrep : ~ List.In bad (orbit_representatives n k).
  move=> Hbadrep.
  have Hmem := word_mem_complete Hbadrep.
  rewrite Hmem in Hnotmem.
  discriminate.
have HmaskDbad : mask <> bad.
  move=> Hmaskbad; subst bad.
  exact: HbadNrep Hrep.
apply: blocking_clause_other_true.
- by rewrite set_mask_vars_length Hbadlen.
- by rewrite Hmask.
Qed.

Section CycleSetMaskBits.
Variable D : diGraphType.

Lemma cycle_graph_valuation_set_mask_bits
    c root n (A : {set D}) mark_bits :
  List.map
    (cycle_graph_valuation c root n
      (fun i => cycle_label c root i \in A) mark_bits)
    (set_mask_vars n) =
  cycle_set_mask c root n A.
Proof.
rewrite /set_mask_vars /cycle_set_mask /vertex_list !List.map_map.
apply List.map_ext_in=> i Hi.
apply cycle_graph_valuation_set.
apply List.in_seq in Hi.
lia.
Qed.

End CycleSetMaskBits.

(** ** Graph realization of the orbit union *)

Section C13OrbitUnionGraphBridge.
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

Lemma c13_k7_orbit_union_satisfied_at_root root y :
  root \in c -> root \in A -> y \in R -> root --> y ->
  List.In (cycle_set_mask c root 13 A)
    (orbit_representatives 13 #|A|) ->
  satisfies_cnf (c13_k7_graph_valuation c root y)
    (c13_k7_orbit_union_base #|A|).
Proof.
move=> rootc rootA yR rooty Hrep.
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
have Hbits :
    List.map rho (set_mask_vars 13) = cycle_set_mask c root 13 A.
  rewrite /rho /c13_k7_graph_valuation.
  exact: cycle_graph_valuation_set_mask_bits.
have Hblockers : satisfies_cnf rho
    (orbit_representative_blockers 13 #|A|).
  exact: orbit_representative_blockers_satisfied Hrep Hbits.
change (satisfies_cnf rho
  (c13_k7_cover_base #|A| ++
    [[positive_literal (mark_var 13 0)]] ++
    orbit_representative_blockers 13 #|A|)).
apply: (proj2 (satisfies_cnf_app rho _ _)); split; first exact Hbase.
apply: (proj2 (satisfies_cnf_app rho _ _)); split.
- exact Hmark0.
- exact Hblockers.
Qed.

Theorem ckpath_k7_c13_graph_satisfies_orbit_union_base :
  exists m rho,
    [ /\ m = 3 \/ m = 4 \/ m = 5,
        #|A| = m
      & satisfies_cnf rho (c13_k7_orbit_union_base m) ].
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
  apply: (subset_trans
    (@odd_active_subset_gateway D c S HSclosed)).
  apply/subsetP=> q.
  by rewrite /odd_gateway_set inE => /andP[].
have [root [rootc [rootA [Hrep _]]]] :=
  @choose_cycle_set_orbit_root D c A 13 #|A| uc Hcsize Asubc erefl
    Apos Hrooted.
have [y yR rooty] : exists2 y, y \in R & root --> y.
  exact: (@odd_active_witness D c root rootA).
have Hsat : satisfies_cnf (c13_k7_graph_valuation c root y)
    (c13_k7_orbit_union_base #|A|).
  exact: c13_k7_orbit_union_satisfied_at_root
    rootc rootA yR rooty Hrep.
exists #|A|, (c13_k7_graph_valuation c root y).
by split.
Qed.

End C13OrbitUnionGraphBridge.
