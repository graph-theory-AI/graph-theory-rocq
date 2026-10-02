(** * Shared graph semantics for the finite CK-path certificates. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cycle_tools ckpath_graph_count ckpath_cnf ckpath_cardinality
  ckpath_cert_base
  ckpath_cert_valuation ckpath_cert_clause_tools ckpath_rotation_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CycleValuation.
Variable D : diGraphType.

Definition cycle_graph_valuation (c : seq D) (root : D) (n : nat)
    (set_bits mark_bits : nat -> bool) : valuation :=
  concrete_valuation n
    (fun u v => cycle_label c root u --> cycle_label c root v)
    set_bits mark_bits.

Lemma cycle_graph_valuation_arc c root n set_bits mark_bits u v :
  (2 <= n)%coq_nat -> (u < n)%coq_nat -> (v < n)%coq_nat -> u <> v ->
  cycle_graph_valuation c root n set_bits mark_bits (arc_var n u v) =
    (cycle_label c root u --> cycle_label c root v).
Proof.
move=> n2 un vn uv.
exact: concrete_valuation_arc n
  (fun a b => cycle_label c root a --> cycle_label c root b)
  set_bits mark_bits u v n2 un vn uv.
Qed.

Lemma cycle_graph_valuation_set c root n set_bits mark_bits u :
  (u < n)%coq_nat ->
  cycle_graph_valuation c root n set_bits mark_bits (set_var n u) =
    set_bits u.
Proof.
move=> un.
exact: concrete_valuation_set un.
Qed.

Lemma cycle_graph_valuation_mark c root n set_bits mark_bits u :
  cycle_graph_valuation c root n set_bits mark_bits (mark_var n u) =
    mark_bits u.
Proof. exact: concrete_valuation_mark. Qed.

Lemma cycle_graph_label_enumeration c root n :
  size c = n ->
  map (cycle_label c root) (vertex_list n) = @rooted_cycle D c root.
Proof. exact: cycle_labels_vertex_list. Qed.

Lemma cycle_label_arc_count c root n q :
  dicycle c -> size c = n ->
  count_true_bits
    (map (fun i => q --> cycle_label c root i) (vertex_list n)) =
  @outdeg_in D [set z in c] q.
Proof.
move=> dc sizec.
have uc : uniq c by case/and3P: dc.
have ur : uniq (rooted_cycle c root) := rooted_cycle_uniq root uc.
have enum := cycle_graph_label_enumeration root sizec.
rewrite (@count_true_bits_map_enum_pred D
  (fun z : D => q --> z) (rooted_cycle c root)
  (cycle_label c root) (vertex_list n) ur enum).
rewrite /outdeg_in.
apply: eq_card=> z.
by rewrite !inE /rooted_cycle mem_rot.
Qed.

Lemma cycle_label_nonarc_count c root n q :
  dicycle c -> size c = n ->
  count_true_bits
    (map (fun i => ~~ (q --> cycle_label c root i)) (vertex_list n)) =
  n - @outdeg_in D [set z in c] q.
Proof.
move=> dc sizec.
have Hmap :
    [seq ~~ (q --> cycle_label c root i) | i <- vertex_list n] =
    map negb
      [seq q --> cycle_label c root i | i <- vertex_list n].
  by rewrite -map_comp /comp.
rewrite Hmap count_true_bits_map_negb.
rewrite List.length_map /vertex_list List.length_seq.
by rewrite (@cycle_label_arc_count c root n q dc sizec).
Qed.

Lemma cycle_graph_valuation_set_count c root n (A : {set D}) mark_bits :
  dicycle c -> size c = n -> A \subset [set z in c] ->
  count_true
    (cycle_graph_valuation c root n
       (fun i => cycle_label c root i \in A) mark_bits)
    (map (set_var n) (vertex_list n)) = #|A|.
Proof.
move=> dc sizec Asub.
set rho := cycle_graph_valuation c root n
  (fun i => cycle_label c root i \in A) mark_bits.
have lookup : forall i, List.In i (vertex_list n) ->
    rho (set_var n i) = (cycle_label c root i \in A).
  move=> i.
  rewrite /vertex_list => /List.in_seq [_ ilt].
  apply: cycle_graph_valuation_set.
  exact ilt.
rewrite (@count_true_map_lookup rho (set_var n)
  (fun i => cycle_label c root i \in A) (vertex_list n) lookup).
have uc : uniq c by case/and3P: dc.
have ur : uniq (rooted_cycle c root) := rooted_cycle_uniq root uc.
have enum := cycle_graph_label_enumeration root sizec.
rewrite (@count_true_bits_map_enum_pred D
  (fun z : D => z \in A) (rooted_cycle c root)
  (cycle_label c root) (vertex_list n) ur enum).
have Asubroot : A \subset [set z in rooted_cycle c root].
  apply/subsetP=> z zA.
  have zc := (subsetP Asub z zA).
  by move: zc; rewrite !inE /rooted_cycle mem_rot.
apply: eq_card=> x.
rewrite !inE.
case xA: (x \in A); last by rewrite andbF.
have xr := (subsetP Asubroot x xA).
by move: xr; rewrite inE => ->.
Qed.

Lemma cycle_graph_valuation_mark_count c root n (A : {set D}) set_bits :
  dicycle c -> size c = n -> A \subset [set z in c] ->
  count_true
    (cycle_graph_valuation c root n set_bits
       (fun i => cycle_label c root i \in A))
    (map (mark_var n) (vertex_list n)) = #|A|.
Proof.
move=> dc sizec Asub.
set rho := cycle_graph_valuation c root n set_bits
  (fun i => cycle_label c root i \in A).
have lookup : forall i, List.In i (vertex_list n) ->
    rho (mark_var n i) = (cycle_label c root i \in A).
  move=> i _.
  exact: cycle_graph_valuation_mark.
rewrite (@count_true_map_lookup rho (mark_var n)
  (fun i => cycle_label c root i \in A) (vertex_list n) lookup).
have uc : uniq c by case/and3P: dc.
have ur : uniq (rooted_cycle c root) := rooted_cycle_uniq root uc.
have enum := cycle_graph_label_enumeration root sizec.
rewrite (@count_true_bits_map_enum_pred D
  (fun z : D => z \in A) (rooted_cycle c root)
  (cycle_label c root) (vertex_list n) ur enum).
have Asubroot : A \subset [set z in rooted_cycle c root].
  apply/subsetP=> z zA.
  have zc := (subsetP Asub z zA).
  by move: zc; rewrite !inE /rooted_cycle mem_rot.
apply: eq_card=> x.
rewrite !inE.
case xA: (x \in A); last by rewrite andbF.
have xr := (subsetP Asubroot x xA).
by move: xr; rewrite inE => ->.
Qed.

Lemma cycle_graph_valuation_nonarc_mark_count c root n q set_bits :
  dicycle c -> size c = n ->
  count_true
    (cycle_graph_valuation c root n set_bits
       (fun i => ~~ (q --> cycle_label c root i)))
    (map (mark_var n) (vertex_list n)) =
  n - outdeg_in [set z in c] q.
Proof.
move=> dc sizec.
set rho := cycle_graph_valuation c root n set_bits
  (fun i => ~~ (q --> cycle_label c root i)).
have lookup : forall i, List.In i (vertex_list n) ->
    rho (mark_var n i) = ~~ (q --> cycle_label c root i).
  move=> i _.
  exact: cycle_graph_valuation_mark.
rewrite (@count_true_map_lookup rho (mark_var n)
  (fun i => ~~ (q --> cycle_label c root i)) (vertex_list n) lookup).
exact: cycle_label_nonarc_count q dc sizec.
Qed.

End CycleValuation.

Lemma cycle_successor_neq n u :
  (2 <= n)%coq_nat -> (u < n)%coq_nat -> cycle_successor n u <> u.
Proof.
intros Hn Hu.
unfold cycle_successor.
assert (Hle : (u + 1 <= n)%coq_nat) by lia.
destruct (PeanoNat.Nat.eq_dec (u + 1)%coq_nat n) as [Heq | Hneq].
- have nNZ : n <> 0 by lia.
  rewrite Heq (PeanoNat.Nat.Private_NDivProp.mod_same n nNZ).
  lia.
- have Hlt : (u + 1 < n)%coq_nat by lia.
  rewrite (PeanoNat.Nat.mod_small (u + 1) n Hlt).
  lia.
Qed.

Section OrientedCycleValuation.
Variable D : orientedDigraph.

Lemma cycle_graph_valuation_cycle_base c root n set_bits mark_bits :
  (2 <= n)%coq_nat -> dicycle c -> size c = n -> root \in c ->
  satisfies_cnf (@cycle_graph_valuation D c root n set_bits mark_bits)
                (cycle_base_clauses n).
Proof.
move=> n2 dc sizec rootc.
rewrite /cycle_base_clauses satisfies_cnf_app.
split.
- apply: satisfies_cnf_flat_map=> u hu.
  apply: satisfies_cnf_map=> v hv.
  have hu' := hu.
  rewrite /vertex_list in hu'.
  apply List.in_seq in hu'.
  apply List.in_seq in hv.
  have un : (u < n)%coq_nat by lia.
  have vn : (v < n)%coq_nat by lia.
  have uv : u <> v by lia.
  unfold satisfies_clause, eval_clause.
  simpl.
  rewrite !eval_negative_literal
    (@cycle_graph_valuation_arc D c root n set_bits mark_bits u v
       n2 un vn uv)
    (@cycle_graph_valuation_arc D c root n set_bits mark_bits v u
       n2 vn un (not_eq_sym uv)).
  simpl.
  case auv: (cycle_label c root u --> cycle_label c root v).
  + rewrite (arc_asymm _ _ auv).
    by [].
  + by [].
- apply: satisfies_cnf_map=> u hu.
  have hu' := hu.
  rewrite /vertex_list in hu'.
  apply List.in_seq in hu'.
  have un : (u < n)%coq_nat by lia.
  have nNZ : n <> 0 by lia.
  have sun : (cycle_successor n u < n)%coq_nat.
    rewrite /cycle_successor.
    exact: PeanoNat.Nat.mod_upper_bound _ _ nNZ.
  have us : u <> cycle_successor n u.
    exact: not_eq_sym (cycle_successor_neq n2 un).
  unfold satisfies_clause, eval_clause.
  simpl.
  rewrite eval_positive_literal
    (@cycle_graph_valuation_arc D c root n set_bits mark_bits
       u (cycle_successor n u) n2 un sun us).
  simpl.
  have uc : uniq c by case/and3P: dc.
  have npos : 0 < n by apply/ltP; lia.
  have ub : u < n by exact/ltP.
  rewrite (cycle_label_successor uc rootc sizec npos ub) orbF.
  apply: (@dicycle_next D c (cycle_label c root u) dc).
  apply: cycle_label_mem.
  by rewrite sizec.
Qed.

Lemma cycle_graph_valuation_internal_row_count_in
    c root n e set_bits mark_bits d :
  (3 <= n)%coq_nat -> dicycle c -> size c = n -> root \in c ->
  (e < n)%coq_nat ->
  outdeg_in [set z in c] (cycle_label c root e) = d ->
  count_true (@cycle_graph_valuation D c root n set_bits mark_bits)
             (internal_row n e) = d - 1.
Proof.
move=> n3 dc sizec rootc en outd.
have n2 : (2 <= n)%coq_nat by lia.
have enB : e < n by exact/ltP.
have npos : 0 < n by apply/ltP; lia.
have uc : uniq c by case/and3P: dc.
set q := cycle_label c root e.
set succ := cycle_successor n e.
set pred := cycle_predecessor n e.
set p : nat -> bool := fun i => q --> cycle_label c root i.
set guard : nat -> bool := fun i =>
  negb (PeanoNat.Nat.eqb i e ||
        PeanoNat.Nat.eqb i succ ||
        PeanoNat.Nat.eqb i pred).
set ids := filter guard (vertex_list n).
set rho := @cycle_graph_valuation D c root n set_bits mark_bits.
change (count_true rho (map (arc_var n e) ids) = d - 1).
have lookup : forall i, List.In i ids ->
    rho (arc_var n e i) = p i.
  move=> i hi.
  have hi' := hi.
  rewrite /ids in hi'.
  apply List.filter_In in hi'.
  case: hi' => hiv hguard.
  rewrite /vertex_list in hiv.
  apply List.in_seq in hiv.
  have in_ : (i < n)%coq_nat by lia.
  have ie : i <> e.
    move=> ie; subst i.
    move: hguard.
    by rewrite /guard PeanoNat.Nat.eqb_refl.
  apply: (@cycle_graph_valuation_arc D c root n set_bits mark_bits
            e i n2 en in_ (not_eq_sym ie)).
rewrite (@count_true_map_lookup rho (arc_var n e) p ids lookup).
rewrite count_true_bits_map_pred.
have qmem : q \in c.
  rewrite /q.
  apply: cycle_label_mem.
  by rewrite sizec.
have succB : succ < n.
  rewrite /succ.
  exact: cycle_successor_lt e npos.
have pe : p e = false by rewrite /p /q arc_irrefl.
have psucc : p succ = true.
  rewrite /p /q /succ
    (cycle_label_successor uc rootc sizec npos enB).
  exact: (@dicycle_next D c (cycle_label c root e) dc qmem).
have ppred : p pred = false.
  rewrite /p /q /pred
    (cycle_label_predecessor uc rootc sizec npos enB).
  exact: arc_asymm _ _
    (@dicycle_prev D c (cycle_label c root e) dc qmem).
have fullcount : count p (vertex_list n) = d.
  have h := (@cycle_label_arc_count D c root n q dc sizec).
  rewrite count_true_bits_map_pred in h.
  by rewrite /p outd in h.
have ufull : uniq (vertex_list n) by rewrite /vertex_list iota_uniq.
have succmem : succ \in vertex_list n.
  by rewrite /vertex_list mem_iota add0n succB.
have countsame :
    count p ids = count p (rem succ (vertex_list n)).
  rewrite /ids (rem_filter succ ufull) !count_filter.
  apply: eq_in_count=> x xmem.
  rewrite /predI /predC1 /=.
  case px: (p x); last by [].
  have xeF : PeanoNat.Nat.eqb x e = false.
    apply PeanoNat.Nat.eqb_neq=> xe.
    subst x.
    by rewrite pe in px.
  have xpF : PeanoNat.Nat.eqb x pred = false.
    apply PeanoNat.Nat.eqb_neq=> xp.
    subst x.
    by rewrite ppred in px.
  rewrite /guard xeF xpF.
  case xs: (PeanoNat.Nat.eqb x succ).
  - apply PeanoNat.Nat.eqb_eq in xs.
    subst x.
    by rewrite eqxx.
  - have xDs : x != succ.
      apply/negP=> /eqP xeq.
      subst x.
      by rewrite PeanoNat.Nat.eqb_refl in xs.
    by rewrite xDs.
rewrite countsame count_rem succmem psucc.
by rewrite fullcount.
Qed.

Lemma cycle_graph_valuation_internal_row_count_closed
    c root n e set_bits mark_bits d :
  (3 <= n)%coq_nat -> dicycle c -> size c = n -> root \in c ->
  (e < n)%coq_nat ->
  outdeg (cycle_label c root e) = d ->
  (forall z, cycle_label c root e --> z -> z \in [set x in c]) ->
  count_true (@cycle_graph_valuation D c root n set_bits mark_bits)
             (internal_row n e) = d - 1.
Proof.
move=> n3 dc sizec rootc en outd closed.
have indeg :
    outdeg_in [set z in c] (cycle_label c root e) = d.
  rewrite -outd /outdeg_in /outdeg.
  apply: eq_card=> z.
  rewrite !inE.
  case az: (cycle_label c root e --> z).
  - have zc := closed z az.
    move: zc; rewrite inE => ->.
    by [].
  - by rewrite andbF.
exact: (@cycle_graph_valuation_internal_row_count_in
          c root n e set_bits mark_bits d
          n3 dc sizec rootc en indeg).
Qed.

End OrientedCycleValuation.
