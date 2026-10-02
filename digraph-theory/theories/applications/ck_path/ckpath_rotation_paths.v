(** * Rotated cycle labels and certificate path bridges. *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cycle_tools ckpath_cert_base ckpath_cert_valuation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Labels.
Variable D : diGraphType.

(** Rotate a cycle so that the chosen root receives numeric label zero. *)
Definition rooted_cycle (c : seq D) (root : D) : seq D :=
  rot (index root c) c.

Definition cycle_label (c : seq D) (root : D) (i : nat) : D :=
  nth root (rooted_cycle c root) i.

Lemma rooted_cycle_size c root :
  size (rooted_cycle c root) = size c.
Proof. by rewrite /rooted_cycle size_rot. Qed.

Lemma rooted_cycle_uniq c root :
  uniq c -> uniq (rooted_cycle c root).
Proof. by rewrite /rooted_cycle rot_uniq. Qed.

Lemma rooted_cycle_root c root :
  root \in c -> cycle_label c root 0 = root.
Proof.
move=> rc.
by rewrite /cycle_label /rooted_cycle (rot_index rc).
Qed.

Lemma cycle_label_mem c root i :
  i < size c -> cycle_label c root i \in c.
Proof.
move=> ilt.
have h : cycle_label c root i \in rooted_cycle c root.
  rewrite /cycle_label mem_nth // rooted_cycle_size.
  exact ilt.
move: h.
by rewrite /rooted_cycle mem_rot.
Qed.

Lemma rooted_cycle_coverage c root z :
  z \in c -> exists2 i, i < size c & cycle_label c root i = z.
Proof.
move=> zc.
have zr : z \in rooted_cycle c root
  by move: zc; rewrite /rooted_cycle mem_rot.
case/(nthP root): zr => i ilt zi.
exists i.
- move: ilt; by rewrite rooted_cycle_size.
- by rewrite /cycle_label zi.
Qed.

Lemma cycle_label_inj c root i j :
  uniq c -> i < size c -> j < size c ->
  cycle_label c root i = cycle_label c root j -> i = j.
Proof.
move=> uc ilt jlt eqij.
apply/eqP.
have eqb : cycle_label c root i == cycle_label c root j by exact/eqP.
move: eqb.
rewrite /cycle_label nth_uniq ?rooted_cycle_uniq ?rooted_cycle_size //.
Qed.

Lemma cycle_label_successor c root n i :
  uniq c -> root \in c -> size c = n -> 0 < n -> i < n ->
  cycle_label c root (cycle_successor n i) =
    next c (cycle_label c root i).
Proof.
move=> uc rootc sizec npos ilt.
rewrite -(next_rot (index root c) uc (cycle_label c root i)).
rewrite /cycle_label /rooted_cycle next_nth mem_nth ?size_rot ?sizec //.
case rcE : (rot (index root c) c) => [|y q].
- have rsize : size (rot (index root c) c) = n.
    by rewrite size_rot sizec.
  exfalso.
  move: npos.
  by rewrite -rsize rcE.
- have sizeq : size (y :: q) = n.
    by rewrite -rcE size_rot sizec.
  have uyq : uniq (y :: q).
    by rewrite -rcE rot_uniq.
  have idx : index (nth root (y :: q) i) (y :: q) = i
    by apply: index_uniq uyq; rewrite sizeq.
  rewrite idx.
  case hnext : (i.+1 < n).
  + have hp : Peano.lt (i + 1)%coq_nat n by
      move/ltP: hnext; rewrite PeanoNat.Nat.add_1_r.
    rewrite /cycle_successor (PeanoNat.Nat.mod_small _ _ hp)
            PeanoNat.Nat.add_1_r /=.
    have iq : i < size q.
      move: hnext.
      by rewrite -sizeq /= ltnS.
    exact: set_nth_default iq.
  + have ie : i.+1 = n by lia.
    have nNZ : n <> 0 by lia.
    have coqie : (i + 1)%coq_nat = n by lia.
    rewrite /cycle_successor coqie
            (PeanoNat.Nat.Private_NDivProp.mod_same n nNZ) /=.
    have qi : size q <= i.
      apply/leP.
      change (S (size q) = n) in sizeq.
      by lia.
    by rewrite nth_default.
Qed.

Lemma cycle_label_predecessor c root n i :
  uniq c -> root \in c -> size c = n -> 0 < n -> i < n ->
  cycle_label c root (cycle_predecessor n i) =
    prev c (cycle_label c root i).
Proof.
move=> uc rootc sizec npos ilt.
have nNZ : n <> 0 by lia.
have predlt : cycle_predecessor n i < n.
  apply/ltP.
  rewrite /cycle_predecessor.
  exact: PeanoNat.Nat.mod_upper_bound _ _ nNZ.
have succpred : cycle_successor n (cycle_predecessor n i) = i.
  case: i ilt predlt => [|j] ilt predlt.
  - rewrite /cycle_predecessor /cycle_successor.
    cbn.
    have nsub : Peano.lt (n - 1)%coq_nat n by lia.
    rewrite (PeanoNat.Nat.mod_small _ _ nsub).
    have -> : (n - 1 + 1)%coq_nat = n by lia.
    exact: PeanoNat.Nat.Private_NDivProp.mod_same n nNZ.
  - rewrite /cycle_predecessor /cycle_successor.
    cbn.
    have jlt : Peano.lt j n by lia.
    have sjlt : Peano.lt (j + 1)%coq_nat n by lia.
    rewrite PeanoNat.Nat.sub_0_r.
    replace (j + n)%coq_nat with (j + 1 * n)%coq_nat by lia.
    rewrite (PeanoNat.Nat.Private_NDivProp.mod_add j 1 n nNZ)
            (PeanoNat.Nat.mod_small _ _ jlt)
            (PeanoNat.Nat.mod_small _ _ sjlt)
            PeanoNat.Nat.add_1_r.
    by [].
have hs := cycle_label_successor uc rootc sizec npos predlt.
rewrite succpred in hs.
by rewrite hs prev_next.
Qed.

Lemma cycle_labels_vertex_list c root n :
  size c = n ->
  map (cycle_label c root) (vertex_list n) = rooted_cycle c root.
Proof.
move=> sizec.
rewrite /vertex_list /cycle_label.
rewrite (map_nth_iota0 root).
- by rewrite -sizec -(rooted_cycle_size c root) take_size.
- by rewrite rooted_cycle_size sizec.
Qed.

End Labels.

(** Executable structural predicate for a numeric Hamilton ordering. *)
Definition numeric_hamilton_pathb (n endpoint : nat) (path : seq nat) : bool :=
  [&& size path == n, uniq path, all (fun i => i < n) path
    & last 0 path == endpoint].

Definition numeric_hamilton_path (n endpoint : nat) (path : seq nat) : Prop :=
  [/\ size path = n, uniq path, all (fun i => i < n) path
    & last 0 path = endpoint].

Lemma numeric_hamilton_pathP n endpoint path :
  reflect (numeric_hamilton_path n endpoint path)
          (numeric_hamilton_pathb n endpoint path).
Proof.
rewrite /numeric_hamilton_pathb /numeric_hamilton_path.
apply: (iffP and4P).
- move=> [/eqP sz up ap /eqP lp].
  by split.
- move=> [sz up ap lp].
  by rewrite sz eqxx up ap lp eqxx.
Qed.

Lemma numeric_hamilton_path_mem n endpoint path i :
  numeric_hamilton_path n endpoint path -> i < n -> i \in path.
Proof.
move=> [sizep up allp _] ilt.
have psub : {subset path <= vertex_list n}.
  move=> j jp.
  rewrite /vertex_list mem_iota add0n.
  exact: (allP allp j jp).
have vsize : size (vertex_list n) <= size path.
  by rewrite /vertex_list size_iota sizep.
have [_ same] := uniq_min_size up psub vsize.
have iv : i \in vertex_list n
  by rewrite /vertex_list mem_iota add0n ilt.
by rewrite same iv.
Qed.

Lemma numeric_hamilton_path_start_lt n endpoint u tail :
  numeric_hamilton_path n endpoint (u :: tail) -> u < n.
Proof.
move=> [_ _ /andP[ult _] _].
exact ult.
Qed.

Lemma cycle_successor_lt n i :
  0 < n -> cycle_successor n i < n.
Proof.
move=> npos.
apply/ltP.
rewrite /cycle_successor.
apply: PeanoNat.Nat.mod_upper_bound.
lia.
Qed.

Lemma cycle_predecessor_lt n i :
  0 < n -> cycle_predecessor n i < n.
Proof.
move=> npos.
apply/ltP.
rewrite /cycle_predecessor.
apply: PeanoNat.Nat.mod_upper_bound.
lia.
Qed.

Lemma numeric_hamilton_path_successor_mem n endpoint path i :
  0 < n -> numeric_hamilton_path n endpoint path ->
  cycle_successor n i \in path.
Proof.
move=> npos hp.
exact: (numeric_hamilton_path_mem hp (cycle_successor_lt i npos)).
Qed.

Lemma numeric_hamilton_path_predecessor_mem n endpoint path i :
  0 < n -> numeric_hamilton_path n endpoint path ->
  cycle_predecessor n i \in path.
Proof.
move=> npos hp.
exact: (numeric_hamilton_path_mem hp (cycle_predecessor_lt i npos)).
Qed.

Lemma two_chord_paths9_numeric endpoint : endpoint < 9 ->
  all (numeric_hamilton_pathb 9 endpoint) (two_chord_paths 9 endpoint).
Proof.
move=> hlt.
do 9 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Lemma two_chord_paths10_numeric endpoint : endpoint < 10 ->
  all (numeric_hamilton_pathb 10 endpoint) (two_chord_paths 10 endpoint).
Proof.
move=> hlt.
do 10 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Lemma two_chord_paths11_numeric endpoint : endpoint < 11 ->
  all (numeric_hamilton_pathb 11 endpoint) (two_chord_paths 11 endpoint).
Proof.
move=> hlt.
do 11 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Lemma three_chord_paths11_numeric endpoint : endpoint < 11 ->
  all (numeric_hamilton_pathb 11 endpoint) (three_chord_paths endpoint).
Proof.
move=> hlt.
do 11 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Section Bridge.
Variable D : diGraphType.

Definition labelled_numeric_path (c : seq D) (root : D)
    (path : seq nat) : seq D :=
  map (cycle_label c root) path.

Definition path_chords_realized (c : seq D) (root : D) (n : nat)
    (path : seq nat) : Prop :=
  forall u v, u < n -> v < n ->
    u != v ->
    arc_var n u v \in path_chord_vars n path ->
    cycle_label c root u --> cycle_label c root v.

Lemma concrete_valuation_path_chords_realized_mem n c root path
    set_bits mark_bits :
  2 <= n ->
  (forall x, x \in path_chord_vars n path ->
    concrete_valuation n
      (fun u v => cycle_label c root u --> cycle_label c root v)
      set_bits mark_bits x = true) ->
  path_chords_realized c root n path.
Proof.
move=> /leP n2 htrue u v /ltP ult /ltP vlt uvneq hmem.
have uvP : u <> v.
  move=> uv; subst v.
  by move: uvneq; rewrite eqxx.
have hv := htrue (arc_var n u v) hmem.
rewrite (concrete_valuation_arc n
          (fun a b => cycle_label c root a --> cycle_label c root b)
          set_bits mark_bits u v n2 ult vlt uvP) in hv.
exact hv.
Qed.

Lemma concrete_valuation_path_chords_realized n c root path
    set_bits mark_bits :
  2 <= n ->
  (forall x, List.In x (path_chord_vars n path) ->
    concrete_valuation n
      (fun u v => cycle_label c root u --> cycle_label c root v)
      set_bits mark_bits x = true) ->
  path_chords_realized c root n path.
Proof.
move=> n2 htrue.
have mem_ListIn : forall (s : seq nat) x, x \in s -> List.In x s.
  elim=> [|a s IH] x /=.
  - by [].
  - move/orP=> [/eqP -> | hx].
    + by left.
    + right; exact: IH x hx.
apply: (@concrete_valuation_path_chords_realized_mem
          n c root path set_bits mark_bits n2).
move=> x hx.
apply: htrue.
exact: mem_ListIn _ _ hx.
Qed.

Lemma labelled_numeric_path_is_path n c root u tail :
  0 < n -> dicycle c -> size c = n -> root \in c ->
  all (fun i => i < n) (u :: tail) ->
  uniq (u :: tail) ->
  path_chords_realized c root n (u :: tail) ->
  path arc (cycle_label c root u)
       (map (cycle_label c root) tail).
Proof.
move=> npos dc sizec rootc.
have uc : uniq c by case/and3P: dc.
elim: tail u => [|v t IH] u /=.
- by move=> _ _ _.
- move=> /and3P[ult vlt allt] uniqp chords.
  have uNvt : u \notin v :: t := (andP uniqp).1.
  have uniqvt : uniq (v :: t) := (andP uniqp).2.
  have uvneq : u != v.
    apply/negP=> /eqP uv.
    subst v.
    by move: uNvt; rewrite mem_head.
  have tail_chords : path_chords_realized c root n (v :: t).
    move=> a b alt blt abneq hab.
    apply: (chords a b alt blt abneq).
    rewrite /=.
    case hsucc: (PeanoNat.Nat.eqb v (cycle_successor n u)).
    + exact hab.
    + by rewrite inE hab orbT.
  apply/andP; split.
  + case hs: (PeanoNat.Nat.eqb v (cycle_successor n u)).
    * apply PeanoNat.Nat.eqb_eq in hs.
      rewrite hs cycle_label_successor //.
      apply: (@dicycle_next D c (cycle_label c root u) dc).
      by apply: cycle_label_mem; rewrite sizec.
    * apply: (chords u v ult vlt uvneq).
      by rewrite /= hs inE eqxx.
  + apply: IH.
    * by rewrite /= vlt allt.
    * exact uniqvt.
    * exact tail_chords.
Qed.

Lemma labelled_numeric_path_uniq n c root path :
  uniq c -> size c = n -> all (fun i => i < n) path -> uniq path ->
  uniq (labelled_numeric_path c root path).
Proof.
move=> uc sizec allp up.
have linj : {in path &, injective (cycle_label c root)}.
  move=> i j ip jp eqij.
  apply: cycle_label_inj uc _ _ eqij.
  - rewrite sizec; exact: (allP allp i ip).
  - rewrite sizec; exact: (allP allp j jp).
by rewrite /labelled_numeric_path (map_inj_in_uniq linj) up.
Qed.

Lemma numeric_hamilton_path_bridge n endpoint c root path :
  0 < n -> dicycle c -> size c = n -> root \in c ->
  numeric_hamilton_path n endpoint path ->
  path_chords_realized c root n path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> npos dc sizec rootc [sizep up allp lastp] chords.
have uc : uniq c by case/and3P: dc.
case: path sizep up allp lastp chords => [|u t] /=.
- move=> sizep; exfalso; lia.
- move=> sizep up allp lastp chords.
  have lup : uniq (labelled_numeric_path c root (u :: t)).
    exact: (@labelled_numeric_path_uniq n c root (u :: t)
              uc sizec allp up).
  exists (cycle_label c root u), (map (cycle_label c root) t).
  split.
  + by [].
  + apply/andP; split.
    * exact: (@labelled_numeric_path_is_path n c root u t
                npos dc sizec rootc allp up chords).
    * exact lup.
  + change ([set z in labelled_numeric_path c root (u :: t)] =
              [set z in c]).
    have msub :
        [set z in labelled_numeric_path c root (u :: t)]
          \subset [set z in c].
      apply/subsetP=> z.
      rewrite !inE /labelled_numeric_path.
      move/orP=> [/eqP -> | zt].
      * apply: cycle_label_mem.
        rewrite sizec.
        by case/andP: allp.
      * move/mapP: zt => [i it ->].
        apply: cycle_label_mem.
        rewrite sizec.
        exact: (allP (andP allp).2 i it).
    apply/eqP.
    rewrite eqEcard msub andTb (dicycle_set_card dc)
            cardsE (card_uniqP lup).
    rewrite /labelled_numeric_path size_map sizec /= sizep.
    by [].
  + by rewrite last_map lastp.
Qed.

Theorem two_chord_path9_hamilton endpoint c root path :
  dicycle c -> size c = 9 -> root \in c -> endpoint < 9 ->
  path \in two_chord_paths 9 endpoint ->
  path_chords_realized c root 9 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 9 endpoint path.
  exact: (allP (two_chord_paths9_numeric endlt) path pin).
have hp : numeric_hamilton_path 9 endpoint path :=
  elimT (@numeric_hamilton_pathP 9 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge 9 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

Theorem two_chord_path10_hamilton endpoint c root path :
  dicycle c -> size c = 10 -> root \in c -> endpoint < 10 ->
  path \in two_chord_paths 10 endpoint ->
  path_chords_realized c root 10 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 10 endpoint path.
  exact: (allP (two_chord_paths10_numeric endlt) path pin).
have hp : numeric_hamilton_path 10 endpoint path :=
  elimT (@numeric_hamilton_pathP 10 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge 10 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

Theorem two_chord_path11_hamilton endpoint c root path :
  dicycle c -> size c = 11 -> root \in c -> endpoint < 11 ->
  path \in two_chord_paths 11 endpoint ->
  path_chords_realized c root 11 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 11 endpoint path.
  exact: (allP (two_chord_paths11_numeric endlt) path pin).
have hp : numeric_hamilton_path 11 endpoint path :=
  elimT (@numeric_hamilton_pathP 11 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge 11 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

Theorem three_chord_path11_hamilton endpoint c root path :
  dicycle c -> size c = 11 -> root \in c -> endpoint < 11 ->
  path \in three_chord_paths endpoint ->
  path_chords_realized c root 11 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 11 endpoint path.
  exact: (allP (three_chord_paths11_numeric endlt) path pin).
have hp : numeric_hamilton_path 11 endpoint path :=
  elimT (@numeric_hamilton_pathP 11 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge 11 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

End Bridge.
