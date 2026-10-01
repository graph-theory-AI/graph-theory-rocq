(** * Cyclic set-pattern normalization for the k=7 certificates

    The hard C12/C13 certificate instances are much smaller after fixing the
    distinguished set.  This file supplies the trusted normalization layer:

    - enumerate Boolean words of a prescribed length and weight;
    - choose one deterministic representative of every translation orbit;
    - reroot a graph cycle so its set-membership word is that representative;
    - append the corresponding unit clauses to an arbitrary CNF.

    Orbit coverage is proved structurally.  Computation is used only to check
    the four small representative-table cardinalities and that their first bit
    is true (the latter preserves the existing [set_var n 0] unit). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import prelude digraph
  ckpath_cnf ckpath_cardinality ckpath_cert_base
  ckpath_cert_clause_tools ckpath_graph_count
  ckpath_rotation_paths ckpath_cert_graph_common.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Deterministic representatives of cyclic Boolean words *)

(** Lexicographic comparison in which [true] comes before [false].  For every
    nonzero-weight orbit this makes the chosen representative start with
    [true]. *)
Fixpoint true_first_word_leb (s t : list bool) : bool :=
  match s, t with
  | [], _ => true
  | _ :: _, [] => false
  | b :: s', c :: t' =>
      if Bool.eqb b c then true_first_word_leb s' t' else b
  end.

Definition true_first_word_min (s t : list bool) : list bool :=
  if true_first_word_leb s t then s else t.

Fixpoint word_min_fold (best : list bool) (choices : list (list bool))
    : list bool :=
  match choices with
  | [] => best
  | choice :: choices' =>
      word_min_fold (true_first_word_min best choice) choices'
  end.

Definition cyclic_rotations (s : list bool) : list (list bool) :=
  List.map (fun i => rot i s) (List.seq 0 (List.length s)).

Definition canonical_rotation (s : list bool) : list bool :=
  word_min_fold s (cyclic_rotations s).

Lemma word_min_fold_choice best choices :
  word_min_fold best choices = best \/
  List.In (word_min_fold best choices) choices.
Proof.
revert best.
induction choices as [|choice choices IH]; intro best; simpl.
- now left.
- specialize (IH (true_first_word_min best choice)).
  destruct IH as [Hbest | Hin].
  + unfold true_first_word_min in Hbest |- *.
    destruct (true_first_word_leb best choice).
    * left. exact Hbest.
    * right; left. now symmetry.
  + right; now right.
Qed.

Lemma word_in_cyclic_rotations s :
  s <> [] -> List.In s (cyclic_rotations s).
Proof.
intro snil.
unfold cyclic_rotations.
apply List.in_map_iff.
exists 0%coq_nat; split.
- exact (rot0 s).
- apply List.in_seq.
  destruct s; simpl in *; [contradiction | lia].
Qed.

Lemma canonical_rotation_in s :
  s <> [] -> List.In (canonical_rotation s) (cyclic_rotations s).
Proof.
intro snil.
unfold canonical_rotation.
destruct (word_min_fold_choice s (cyclic_rotations s)) as [-> | Hin].
- exact (word_in_cyclic_rotations snil).
- exact Hin.
Qed.

Lemma canonical_rotation_witness s :
  s <> [] ->
  exists i,
    (i < List.length s)%coq_nat /\ canonical_rotation s = rot i s.
Proof.
intro snil.
pose proof (canonical_rotation_in snil) as Hin.
unfold cyclic_rotations in Hin.
apply List.in_map_iff in Hin.
destruct Hin as [i [Hi Hin]].
apply List.in_seq in Hin.
exists i; split; [lia | now symmetry].
Qed.

Lemma bit_vectors_complete (s : list bool) :
  List.In s (bit_vectors (List.length s)).
Proof.
induction s as [|b s IH]; simpl.
- now left.
- apply List.in_or_app.
  destruct b.
  + right; now apply List.in_map.
  + left; now apply List.in_map.
Qed.

Definition fixed_weight_words (n k : nat) : list (list bool) :=
  List.filter (fun s => Nat.eqb (count_true_bits s) k) (bit_vectors n).

Lemma fixed_weight_words_complete n k s :
  List.length s = n -> count_true_bits s = k ->
  List.In s (fixed_weight_words n k).
Proof.
intros Hsize Hweight.
unfold fixed_weight_words.
apply List.filter_In; split.
- rewrite <- Hsize. exact (bit_vectors_complete s).
- now apply Nat.eqb_eq.
Qed.

Fixpoint bool_word_eqb (s t : list bool) : bool :=
  match s, t with
  | [], [] => true
  | b :: s', c :: t' => Bool.eqb b c && bool_word_eqb s' t'
  | _, _ => false
  end.

Lemma bool_word_eqb_eq s t : bool_word_eqb s t = true -> s = t.
Proof.
revert t.
induction s as [|b s IH]; intros [|c t] Heq; try discriminate.
- reflexivity.
- simpl in Heq.
  destruct b, c; simpl in Heq; try discriminate.
  + f_equal. exact (IH t Heq).
  + f_equal. exact (IH t Heq).
Qed.

Definition word_mem (s : list bool) (words : list (list bool)) : bool :=
  List.existsb (bool_word_eqb s) words.

Lemma word_mem_sound s words :
  word_mem s words = true -> List.In s words.
Proof.
unfold word_mem.
rewrite List.existsb_exists.
move=> [t [Hin Heq]].
have -> : s = t := bool_word_eqb_eq Heq.
exact Hin.
Qed.

(** Accumulator-based duplicate removal.  Its membership tests are against
    the already discovered representatives (at most 99 in the instances
    below), rather than against the whole remaining list of 8192 words. *)
Fixpoint collect_new_words
    (acc words : list (list bool)) : list (list bool) :=
  match words with
  | [] => acc
  | word :: words' =>
      if word_mem word acc then collect_new_words acc words'
      else collect_new_words (word :: acc) words'
  end.

Lemma collect_new_words_covers acc words s :
  List.In s acc \/ List.In s words ->
  List.In s (collect_new_words acc words).
Proof.
revert acc.
induction words as [|word words IH]; intros acc Hin; simpl in *.
- destruct Hin as [Hin | []]. exact Hin.
- destruct (word_mem word acc) eqn:Hmem.
  + apply IH.
    destruct Hin as [Hin | [<- | Hin]].
    * now left.
    * left. exact (word_mem_sound Hmem).
    * now right.
  + apply IH.
    destruct Hin as [Hin | [<- | Hin]].
    * left; now right.
    * left; now left.
    * now right.
Qed.

Definition orbit_representatives (n k : nat) : list (list bool) :=
  collect_new_words []
    (List.map canonical_rotation (fixed_weight_words n k)).

Lemma canonical_rotation_is_representative n k s :
  List.length s = n -> count_true_bits s = k ->
  List.In (canonical_rotation s) (orbit_representatives n k).
Proof.
intros Hsize Hweight.
unfold orbit_representatives.
apply collect_new_words_covers; right.
apply List.in_map_iff.
exists s; split; [reflexivity |].
exact (fixed_weight_words_complete Hsize Hweight).
Qed.

Definition representatives_rootedb (n k : nat) : bool :=
  List.forallb (fun s => List.hd false s) (orbit_representatives n k).

Lemma representatives_rootedb_sound n k s :
  representatives_rootedb n k = true ->
  List.In s (orbit_representatives n k) -> List.hd false s = true.
Proof.
intros Hrooted Hin.
unfold representatives_rootedb in Hrooted.
apply (proj1 (List.forallb_forall _ _) Hrooted s Hin).
Qed.

(** These are the binary-necklace counts
    [C(12,7)/12], [C(13,3)/13], [C(13,4)/13], [C(13,5)/13].  Pairing each
    count with its first-bit check avoids evaluating the same table twice. *)
Lemma k7_orbit_representatives_12_7_checked :
  List.length (orbit_representatives 12 7) = 66 /\
  representatives_rootedb 12 7 = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma k7_orbit_representatives_13_3_checked :
  List.length (orbit_representatives 13 3) = 22 /\
  representatives_rootedb 13 3 = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma k7_orbit_representatives_13_4_checked :
  List.length (orbit_representatives 13 4) = 55 /\
  representatives_rootedb 13 4 = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma k7_orbit_representatives_13_5_checked :
  List.length (orbit_representatives 13 5) = 99 /\
  representatives_rootedb 13 5 = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma k7_orbit_representatives_12_7_count :
  List.length (orbit_representatives 12 7) = 66.
Proof. exact (proj1 k7_orbit_representatives_12_7_checked). Qed.

Lemma k7_orbit_representatives_13_3_count :
  List.length (orbit_representatives 13 3) = 22.
Proof. exact (proj1 k7_orbit_representatives_13_3_checked). Qed.

Lemma k7_orbit_representatives_13_4_count :
  List.length (orbit_representatives 13 4) = 55.
Proof. exact (proj1 k7_orbit_representatives_13_4_checked). Qed.

Lemma k7_orbit_representatives_13_5_count :
  List.length (orbit_representatives 13 5) = 99.
Proof. exact (proj1 k7_orbit_representatives_13_5_checked). Qed.

Lemma k7_orbit_representatives_12_7_rooted :
  representatives_rootedb 12 7 = true.
Proof. exact (proj2 k7_orbit_representatives_12_7_checked). Qed.

Lemma k7_orbit_representatives_13_3_rooted :
  representatives_rootedb 13 3 = true.
Proof. exact (proj2 k7_orbit_representatives_13_3_checked). Qed.

Lemma k7_orbit_representatives_13_4_rooted :
  representatives_rootedb 13 4 = true.
Proof. exact (proj2 k7_orbit_representatives_13_4_checked). Qed.

Lemma k7_orbit_representatives_13_5_rooted :
  representatives_rootedb 13 5 = true.
Proof. exact (proj2 k7_orbit_representatives_13_5_checked). Qed.

(** ** Rerooting a graph cycle to a representative *)

Section CycleSetMasks.
Variable D : diGraphType.

Definition unrooted_set_mask (c : seq.seq D) (A : {set D}) : list bool :=
  seq.map (fun z => z \in A) c.

Definition cycle_set_mask
    (c : seq.seq D) (root : D) (n : nat) (A : {set D}) : list bool :=
  seq.map (fun i => cycle_label c root i \in A) (vertex_list n).

Lemma cycle_set_maskE (c : seq.seq D) (root : D) n (A : {set D}) :
  size c = n ->
  cycle_set_mask c root n A =
    seq.map (fun z => z \in A) (rooted_cycle c root).
Proof.
move=> Hsize.
rewrite /cycle_set_mask -(cycle_labels_vertex_list root Hsize).
by rewrite -map_comp /comp.
Qed.

Lemma rooted_cycle_nth (c : seq.seq D) (default : D) i :
  uniq c -> i < size c ->
  rooted_cycle c (seq.nth default c i) = rot i c.
Proof.
move=> Huniq Hlt.
have Hindex : index (seq.nth default c i) c = i.
  by apply: index_uniq Huniq.
by rewrite /rooted_cycle Hindex.
Qed.

Lemma unrooted_set_mask_weight (c : seq.seq D) (A : {set D}) :
  uniq c -> A \subset [set z in c] ->
  count_true_bits (unrooted_set_mask c A) = #|A|.
Proof.
move=> Huniq Hsub.
rewrite /unrooted_set_mask.
rewrite (@count_true_bits_pred_card D (fun z : D => z \in A) c Huniq).
apply: eq_card => x.
rewrite !inE.
case xA: (x \in A); last by rewrite andbF.
have xc := subsetP Hsub x xA.
rewrite inE in xc.
by rewrite xc.
Qed.

Lemma cycle_set_mask_head
    (c : seq.seq D) (root : D) n (A : {set D}) :
  (0 < n)%coq_nat -> root \in c ->
  List.hd false (cycle_set_mask c root n A) = (root \in A).
Proof.
intros Hnpos Hroot.
destruct n as [|n]; [lia |].
unfold cycle_set_mask, vertex_list.
simpl.
by rewrite (rooted_cycle_root Hroot).
Qed.

Theorem choose_cycle_set_orbit_root
    (c : seq.seq D) (A : {set D}) n k :
  uniq c -> size c = n -> A \subset [set z in c] -> #|A| = k ->
  (0 < k)%coq_nat -> representatives_rootedb n k = true ->
  exists root,
    root \in c /\ root \in A /\
    List.In (cycle_set_mask c root n A) (orbit_representatives n k) /\
    cycle_set_mask c root n A =
      canonical_rotation (unrooted_set_mask c A).
Proof.
move=> Huniq Hsize Hsub Hcard Hkpos Hrooted.
set s := unrooted_set_mask c A.
have ssize : List.length s = n.
  by rewrite /s /unrooted_set_mask List.length_map -Hsize.
have sweight : count_true_bits s = k.
  by rewrite /s (unrooted_set_mask_weight Huniq Hsub) Hcard.
have snil : s <> [].
  move=> snil; rewrite snil /= in sweight; lia.
have [i [Hilt Hcanonical]] := canonical_rotation_witness snil.
have Hiltc : i < size c.
  apply/ltP. rewrite Hsize. lia.
have An0 : A != set0.
  rewrite -card_gt0 Hcard.
  apply/ltP.
  exact Hkpos.
move/set0Pn: An0 => [default Hdefault].
set root := seq.nth default c i.
have Hrootc : root \in c.
  rewrite /root.
  exact: mem_nth Hiltc.
have Hreroot : rooted_cycle c root = rot i c.
  rewrite /root.
  exact: rooted_cycle_nth Huniq Hiltc.
have Hmask : cycle_set_mask c root n A = canonical_rotation s.
  rewrite (@cycle_set_maskE c root n A Hsize).
  rewrite Hreroot.
  rewrite map_rot.
  by rewrite /s /unrooted_set_mask -Hcanonical.
have Hrep : List.In (canonical_rotation s) (orbit_representatives n k).
  exact: canonical_rotation_is_representative ssize sweight.
have Hhead : List.hd false (canonical_rotation s) = true.
  exact: representatives_rootedb_sound Hrooted Hrep.
have Hnpos : (0 < n)%coq_nat by lia.
have HrootA : root \in A.
  have Hheadroot :
      List.hd false (cycle_set_mask c root n A) = (root \in A).
    apply: cycle_set_mask_head.
    - exact Hnpos.
    - exact Hrootc.
  rewrite Hmask Hhead in Hheadroot.
  move: Hheadroot.
  by case: (root \in A).
exists root; repeat split.
- exact Hrootc.
- exact HrootA.
- by rewrite Hmask.
- exact Hmask.
Qed.

End CycleSetMasks.

(** ** Fixed-set unit clauses *)

Fixpoint fixed_set_units_from
    (n start : nat) (mask : list bool) : cnf :=
  match mask with
  | [] => []
  | b :: mask' =>
      [(set_var n start, b)] :: fixed_set_units_from n (S start) mask'
  end.

Definition fixed_set_units (n : nat) (mask : list bool) : cnf :=
  fixed_set_units_from n 0 mask.

Definition fixed_set_instance
    (base : cnf) (n : nat) (mask : list bool) : cnf :=
  base ++ fixed_set_units n mask.

Lemma fixed_set_units_from_bits_satisfied rho n start len bits :
  (forall i,
      (start <= i < start + len)%coq_nat ->
      rho (set_var n i) = bits i) ->
  satisfies_cnf rho
    (fixed_set_units_from n start
      (List.map bits (List.seq start len))).
Proof.
revert start.
induction len as [| len IH].
- intros start Hlookup.
  reflexivity.
- intros start Hlookup.
  simpl.
  unfold satisfies_cnf, eval_cnf in *.
  simpl.
  unfold eval_clause, eval_literal.
  simpl.
  pose proof (Hlookup start) as Hstart.
  assert (Hbounds : (start <= start < start + S len)%coq_nat).
  { lia. }
  specialize (Hstart Hbounds).
  rewrite Hstart.
  destruct (bits start).
  * simpl.
    apply IH.
    intros i Hi.
    apply Hlookup.
    lia.
  * simpl.
    apply IH.
    intros i Hi.
    apply Hlookup.
    lia.
Qed.

Lemma fixed_set_instance_satisfied rho base n mask :
  satisfies_cnf rho base ->
  satisfies_cnf rho (fixed_set_units n mask) ->
  satisfies_cnf rho (fixed_set_instance base n mask).
Proof.
move=> Hbase Hunits.
rewrite /fixed_set_instance satisfies_cnf_app.
by split.
Qed.

Section CycleFixedUnits.
Variable D : diGraphType.

Lemma cycle_graph_valuation_fixed_set_units
    c root n (A : {set D}) mark_bits :
  satisfies_cnf
    (cycle_graph_valuation c root n
      (fun i => cycle_label c root i \in A) mark_bits)
    (fixed_set_units n (cycle_set_mask c root n A)).
Proof.
unfold fixed_set_units, cycle_set_mask, vertex_list.
apply fixed_set_units_from_bits_satisfied.
intros i Hi.
apply cycle_graph_valuation_set.
lia.
Qed.

Lemma cycle_graph_valuation_fixed_set_instance
    c root n (A : {set D}) mark_bits base :
  satisfies_cnf
    (cycle_graph_valuation c root n
      (fun i => cycle_label c root i \in A) mark_bits) base ->
  satisfies_cnf
    (cycle_graph_valuation c root n
      (fun i => cycle_label c root i \in A) mark_bits)
    (fixed_set_instance base n (cycle_set_mask c root n A)).
Proof.
move=> Hbase.
apply fixed_set_instance_satisfied; [exact Hbase |].
exact: cycle_graph_valuation_fixed_set_units.
Qed.

End CycleFixedUnits.
