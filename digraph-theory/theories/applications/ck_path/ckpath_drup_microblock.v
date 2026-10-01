(** * Bounded-memory semantic interfaces for hinted-RUP microblocks

    A microblock is replayed against a fresh dense database containing only
    the global-base clauses and earlier consequences named by its hints.  Its
    exported theorem mentions only the clauses derived by that microblock: no
    computed clause database has to survive as a transparent constant. *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_drup ckpath_cert_base.
Import ListNotations.

(** The clauses added by a trace, in trace order.  Deletion steps export
    nothing. *)
Fixpoint added_clauses (trace : list drup_step) : cnf :=
  match trace with
  | [] => []
  | Delete _ :: trace' => added_clauses trace'
  | RupAdd c _ :: trace' => c :: added_clauses trace'
  end.

(** Unlike [check_drup_chunk_sound], this theorem deliberately does not expose
    [add_drup_steps db trace].  The database used by the computation can
    therefore remain transient. *)
Theorem check_drup_chunk_outputs_sound
    (db : clause_database) (trace : list drup_step) :
  check_drup_chunk db trace = true ->
  forall rho,
    satisfies_database rho db ->
    satisfies_cnf rho (added_clauses trace).
Proof.
revert db.
induction trace as [|step trace IH]; intros db Hcheck rho Hdb.
- reflexivity.
- destruct step as [c hints | ids].
  + simpl in Hcheck |- *.
    destruct (rup_hints db c hints) eqn:Hrup; try discriminate.
    apply andb_true_iff; split.
    * eapply rup_hints_sound; eauto.
    * apply (IH (database_add db c) Hcheck rho).
      apply satisfies_database_add; [exact Hdb |].
      eapply rup_hints_sound; eauto.
  + simpl in Hcheck |- *.
    eapply IH; eauto.
Qed.

Definition check_microblock
    (input : cnf) (trace : list drup_step) : bool :=
  check_drup_chunk (initial_database input) trace.

Theorem check_microblock_sound (input : cnf) (trace : list drup_step) :
  check_microblock input trace = true ->
  forall rho,
    satisfies_cnf rho input ->
    satisfies_cnf rho (added_clauses trace).
Proof.
intros Hcheck rho Hinput.
apply (check_drup_chunk_outputs_sound
         (initial_database input) trace Hcheck rho).
exact (initial_database_sound rho input Hinput).
Qed.

(** ** Selecting a dense local database *)

Definition select_cnf (f : cnf) (ids : list nat) : cnf :=
  map (fun i => nth i f []) ids.

Definition indices_in_bounds (f : cnf) (ids : list nat) : bool :=
  let bound := length f in
  forallb (fun i => i <? bound) ids.

Lemma nth_in_bounds {A : Type} (xs : list A) (default : A) i :
  i < length xs -> In (nth i xs default) xs.
Proof.
revert i.
induction xs as [|x xs IH]; intros [|i] Hlt; simpl in *.
- lia.
- lia.
- now left.
- right. apply IH. lia.
Qed.

Lemma indices_in_bounds_sound f ids :
  indices_in_bounds f ids = true ->
  forall i, In i ids -> i < length f.
Proof.
unfold indices_in_bounds.
cbn.
rewrite forallb_forall.
intros Hall i Hi.
apply Nat.ltb_lt.
exact (Hall i Hi).
Qed.

Lemma satisfies_cnf_select rho f ids :
  satisfies_cnf rho f ->
  indices_in_bounds f ids = true ->
  satisfies_cnf rho (select_cnf f ids).
Proof.
intros Hf Hbounds.
unfold satisfies_cnf, eval_cnf, select_cnf.
apply forallb_forall.
intros c Hc.
apply in_map_iff in Hc.
destruct Hc as [i [<- Hi]].
eapply eval_cnf_member; [exact Hf |].
apply nth_in_bounds.
exact (indices_in_bounds_sound f ids Hbounds i Hi).
Qed.

Lemma satisfies_cnf_app_intro rho f g :
  satisfies_cnf rho f ->
  satisfies_cnf rho g ->
  satisfies_cnf rho (f ++ g).
Proof.
unfold satisfies_cnf, eval_cnf.
rewrite forallb_app.
intros -> ->.
reflexivity.
Qed.

Lemma satisfies_cnf_concat_intro rho formulas :
  Forall (satisfies_cnf rho) formulas ->
  satisfies_cnf rho (concat formulas).
Proof.
intro Hall.
induction Hall as [|f formulas Hf Hformulas IH].
- reflexivity.
- simpl. apply satisfies_cnf_app_intro; assumption.
Qed.

Definition selected_input
    (base : cnf) (base_ids : list nat) (imported : cnf) : cnf :=
  select_cnf base base_ids ++ imported.

Lemma selected_input_sound rho base base_ids imported :
  indices_in_bounds base base_ids = true ->
  satisfies_cnf rho base ->
  satisfies_cnf rho imported ->
  satisfies_cnf rho (selected_input base base_ids imported).
Proof.
intros Hbounds Hbase Himported.
apply satisfies_cnf_app_intro.
- exact (satisfies_cnf_select rho base base_ids Hbase Hbounds).
- exact Himported.
Qed.

(** ** An executable output guard

    The explicit output list keeps the exported theorem small.  The Boolean
    equality below makes a mistaken generator output fail inside Rocq. *)

Definition literal_eq_dec (x y : literal) : {x = y} + {x <> y}.
Proof.
destruct x as [xn xb], y as [yn yb].
destruct (Nat.eq_dec xn yn) as [Hn | Hn].
- subst yn. destruct (Bool.bool_dec xb yb) as [Hb | Hb].
  + subst yb. left. reflexivity.
  + right. intro Heq. inversion Heq. contradiction.
- right. intro Heq. inversion Heq. contradiction.
Defined.

Definition clause_eq_dec : forall x y : clause, {x = y} + {x <> y} :=
  list_eq_dec literal_eq_dec.

Definition cnf_eq_dec : forall x y : cnf, {x = y} + {x <> y} :=
  list_eq_dec clause_eq_dec.

Definition cnf_eqb (f g : cnf) : bool :=
  if cnf_eq_dec f g then true else false.

Lemma cnf_eqb_true f g : cnf_eqb f g = true -> f = g.
Proof.
unfold cnf_eqb.
destruct (cnf_eq_dec f g) as [Heq | Hneq].
- exact (fun _ => Heq).
- discriminate.
Qed.

Definition check_microblock_export
    (input : cnf) (records : list (list nat * list nat))
    (output : cnf) : bool :=
  let trace := decode_trace records in
  check_microblock input trace && cnf_eqb (added_clauses trace) output.

Theorem check_microblock_export_sound input records output :
  check_microblock_export input records output = true ->
  forall rho,
    satisfies_cnf rho input ->
    satisfies_cnf rho output.
Proof.
unfold check_microblock_export.
intros Hcheck rho Hinput.
apply andb_true_iff in Hcheck.
destruct Hcheck as [Hrup Houtput].
apply cnf_eqb_true in Houtput.
rewrite <- Houtput.
exact (check_microblock_sound input (decode_trace records) Hrup rho Hinput).
Qed.

Definition check_selected_microblock
    (base : cnf) (base_ids : list nat) (imported : cnf)
    (records : list (list nat * list nat)) (output : cnf) : bool :=
  indices_in_bounds base base_ids &&
  check_microblock_export
    (selected_input base base_ids imported) records output.

Theorem check_selected_microblock_sound
    base base_ids imported records output :
  check_selected_microblock base base_ids imported records output = true ->
  forall rho,
    satisfies_cnf rho base ->
    satisfies_cnf rho imported ->
    satisfies_cnf rho output.
Proof.
unfold check_selected_microblock.
intros Hcheck rho Hbase Himported.
apply andb_true_iff in Hcheck.
destruct Hcheck as [Hbounds Hblock].
apply (check_microblock_export_sound
         (selected_input base base_ids imported) records output
         Hblock rho).
exact (selected_input_sound rho base base_ids imported
         Hbounds Hbase Himported).
Qed.

(** A tiny executable regression: the selected contradictory units derive the
    empty clause without exporting a database checkpoint. *)
Definition microblock_smoke_records : list (list nat * list nat) :=
  [([], [0; 1])].

Example microblock_smoke_checks :
  check_selected_microblock smoke_base [0; 1] []
    microblock_smoke_records [[]] = true.
Proof. vm_compute. reflexivity. Qed.
