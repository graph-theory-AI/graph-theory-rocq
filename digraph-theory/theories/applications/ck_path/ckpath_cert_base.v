(** * Concrete finite CNFs for the k=5 and k=6 endgames

    The variable layout is deliberately arithmetic and stable.

    - variables [1 .. n(n-1)] are arcs [(u,v)], in row-major order with
      diagonal entries omitted;
    - the next [n] variables encode the distinguished vertex set;
    - the final [n] variables encode covered starts (C9/C11) or bad endpoints
      (C10).

    Every instance is rotationally normalized: variable zero of the final
    distinguished nonempty set is asserted.  A graph counterexample is first
    rotated so that a chosen active/bad endpoint has label zero.

    Cardinality constraints use the direct subset encoding emitted by
    [scripts/generate_ckpath_certificates.py].  No auxiliary variables occur. *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality ckpath_drup.
Import ListNotations.

Definition positive_literal (x : nat) : literal := (x, true).
Definition negative_literal (x : nat) : literal := (x, false).

Fixpoint combinations {A : Type} (k : nat) (xs : list A) : list (list A) :=
  match k, xs with
  | 0, _ => [[]]
  | S _, [] => []
  | S k', x :: xs' =>
      map (cons x) (combinations k' xs') ++ combinations (S k') xs'
  end.

Definition at_least_comb
    (guard : clause) (k : nat) (xs : list nat) : cnf :=
  map (fun ys => guard ++ map positive_literal ys)
      (combinations (length xs - k + 1) xs).

Definition at_most_comb
    (guard : clause) (k : nat) (xs : list nat) : cnf :=
  map (fun ys => guard ++ map negative_literal ys)
      (combinations (S k) xs).

Definition exactly_comb
    (guard : clause) (k : nat) (xs : list nat) : cnf :=
  at_least_comb guard k xs ++ at_most_comb guard k xs.

Inductive list_subsequence {A : Type} : list A -> list A -> Prop :=
| subsequence_nil : list_subsequence [] []
| subsequence_keep x ys xs :
    list_subsequence ys xs -> list_subsequence (x :: ys) (x :: xs)
| subsequence_drop x ys xs :
    list_subsequence ys xs -> list_subsequence ys (x :: xs).

Lemma combinations_spec {A : Type} (k : nat) (xs ys : list A) :
  In ys (combinations k xs) ->
  length ys = k /\ list_subsequence ys xs.
Proof.
revert k ys.
induction xs as [|x xs IH]; intros k ys Hin.
- destruct k; simpl in Hin.
  + destruct Hin as [H | H]; [subst ys | contradiction].
    split; [reflexivity | constructor].
  + contradiction.
- destruct k as [|k].
  + simpl in Hin. destruct Hin as [H | H]; [subst ys | contradiction].
    split; [reflexivity | constructor].
    clear IH. induction xs as [|y ys IHy].
    * constructor.
    * apply subsequence_drop. exact IHy.
  + simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    * apply in_map_iff in Hin.
      destruct Hin as [zs [Hys Hzs]]. subst ys.
      specialize (IH k zs Hzs). destruct IH as [Hlen Hsub].
      split; [simpl; now rewrite Hlen | now constructor].
    * specialize (IH (S k) ys Hin). destruct IH as [Hlen Hsub].
      split; [exact Hlen | now constructor].
Qed.

Lemma list_subsequence_length {A : Type} (xs ys : list A) :
  list_subsequence ys xs -> length ys <= length xs.
Proof.
intro Hsub. induction Hsub; simpl; lia.
Qed.

Lemma count_true_subsequence (rho : valuation) (xs ys : list nat) :
  list_subsequence ys xs -> count_true rho ys <= count_true rho xs.
Proof.
intro Hsub.
induction Hsub; unfold count_true in *; simpl in *.
- lia.
- destruct (rho x); simpl; lia.
- destruct (rho x); simpl; lia.
Qed.

Lemma count_true_zero_subsequence (rho : valuation) (xs ys : list nat) :
  list_subsequence ys xs -> count_true rho ys = 0 ->
  count_true rho xs <= length xs - length ys.
Proof.
intro Hsub.
induction Hsub; intro Hzero; unfold count_true in *; simpl in *.
- lia.
- destruct (rho x); simpl in Hzero |- *.
  + discriminate.
  + apply IHHsub. exact Hzero.
- pose proof (list_subsequence_length xs ys Hsub) as Hlen.
  specialize (IHHsub Hzero).
  destruct (rho x); destruct (length ys); simpl in *; lia.
Qed.

Lemma negative_clause_false_count (rho : valuation) (xs : list nat) :
  eval_clause rho (map negative_literal xs) = false ->
  count_true rho xs = length xs.
Proof.
induction xs as [|x xs IH]; intro Hfalse.
- reflexivity.
- unfold eval_clause in Hfalse; simpl in Hfalse.
  unfold count_true; simpl.
  destruct (rho x) eqn:Hx; simpl in Hfalse |- *.
  + f_equal. apply IH.
    unfold negative_literal, eval_literal in Hfalse.
    simpl in Hfalse. rewrite Hx in Hfalse. simpl in Hfalse. exact Hfalse.
  + unfold negative_literal, eval_literal in Hfalse.
    simpl in Hfalse. rewrite Hx in Hfalse. discriminate.
Qed.

Lemma positive_clause_false_count (rho : valuation) (xs : list nat) :
  eval_clause rho (map positive_literal xs) = false ->
  count_true rho xs = 0.
Proof.
induction xs as [|x xs IH]; intro Hfalse.
- reflexivity.
- unfold eval_clause in Hfalse; simpl in Hfalse.
  unfold count_true; simpl.
  destruct (rho x) eqn:Hx; simpl in Hfalse |- *.
  + unfold positive_literal, eval_literal in Hfalse.
    simpl in Hfalse. rewrite Hx in Hfalse. discriminate.
  + apply IH.
    unfold positive_literal, eval_literal in Hfalse.
    simpl in Hfalse. rewrite Hx in Hfalse. simpl in Hfalse. exact Hfalse.
Qed.

Theorem at_most_comb_complete
    (rho : valuation) (guard : clause) (k : nat) (xs : list nat) :
  eval_clause rho guard = true \/ count_true rho xs <= k ->
  eval_cnf rho (at_most_comb guard k xs) = true.
Proof.
intro Hbound.
unfold eval_cnf, at_most_comb.
apply forallb_forall.
intros c Hin.
apply in_map_iff in Hin.
destruct Hin as [ys [Hc Hys]]. subst c.
unfold eval_clause. rewrite existsb_app.
fold (eval_clause rho guard).
fold (eval_clause rho (map negative_literal ys)).
destruct Hbound as [Hguard | Hbound].
- rewrite Hguard. reflexivity.
- destruct (eval_clause rho (map negative_literal ys)) eqn:Hneg.
  + destruct (eval_clause rho guard); reflexivity.
  + exfalso.
    pose proof (combinations_spec (S k) xs ys Hys) as [Hlen Hsub].
    pose proof (negative_clause_false_count rho ys Hneg) as Hcount.
    pose proof (count_true_subsequence rho xs ys Hsub) as Hmono.
    lia.
Qed.

Theorem at_least_comb_complete
    (rho : valuation) (guard : clause) (k : nat) (xs : list nat) :
  k <= length xs ->
  eval_clause rho guard = true \/ k <= count_true rho xs ->
  eval_cnf rho (at_least_comb guard k xs) = true.
Proof.
intros Hk Hbound.
unfold eval_cnf, at_least_comb.
apply forallb_forall.
intros c Hin.
apply in_map_iff in Hin.
destruct Hin as [ys [Hc Hys]]. subst c.
unfold eval_clause. rewrite existsb_app.
fold (eval_clause rho guard).
fold (eval_clause rho (map positive_literal ys)).
destruct Hbound as [Hguard | Hbound].
- rewrite Hguard. reflexivity.
- destruct (eval_clause rho (map positive_literal ys)) eqn:Hpos.
  + destruct (eval_clause rho guard); reflexivity.
  + exfalso.
    pose proof (combinations_spec (length xs - k + 1) xs ys Hys)
      as [Hlen Hsub].
    pose proof (positive_clause_false_count rho ys Hpos) as Hzero.
    pose proof (count_true_zero_subsequence rho xs ys Hsub Hzero) as Hmono.
    pose proof (list_subsequence_length xs ys Hsub) as Hsub_length.
    destruct k as [|k]; simpl in *; lia.
Qed.

Theorem exactly_comb_complete
    (rho : valuation) (guard : clause) (k : nat) (xs : list nat) :
  k <= length xs ->
  eval_clause rho guard = true \/ count_true rho xs = k ->
  eval_cnf rho (exactly_comb guard k xs) = true.
Proof.
intros Hk Hbound.
unfold exactly_comb, eval_cnf.
rewrite forallb_app.
apply andb_true_iff.
split.
- fold (eval_cnf rho (at_least_comb guard k xs)).
  apply at_least_comb_complete; [exact Hk |].
  destruct Hbound as [Hg | Hc]; [now left | right; lia].
- fold (eval_cnf rho (at_most_comb guard k xs)).
  apply at_most_comb_complete.
  destruct Hbound as [Hg | Hc]; [now left | right; lia].
Qed.

(** ** Static variable layout and rotations *)

Definition vertex_list (n : nat) : list nat := seq 0 n.

Definition arc_var (n u v : nat) : nat :=
  1 + u * (n - 1) + (if v <? u then v else v - 1).

Definition set_var (n v : nat) : nat := n * (n - 1) + 1 + v.
Definition mark_var (n v : nat) : nat := n * (n - 1) + n + 1 + v.

Definition cycle_successor (n u : nat) : nat := (u + 1) mod n.
Definition cycle_predecessor (n u : nat) : nat := (u + n - 1) mod n.

Definition internal_row (n u : nat) : list nat :=
  map (arc_var n u)
      (filter
         (fun v =>
            negb ((v =? u) ||
                  (v =? cycle_successor n u) ||
                  (v =? cycle_predecessor n u)))
         (vertex_list n)).

Definition antiparallel_clauses (n : nat) : cnf :=
  flat_map
    (fun u =>
       map (fun v =>
              [negative_literal (arc_var n u v);
               negative_literal (arc_var n v u)])
           (seq (S u) (n - S u)))
    (vertex_list n).

Definition directed_cycle_clauses (n : nat) : cnf :=
  map (fun u =>
         [positive_literal (arc_var n u (cycle_successor n u))])
      (vertex_list n).

Definition cycle_base_clauses (n : nat) : cnf :=
  antiparallel_clauses n ++ directed_cycle_clauses n.

Definition cyclic_order (n endpoint : nat) : list nat :=
  map (fun offset => (endpoint + 1 + offset) mod n) (vertex_list n).

Definition two_chord_rotation
    (n endpoint i j : nat) : list nat :=
  let word := cyclic_order n endpoint in
  firstn (S j - i) (skipn i word) ++
  firstn i word ++ skipn (S j) word.

Definition three_chord_rotation (endpoint cut : nat) : list nat :=
  let word := cyclic_order 11 endpoint in
  firstn (10 - S cut) (skipn (S cut) word) ++
  [nth cut word 0] ++ firstn cut word ++ [nth 10 word 0].

Fixpoint path_chord_vars (n : nat) (path : list nat) : list nat :=
  match path with
  | u :: ((v :: _) as tail) =>
      if v =? cycle_successor n u then path_chord_vars n tail
      else arc_var n u v :: path_chord_vars n tail
  | _ => []
  end.

Definition two_chord_paths (n endpoint : nat) : list (list nat) :=
  flat_map
    (fun i =>
       map (fun j => two_chord_rotation n endpoint i j)
           (seq i (n - 1 - i)))
    (seq 1 (n - 2)).

Definition three_chord_paths (endpoint : nat) : list (list nat) :=
  map (three_chord_rotation endpoint) (seq 1 8).

Definition cover_rotation_clause
    (n endpoint : nat) (path : list nat) : clause :=
  negative_literal (set_var n endpoint) ::
  positive_literal (mark_var n (hd 0 path)) ::
  map negative_literal (path_chord_vars n path).

(** ** C9: three active endpoints cover at least six starts *)

Definition c9_endpoint_clauses (endpoint : nat) : cnf :=
  [[negative_literal (set_var 9 endpoint);
    positive_literal (mark_var 9 (cycle_successor 9 endpoint))]] ++
  exactly_comb [positive_literal (set_var 9 endpoint)] 4
               (internal_row 9 endpoint) ++
  map (cover_rotation_clause 9 endpoint) (two_chord_paths 9 endpoint).

Definition c9_base : cnf :=
  cycle_base_clauses 9 ++
  exactly_comb [] 3 (map (set_var 9) (vertex_list 9)) ++
  at_most_comb [] 5 (map (mark_var 9) (vertex_list 9)) ++
  [[positive_literal (set_var 9 0)]] ++
  flat_map c9_endpoint_clauses (vertex_list 9).

(** ** C10: at most one selected endpoint is rotation-bad *)

Definition c10_rotation_clause
    (endpoint : nat) (path : list nat) : clause :=
  let start := hd 0 path in
  negative_literal (mark_var 10 endpoint) ::
  negative_literal (set_var 10 (cycle_predecessor 10 start)) ::
  map negative_literal (path_chord_vars 10 path).

Definition c10_endpoint_clauses (endpoint : nat) : cnf :=
  exactly_comb [negative_literal (set_var 10 endpoint)] 5
               (internal_row 10 endpoint) ++
  [[negative_literal (mark_var 10 endpoint);
    negative_literal (set_var 10 endpoint)]] ++
  map (c10_rotation_clause endpoint) (two_chord_paths 10 endpoint).

Definition c10_base : cnf :=
  cycle_base_clauses 10 ++
  exactly_comb [] 6 (map (set_var 10) (vertex_list 10)) ++
  [[positive_literal (mark_var 10 0)]] ++
  flat_map c10_endpoint_clauses (vertex_list 10) ++
  at_least_comb [] 2 (map (mark_var 10) (vertex_list 10)).

(** ** C11: three or four active endpoints cover at least six starts *)

Definition c11_endpoint_clauses
    (active_size endpoint : nat) : cnf :=
  [[negative_literal (set_var 11 endpoint);
    positive_literal (mark_var 11 (cycle_successor 11 endpoint))]] ++
  exactly_comb [positive_literal (set_var 11 endpoint)] 5
               (internal_row 11 endpoint) ++
  map (cover_rotation_clause 11 endpoint)
      (two_chord_paths 11 endpoint ++
       if active_size =? 3 then three_chord_paths endpoint else []).

Definition c11_base (active_size : nat) : cnf :=
  cycle_base_clauses 11 ++
  exactly_comb [] active_size (map (set_var 11) (vertex_list 11)) ++
  at_most_comb [] 5 (map (mark_var 11) (vertex_list 11)) ++
  [[positive_literal (set_var 11 0)]] ++
  flat_map (c11_endpoint_clauses active_size) (vertex_list 11).

(** Executable guards on the exact clause ordering expected by certificates. *)
Lemma c9_base_clause_count : length c9_base = 787.
Proof. vm_compute. reflexivity. Qed.

Lemma c10_base_clause_count : length c10_base = 1228.
Proof. vm_compute. reflexivity. Qed.

Lemma c11_m3_base_clause_count : length (c11_base 3) = 2586.
Proof. vm_compute. reflexivity. Qed.

Lemma c11_m4_base_clause_count : length (c11_base 4) = 2740.
Proof. vm_compute. reflexivity. Qed.

(** Decode the compact nonnegative literal representation used in generated
    trace files: [2(v-1)] is negative [v], and [2(v-1)+1] is positive [v]. *)
Definition decode_literal (code : nat) : literal :=
  (code / 2 + 1, Nat.odd code).

Definition decode_clause (codes : list nat) : clause :=
  map decode_literal codes.

Definition decode_addition
    (record : list nat * list nat) : drup_step :=
  RupAdd (decode_clause (fst record)) (snd record).

Definition decode_trace (records : list (list nat * list nat)) : list drup_step :=
  map decode_addition records.

(** ** Bounded incremental replay

    Large traces are split into independently computed chunks.  The checker
    below has exactly the same per-addition condition as [check_drup_from], but
    accepts the end of a chunk instead of demanding the final empty clause.
    [add_drup_steps] computes the stable database handed to the next chunk. *)

Fixpoint add_drup_steps
    (db : clause_database) (trace : list drup_step) : clause_database :=
  match trace with
  | [] => db
  | Delete _ :: trace' => add_drup_steps db trace'
  | RupAdd c _ :: trace' => add_drup_steps (database_add db c) trace'
  end.

Fixpoint check_drup_chunk
    (db : clause_database) (trace : list drup_step) : bool :=
  match trace with
  | [] => true
  | Delete _ :: trace' => check_drup_chunk db trace'
  | RupAdd c hints :: trace' =>
      if rup_hints db c hints
      then check_drup_chunk (database_add db c) trace'
      else false
  end.

Theorem check_drup_chunk_sound (db : clause_database) (trace : list drup_step) :
  check_drup_chunk db trace = true ->
  forall rho,
    satisfies_database rho db ->
    satisfies_database rho (add_drup_steps db trace).
Proof.
revert db.
induction trace as [|step trace IH]; intros db Hcheck rho Hdb.
- simpl. exact Hdb.
- destruct step as [c hints | ids].
  + simpl in Hcheck |- *.
    destruct (rup_hints db c hints) eqn:Hrup; try discriminate.
    apply (IH (database_add db c) Hcheck rho).
    apply satisfies_database_add; [exact Hdb |].
    eapply rup_hints_sound; eauto.
  + simpl in Hcheck |- *.
    eapply IH; eauto.
Qed.
