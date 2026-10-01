(** * A transparent hinted-RUP / DRUP checker

    Each addition carries a list of stable, zero-based clause identifiers.
    Starting from the negation of the proposed clause, every referenced clause
    must reduce either to a unit (which is assigned) or to the final conflict.
    This is the LRAT-style hinted form of RUP: no scan of the whole database is
    performed.  Clause storage is a persistent binary trie, so additions and
    lookups do not introduce quadratic list-append costs.

    Deletion records are accepted and ignored.  This is sound (retaining extra
    clauses only strengthens propagation) and keeps clause identifiers stable.
    A successful trace must end by adding the empty clause. *)

From Stdlib Require Import List Bool Arith BinNums PArith Lia.
From Digraph Require Import ckpath_cnf.
Import ListNotations.

(** ** Persistent clause database *)

Inductive positive_trie (A : Type) : Type :=
| TrieEmpty : positive_trie A
| TrieNode : option A -> positive_trie A -> positive_trie A -> positive_trie A.

Arguments TrieEmpty {A}.
Arguments TrieNode {A} _ _ _.

Fixpoint trie_lookup {A : Type} (p : positive) (t : positive_trie A) : option A :=
  match t with
  | TrieEmpty => None
  | TrieNode here even odd =>
      match p with
      | xH => here
      | xO q => trie_lookup q even
      | xI q => trie_lookup q odd
      end
  end.

Fixpoint trie_insert {A : Type}
    (p : positive) (value : A) (t : positive_trie A) : positive_trie A :=
  match p with
  | xH =>
      match t with
      | TrieEmpty => TrieNode (Some value) TrieEmpty TrieEmpty
      | TrieNode _ even odd => TrieNode (Some value) even odd
      end
  | xO q =>
      match t with
      | TrieEmpty => TrieNode None (trie_insert q value TrieEmpty) TrieEmpty
      | TrieNode here even odd => TrieNode here (trie_insert q value even) odd
      end
  | xI q =>
      match t with
      | TrieEmpty => TrieNode None TrieEmpty (trie_insert q value TrieEmpty)
      | TrieNode here even odd => TrieNode here even (trie_insert q value odd)
      end
  end.

Lemma trie_lookup_empty {A : Type} (p : positive) :
  trie_lookup p (@TrieEmpty A) = None.
Proof. destruct p; reflexivity. Qed.

Lemma trie_lookup_insert {A : Type}
    (p q : positive) (value : A) (t : positive_trie A) :
  trie_lookup q (trie_insert p value t) =
  if Pos.eqb p q then Some value else trie_lookup q t.
Proof.
revert q t.
induction p as [p IHp | p IHp |]; intros q t;
  destruct q; destruct t; simpl; try rewrite IHp;
  try rewrite trie_lookup_empty; reflexivity.
Qed.

Definition clause_key (i : nat) : positive := Pos.of_succ_nat i.

Record clause_database : Type := {
  database_next : nat;
  database_data : positive_trie clause
}.

Definition database_lookup (db : clause_database) (i : nat) : option clause :=
  trie_lookup (clause_key i) (database_data db).

Definition database_add (db : clause_database) (c : clause) : clause_database :=
  {| database_next := S (database_next db);
     database_data :=
       trie_insert (clause_key (database_next db)) c (database_data db) |}.

Fixpoint database_add_cnf
    (i : nat) (f : cnf) (data : positive_trie clause) : positive_trie clause :=
  match f with
  | [] => data
  | c :: f' => database_add_cnf (S i) f' (trie_insert (clause_key i) c data)
  end.

Definition initial_database (f : cnf) : clause_database :=
  {| database_next := length f;
     database_data := database_add_cnf 0 f TrieEmpty |}.

Definition satisfies_database (rho : valuation) (db : clause_database) : Prop :=
  forall i c, database_lookup db i = Some c -> eval_clause rho c = true.

Lemma satisfies_database_add
    (rho : valuation) (db : clause_database) (c : clause) :
  satisfies_database rho db -> eval_clause rho c = true ->
  satisfies_database rho (database_add db c).
Proof.
intros Hdb Hc i d Hlook.
unfold database_lookup, database_add in Hlook; simpl in Hlook.
rewrite trie_lookup_insert in Hlook.
destruct (Pos.eqb (clause_key (database_next db)) (clause_key i)) eqn:E.
- inversion Hlook; subst d. exact Hc.
- apply Hdb with (i := i). exact Hlook.
Qed.

Lemma database_add_cnf_sound
    (rho : valuation) (f : cnf) (i : nat) (data : positive_trie clause) :
  (forall j c, trie_lookup (clause_key j) data = Some c ->
               eval_clause rho c = true) ->
  eval_cnf rho f = true ->
  forall j c,
    trie_lookup (clause_key j) (database_add_cnf i f data) = Some c ->
    eval_clause rho c = true.
Proof.
revert i data.
induction f as [|c f IH]; intros i data Hdata Hsat.
- simpl. exact Hdata.
- unfold eval_cnf in Hsat; simpl in Hsat.
  apply andb_true_iff in Hsat. destruct Hsat as [Hc Hf].
  simpl. apply IH.
  + intros j d Hlook. rewrite trie_lookup_insert in Hlook.
    destruct (Pos.eqb (clause_key i) (clause_key j)) eqn:E.
    * inversion Hlook; subst d. exact Hc.
    * apply Hdata with (j := j). exact Hlook.
  + exact Hf.
Qed.

Lemma initial_database_sound (rho : valuation) (f : cnf) :
  eval_cnf rho f = true -> satisfies_database rho (initial_database f).
Proof.
intros Hsat i c Hlook.
unfold initial_database, database_lookup in Hlook; simpl in Hlook.
eapply (database_add_cnf_sound rho f 0 TrieEmpty); eauto.
intros j d Hj. rewrite trie_lookup_empty in Hj. discriminate.
Qed.

(** ** Hinted unit propagation *)

Fixpoint propagate_hints
    (db : clause_database) (a : assignment) (hints : list nat) : bool :=
  match hints with
  | [] => false
  | i :: hints' =>
      match database_lookup db i with
      | None => false
      | Some c =>
          match reduce_clause a c with
          | None => false
          | Some [] => true
          | Some [(x, b)] =>
              match insert_assignment x b a with
              | None => false
              | Some a' => propagate_hints db a' hints'
              end
          | Some (_ :: _ :: _) => false
          end
      end
  end.

Definition rup_hints
    (db : clause_database) (target : clause) (hints : list nat) : bool :=
  match assume_clause_false target [] with
  | None => true
  | Some a => propagate_hints db a hints
  end.

Lemma reduced_empty_conflict
    (rho : valuation) (a : assignment) (c : clause) :
  extends rho a -> reduce_clause a c = Some [] -> eval_clause rho c = false.
Proof.
intros Ha Hred.
pose proof (reduce_clause_sound rho a c [] Ha Hred) as H.
unfold eval_clause in H; simpl in H. exact H.
Qed.

Lemma reduced_singleton_forces
    (rho : valuation) (a : assignment) (c : clause) (x : nat) (b : bool) :
  extends rho a -> reduce_clause a c = Some [(x, b)] ->
  eval_clause rho c = true -> rho x = b.
Proof.
intros Ha Hred Hsat.
pose proof (reduce_clause_sound rho a c [(x, b)] Ha Hred) as H.
rewrite Hsat in H.
unfold eval_clause in H; simpl in H.
apply eval_literal_true_iff.
rewrite orb_false_r in H. symmetry. exact H.
Qed.

Lemma propagate_hints_sound
    (db : clause_database) (a : assignment) (hints : list nat) :
  propagate_hints db a hints = true ->
  forall rho, extends rho a -> satisfies_database rho db -> False.
Proof.
revert a.
induction hints as [|i hints IH]; intros a Hprop rho Ha Hdb.
- simpl in Hprop. discriminate.
- simpl in Hprop.
  destruct (database_lookup db i) as [c |] eqn:Hlookup;
    try discriminate.
  destruct (reduce_clause a c) as [r |] eqn:Hred; try discriminate.
  destruct r as [|l r'].
  + pose proof (Hdb i c Hlookup) as Hsat.
    pose proof (reduced_empty_conflict rho a c Ha Hred) as Hfalse.
    congruence.
  + destruct r' as [|l' r'']; try discriminate.
    destruct l as [x b].
    destruct (insert_assignment x b a) as [a' |] eqn:Hins;
      try discriminate.
    apply (IH a' Hprop rho).
    * assert (Hc : eval_clause rho c = true) by
        (apply Hdb with (i := i); exact Hlookup).
      assert (Hx : rho x = b) by
        (eapply reduced_singleton_forces; eauto).
      eapply insert_assignment_some; eauto.
    * exact Hdb.
    * destruct l. simpl in Hprop. discriminate.
Qed.

Theorem rup_hints_sound
    (db : clause_database) (target : clause) (hints : list nat) :
  rup_hints db target hints = true ->
  forall rho, satisfies_database rho db -> eval_clause rho target = true.
Proof.
unfold rup_hints.
destruct (assume_clause_false target []) as [a |] eqn:Hassume;
  intros Hrup rho Hdb.
- destruct (eval_clause rho target) eqn:Htarget; [reflexivity |].
  pose proof
    (assume_clause_false_sound rho target [] (extends_nil rho)) as Hinit.
  rewrite Hassume in Hinit. specialize (Hinit Htarget).
  exfalso. eapply propagate_hints_sound; eauto.
- pose proof
    (assume_clause_false_sound rho target [] (extends_nil rho)) as Hinit.
  rewrite Hassume in Hinit. exact Hinit.
Qed.

(** ** Trace checking and the final soundness theorem *)

Inductive drup_step : Type :=
| RupAdd : clause -> list nat -> drup_step
| Delete : list nat -> drup_step.

Fixpoint check_drup_from
    (db : clause_database) (trace : list drup_step) : bool :=
  match trace with
  | [] => false
  | Delete _ :: trace' => check_drup_from db trace'
  | RupAdd c hints :: trace' =>
      if rup_hints db c hints then
        match trace' with
        | [] =>
            match c with
            | [] => true
            | _ => false
            end
        | _ => check_drup_from (database_add db c) trace'
        end
      else false
  end.

Definition check_drup (base : cnf) (trace : list drup_step) : bool :=
  check_drup_from (initial_database base) trace.

Lemma check_drup_from_sound (db : clause_database) (trace : list drup_step) :
  check_drup_from db trace = true ->
  forall rho, satisfies_database rho db -> False.
Proof.
revert db.
induction trace as [|step trace IH]; intros db Hcheck rho Hdb.
- simpl in Hcheck. discriminate.
- destruct step as [c hints | ids].
  + simpl in Hcheck.
    destruct (rup_hints db c hints) eqn:Hrup; try discriminate.
    destruct trace as [|step' trace'].
    * destruct c as [|l c']; try discriminate.
      pose proof (rup_hints_sound db [] hints Hrup rho Hdb) as Hempty.
      unfold eval_clause in Hempty; simpl in Hempty. discriminate.
    * apply (IH (database_add db c) Hcheck rho).
      apply satisfies_database_add.
      -- exact Hdb.
      -- eapply rup_hints_sound; eauto.
  + simpl in Hcheck. eapply IH; eauto.
Qed.

Theorem check_drup_unsatisfiable (base : cnf) (trace : list drup_step) :
  check_drup base trace = true ->
  forall rho, ~ satisfies_cnf rho base.
Proof.
intros Hcheck rho Hsat.
unfold check_drup in Hcheck.
eapply check_drup_from_sound; eauto.
apply initial_database_sound. exact Hsat.
Qed.

(** A two-clause smoke certificate: under the empty target, clause 0 forces
    [x], then clause 1 conflicts with [not x]. *)

Definition smoke_base : cnf := [[(0, true)]; [(0, false)]].
Definition smoke_trace : list drup_step := [RupAdd [] [0; 1]].

Lemma smoke_certificate_checks : check_drup smoke_base smoke_trace = true.
Proof. vm_compute. reflexivity. Qed.

Lemma smoke_certificate_is_unsat :
  forall rho, ~ satisfies_cnf rho smoke_base.
Proof.
apply (check_drup_unsatisfiable smoke_base smoke_trace).
exact smoke_certificate_checks.
Qed.
