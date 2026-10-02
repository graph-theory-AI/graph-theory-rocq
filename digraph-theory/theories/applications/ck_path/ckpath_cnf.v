(** * Transparent CNF semantics and partial assignments

    This file is deliberately independent of the graph library.  Literals are
    pairs [(variable, polarity)]; variables are natural numbers and a literal
    [(x,b)] asks that the valuation of [x] be [b].  The executable definitions
    below are kept transparent so that concrete certificates can be checked by
    [vm_compute]. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Definition valuation := nat -> bool.
Definition literal := (nat * bool)%type.
Definition clause := list literal.
Definition cnf := list clause.

Definition negate_literal (l : literal) : literal :=
  (fst l, negb (snd l)).

Definition eval_literal (rho : valuation) (l : literal) : bool :=
  Bool.eqb (rho (fst l)) (snd l).

Definition eval_clause (rho : valuation) (c : clause) : bool :=
  existsb (eval_literal rho) c.

Definition eval_cnf (rho : valuation) (f : cnf) : bool :=
  forallb (eval_clause rho) f.

Definition satisfies_clause (rho : valuation) (c : clause) : Prop :=
  eval_clause rho c = true.

Definition satisfies_cnf (rho : valuation) (f : cnf) : Prop :=
  eval_cnf rho f = true.

Lemma eval_literal_true_iff (rho : valuation) (x : nat) (b : bool) :
  eval_literal rho (x, b) = true <-> rho x = b.
Proof.
unfold eval_literal; simpl.
apply Bool.eqb_true_iff.
Qed.

Lemma eval_literal_false_iff (rho : valuation) (x : nat) (b : bool) :
  eval_literal rho (x, b) = false <-> rho x = negb b.
Proof.
unfold eval_literal; simpl.
destruct (rho x), b; simpl; intuition congruence.
Qed.

Lemma eval_literal_negate (rho : valuation) (l : literal) :
  eval_literal rho (negate_literal l) = negb (eval_literal rho l).
Proof.
destruct l as [x b].
unfold negate_literal, eval_literal; simpl.
destruct (rho x), b; reflexivity.
Qed.

Lemma eval_cnf_member (rho : valuation) (f : cnf) (c : clause) :
  eval_cnf rho f = true -> In c f -> eval_clause rho c = true.
Proof.
unfold eval_cnf.
intros H Hin.
apply (proj1 (forallb_forall (eval_clause rho) f) H c Hin).
Qed.

Lemma eval_cnf_snoc (rho : valuation) (f : cnf) (c : clause) :
  eval_cnf rho (f ++ [c]) = eval_cnf rho f && eval_clause rho c.
Proof.
unfold eval_cnf.
rewrite forallb_app; simpl.
rewrite andb_true_r; reflexivity.
Qed.

(** A partial assignment is a list of required variable values.  All
    assignments produced by [insert_assignment] are consistent; the abstract
    [extends] predicate is intentionally simple and proof-oriented. *)

Definition assignment := list literal.

Definition extends (rho : valuation) (a : assignment) : Prop :=
  forall x b, In (x, b) a -> rho x = b.

Fixpoint lookup_assignment (x : nat) (a : assignment) : option bool :=
  match a with
  | [] => None
  | (y, b) :: a' => if Nat.eqb x y then Some b else lookup_assignment x a'
  end.

Lemma lookup_assignment_sound
    (rho : valuation) (a : assignment) (x : nat) (b : bool) :
  extends rho a -> lookup_assignment x a = Some b -> rho x = b.
Proof.
induction a as [|[y c] a IHa]; intros Ha Hlook.
- discriminate.
- simpl in Hlook. destruct (Nat.eqb x y) eqn:Exy.
  + apply Nat.eqb_eq in Exy. subst y. inversion Hlook; subst b.
    apply Ha. now left.
  + apply IHa.
    * intros z d Hz. apply Ha. now right.
    * exact Hlook.
Qed.

Fixpoint insert_assignment
    (x : nat) (b : bool) (a : assignment) : option assignment :=
  match a with
  | [] => Some [(x, b)]
  | (y, c) :: a' =>
      if Nat.eqb x y then
        if Bool.eqb b c then Some a else None
      else
        match insert_assignment x b a' with
        | Some a'' => Some ((y, c) :: a'')
        | None => None
        end
  end.

Lemma insert_assignment_some
    (rho : valuation) (a a' : assignment) (x : nat) (b : bool) :
  extends rho a -> rho x = b ->
  insert_assignment x b a = Some a' -> extends rho a'.
Proof.
revert a'.
induction a as [|[y c] a IHa]; intros a' Ha Hx Hins.
- simpl in Hins. inversion Hins; subst a'.
  intros z d Hz. simpl in Hz. destruct Hz as [Hz | Hz].
  + inversion Hz; subst. reflexivity.
  + contradiction.
- simpl in Hins.
  destruct (Nat.eqb x y) eqn:Exy.
  + destruct (Bool.eqb b c) eqn:Ebc; try discriminate.
    inversion Hins; subst a'. exact Ha.
  + destruct (insert_assignment x b a) as [a'' |] eqn:Ei;
      try discriminate.
    inversion Hins; subst a'.
    intros z d Hz. simpl in Hz. destruct Hz as [Hz | Hz].
    * apply Ha. now left.
    * eapply IHa; eauto.
      intros u v Huv. apply Ha. now right.
Qed.

Lemma insert_assignment_none
    (rho : valuation) (a : assignment) (x : nat) (b : bool) :
  extends rho a -> insert_assignment x b a = None -> rho x <> b.
Proof.
induction a as [|[y c] a IHa]; intros Ha Hnone.
- simpl in Hnone. discriminate.
- simpl in Hnone.
  destruct (Nat.eqb x y) eqn:Exy.
  + destruct (Bool.eqb b c) eqn:Ebc; try discriminate.
    apply Nat.eqb_eq in Exy. subst y.
    apply Bool.eqb_false_iff in Ebc.
    pose proof (Ha x c (or_introl eq_refl)) as Hc.
    intro Hxb. apply Ebc. congruence.
  + destruct (insert_assignment x b a) eqn:Ei; try discriminate.
    apply IHa.
    * intros z d Hz. apply Ha. now right.
    * reflexivity.
Qed.

(** [reduce_clause a c] is [None] when [a] already satisfies [c].  Otherwise
    it returns the unresolved literals, after deleting those falsified by [a]. *)

Fixpoint reduce_clause (a : assignment) (c : clause) : option clause :=
  match c with
  | [] => Some []
  | (x, b) :: c' =>
      match lookup_assignment x a with
      | Some v =>
          if Bool.eqb v b then None else reduce_clause a c'
      | None =>
          match reduce_clause a c' with
          | None => None
          | Some r => Some ((x, b) :: r)
          end
      end
  end.

Lemma reduce_clause_sound
    (rho : valuation) (a : assignment) (c r : clause) :
  extends rho a -> reduce_clause a c = Some r ->
  eval_clause rho c = eval_clause rho r.
Proof.
revert r.
induction c as [|[x b] c IHc]; intros r Ha Hred.
- simpl in Hred. inversion Hred; reflexivity.
- simpl in Hred.
  destruct (lookup_assignment x a) as [v |] eqn:Hlook.
  + destruct (Bool.eqb v b) eqn:Hvb; try discriminate.
    assert (Hrho : rho x = v) by
      (eapply lookup_assignment_sound; eauto).
    assert (Hv : v = negb b).
    { destruct v, b; simpl in Hvb; try discriminate; reflexivity. }
    assert (Hlit : eval_literal rho (x, b) = false).
    { apply eval_literal_false_iff. now rewrite Hrho, Hv. }
    unfold eval_clause; simpl. rewrite Hlit; simpl.
    eapply IHc; eauto.
  + destruct (reduce_clause a c) as [r' |] eqn:Htail;
      try discriminate.
    inversion Hred; subst r.
    unfold eval_clause; simpl.
    pose proof (IHc r' Ha eq_refl) as Heq.
    unfold eval_clause in Heq.
    rewrite Heq. reflexivity.
Qed.

(** Build the initial assignment which falsifies every literal in the target
    RUP clause.  [None] means that complementary target literals made those
    assumptions inconsistent, i.e. the target is a tautology. *)

Fixpoint assume_clause_false
    (c : clause) (a : assignment) : option assignment :=
  match c with
  | [] => Some a
  | (x, b) :: c' =>
      match insert_assignment x (negb b) a with
      | None => None
      | Some a' => assume_clause_false c' a'
      end
  end.

Lemma assume_clause_false_sound (rho : valuation) (c : clause) (a : assignment) :
  extends rho a ->
  match assume_clause_false c a with
  | None => eval_clause rho c = true
  | Some a' => eval_clause rho c = false -> extends rho a'
  end.
Proof.
revert a.
induction c as [|[x b] c IHc]; intros a Ha.
- simpl. intros _. exact Ha.
- simpl.
  destruct (insert_assignment x (negb b) a) as [a1 |] eqn:Hins.
  + pose proof (IHc a1) as IH.
    destruct (assume_clause_false c a1) as [a2 |] eqn:Htail.
    * intros Hfalse.
      unfold eval_clause in Hfalse; simpl in Hfalse.
      apply orb_false_iff in Hfalse. destruct Hfalse as [Hlit Hc].
      assert (Hx : rho x = negb b) by
        (apply eval_literal_false_iff; exact Hlit).
      assert (Ha1 : extends rho a1) by
        (eapply insert_assignment_some; eauto).
      apply IH; assumption.
    * destruct (eval_literal rho (x, b)) eqn:Hlit; simpl.
      -- reflexivity.
      -- assert (Hx : rho x = negb b) by
           (apply eval_literal_false_iff; exact Hlit).
         assert (Ha1 : extends rho a1) by
           (eapply insert_assignment_some; eauto).
         apply IH in Ha1. exact Ha1.
  + assert (Hneq : rho x <> negb b) by
      (eapply insert_assignment_none; eauto).
    assert (Hx : rho x = b) by
      (destruct (rho x), b; simpl in Hneq; congruence).
    unfold eval_clause; simpl.
    rewrite (proj2 (eval_literal_true_iff rho x b) Hx). reflexivity.
Qed.

Lemma extends_nil (rho : valuation) : extends rho [].
Proof.
intros x b H. inversion H.
Qed.
