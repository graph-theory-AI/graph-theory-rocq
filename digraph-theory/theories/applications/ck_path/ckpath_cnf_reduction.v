(** * Whole-CNF reduction under a partial assignment *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf.
Import ListNotations.

(** Drop clauses already satisfied by [a], and remove literals falsified by
    [a] from every remaining clause.  The order of both clauses and unresolved
    literals is preserved, which lets generated certificates target this
    executable reduction exactly. *)
Fixpoint reduce_cnf (a : assignment) (f : cnf) : cnf :=
  match f with
  | [] => []
  | c :: f' =>
      match reduce_clause a c with
      | None => reduce_cnf a f'
      | Some r => r :: reduce_cnf a f'
      end
  end.

Lemma reduce_clause_none_sound
    (rho : valuation) (a : assignment) (c : clause) :
  extends rho a -> reduce_clause a c = None ->
  eval_clause rho c = true.
Proof.
induction c as [|[x b] c IHc]; intros Ha Hred.
- discriminate.
- simpl in Hred.
  destruct (lookup_assignment x a) as [v |] eqn:Hlook.
  + destruct (Bool.eqb v b) eqn:Hvb.
    * apply Bool.eqb_true_iff in Hvb.
      assert (Hrho : rho x = v) by
        (eapply lookup_assignment_sound; eauto).
      unfold eval_clause; simpl.
      rewrite (proj2 (eval_literal_true_iff rho x b)); [reflexivity |].
      destruct v, b; simpl in Hvb |- *; congruence.
    * unfold eval_clause; simpl.
      change (eval_literal rho (x, b) || eval_clause rho c = true).
      rewrite (IHc Ha Hred), orb_true_r. reflexivity.
  + destruct (reduce_clause a c) as [r |] eqn:Htail;
      try discriminate.
    unfold eval_clause; simpl.
    change (eval_literal rho (x, b) || eval_clause rho c = true).
    rewrite (IHc Ha eq_refl), orb_true_r. reflexivity.
Qed.

Lemma reduce_cnf_eval
    (rho : valuation) (a : assignment) (f : cnf) :
  extends rho a ->
  eval_cnf rho (reduce_cnf a f) = eval_cnf rho f.
Proof.
intro Ha.
induction f as [|c f IHf].
- reflexivity.
- simpl [reduce_cnf].
  destruct (reduce_clause a c) as [r |] eqn:Hred.
  + simpl [eval_cnf].
    rewrite <- (reduce_clause_sound rho a c r Ha Hred).
    now rewrite IHf.
  + simpl [eval_cnf].
    rewrite (reduce_clause_none_sound rho a c Ha Hred).
    simpl. exact IHf.
Qed.

Lemma reduce_cnf_sound
    (rho : valuation) (a : assignment) (f : cnf) :
  extends rho a -> satisfies_cnf rho f ->
  satisfies_cnf rho (reduce_cnf a f).
Proof.
intros Ha Hsat.
unfold satisfies_cnf in *.
now rewrite (reduce_cnf_eval rho a f Ha).
Qed.
