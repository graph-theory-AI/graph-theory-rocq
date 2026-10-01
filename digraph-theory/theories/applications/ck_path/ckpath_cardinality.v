(** * Direct cardinality clauses

    For the small static configurations used by the k=5 and k=6 endgames,
    the most audit-friendly cardinality encoding is the direct truth-table
    encoding: enumerate Boolean rows and add the clause blocking each row that
    violates the requested bound.  It has no auxiliary variables and its
    semantics follows from a single canonical row, [map rho xs]. *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf.
Import ListNotations.

Fixpoint bit_vectors (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' =>
      map (cons false) (bit_vectors n') ++
      map (cons true) (bit_vectors n')
  end.

Fixpoint count_true_bits (bs : list bool) : nat :=
  match bs with
  | [] => 0
  | b :: bs' => if b then S (count_true_bits bs') else count_true_bits bs'
  end.

Definition count_true (rho : valuation) (xs : list nat) : nat :=
  count_true_bits (map rho xs).

Fixpoint blocking_clause (xs : list nat) (bs : list bool) : clause :=
  match xs, bs with
  | x :: xs', b :: bs' => (x, negb b) :: blocking_clause xs' bs'
  | _, _ => []
  end.

Definition at_most_clauses (k : nat) (xs : list nat) : cnf :=
  map (blocking_clause xs)
      (filter (fun bs => Nat.ltb k (count_true_bits bs))
              (bit_vectors (length xs))).

Definition at_least_clauses (k : nat) (xs : list nat) : cnf :=
  map (blocking_clause xs)
      (filter (fun bs => Nat.ltb (count_true_bits bs) k)
              (bit_vectors (length xs))).

Definition exactly_clauses (k : nat) (xs : list nat) : cnf :=
  at_most_clauses k xs ++ at_least_clauses k xs.

Lemma valuation_bits_in (rho : valuation) (xs : list nat) :
  In (map rho xs) (bit_vectors (length xs)).
Proof.
induction xs as [|x xs IH].
- simpl. now left.
- simpl. apply in_or_app. destruct (rho x) eqn:Hx.
  + right. apply in_map. exact IH.
  + left. apply in_map. exact IH.
Qed.

Lemma blocking_clause_self_false (rho : valuation) (xs : list nat) :
  eval_clause rho (blocking_clause xs (map rho xs)) = false.
Proof.
induction xs as [|x xs IH].
- reflexivity.
- unfold eval_clause in *. simpl.
  rewrite IH. unfold eval_literal; simpl.
  destruct (rho x); reflexivity.
Qed.

Theorem at_most_clauses_sound (rho : valuation) (k : nat) (xs : list nat) :
  eval_cnf rho (at_most_clauses k xs) = true -> count_true rho xs <= k.
Proof.
intros Hsat.
assert (Hnot : ~ k < count_true rho xs).
{ intro Hbad.
  assert (Hltb : Nat.ltb k (count_true_bits (map rho xs)) = true).
  { apply Nat.ltb_lt. exact Hbad. }
  assert (Hinrows : In (map rho xs)
      (filter (fun bs => Nat.ltb k (count_true_bits bs))
              (bit_vectors (length xs)))).
  { apply filter_In. split; [apply valuation_bits_in | exact Hltb]. }
  assert (Hincl : In (blocking_clause xs (map rho xs))
      (at_most_clauses k xs)).
  { unfold at_most_clauses. apply in_map. exact Hinrows. }
  pose proof (eval_cnf_member rho _ _ Hsat Hincl) as Heval.
  rewrite blocking_clause_self_false in Heval. discriminate.
}
unfold count_true in *. lia.
Qed.

Theorem at_least_clauses_sound (rho : valuation) (k : nat) (xs : list nat) :
  eval_cnf rho (at_least_clauses k xs) = true -> k <= count_true rho xs.
Proof.
intros Hsat.
assert (Hnot : ~ count_true rho xs < k).
{ intro Hbad.
  assert (Hltb : Nat.ltb (count_true_bits (map rho xs)) k = true).
  { apply Nat.ltb_lt. exact Hbad. }
  assert (Hinrows : In (map rho xs)
      (filter (fun bs => Nat.ltb (count_true_bits bs) k)
              (bit_vectors (length xs)))).
  { apply filter_In. split; [apply valuation_bits_in | exact Hltb]. }
  assert (Hincl : In (blocking_clause xs (map rho xs))
      (at_least_clauses k xs)).
  { unfold at_least_clauses. apply in_map. exact Hinrows. }
  pose proof (eval_cnf_member rho _ _ Hsat Hincl) as Heval.
  rewrite blocking_clause_self_false in Heval. discriminate.
}
unfold count_true in *. lia.
Qed.

Theorem exactly_clauses_sound (rho : valuation) (k : nat) (xs : list nat) :
  eval_cnf rho (exactly_clauses k xs) = true -> count_true rho xs = k.
Proof.
intros Hsat.
unfold exactly_clauses, eval_cnf in Hsat.
rewrite forallb_app in Hsat.
apply andb_true_iff in Hsat. destruct Hsat as [Hmax Hmin].
pose proof (at_most_clauses_sound rho k xs Hmax) as Hle.
pose proof (at_least_clauses_sound rho k xs Hmin) as Hge.
lia.
Qed.

(** A tiny reduction test, kept as an executable guard on the encoding. *)
Lemma exactly_two_of_three_rejects_all_true :
  eval_cnf (fun _ => true) (exactly_clauses 2 [0; 1; 2]) = false.
Proof. vm_compute. reflexivity. Qed.
