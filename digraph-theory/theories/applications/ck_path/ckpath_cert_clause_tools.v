(** * Semantic plumbing for the CK-path graph-to-CNF bridge *)

From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cardinality
  ckpath_cert_base ckpath_cert_valuation.
Import ListNotations.

Lemma eval_positive_literal (rho : valuation) x :
  eval_literal rho (positive_literal x) = rho x.
Proof.
unfold eval_literal, positive_literal; simpl.
destruct (rho x); reflexivity.
Qed.

Lemma eval_negative_literal (rho : valuation) x :
  eval_literal rho (negative_literal x) = negb (rho x).
Proof.
unfold eval_literal, negative_literal; simpl.
destruct (rho x); reflexivity.
Qed.

Lemma eval_positive_clause (rho : valuation) xs :
  eval_clause rho (map positive_literal xs) = existsb rho xs.
Proof.
induction xs as [|x xs IH]; simpl; [reflexivity |].
unfold eval_clause in IH |- *; simpl in IH |- *.
rewrite eval_positive_literal, IH. reflexivity.
Qed.

Lemma eval_negative_clause (rho : valuation) xs :
  eval_clause rho (map negative_literal xs) = negb (forallb rho xs).
Proof.
induction xs as [|x xs IH]; simpl; [reflexivity |].
unfold eval_clause in IH |- *; simpl in IH |- *.
rewrite eval_negative_literal, IH.
destruct (rho x), (forallb rho xs); reflexivity.
Qed.

Lemma satisfies_cnf_app (rho : valuation) f g :
  satisfies_cnf rho (f ++ g) <->
  satisfies_cnf rho f /\ satisfies_cnf rho g.
Proof.
unfold satisfies_cnf, eval_cnf.
rewrite forallb_app, andb_true_iff.
reflexivity.
Qed.

Lemma satisfies_cnf_map {A : Type} (rho : valuation)
    (f : A -> clause) xs :
  (forall x, In x xs -> satisfies_clause rho (f x)) ->
  satisfies_cnf rho (map f xs).
Proof.
intro H.
unfold satisfies_cnf, eval_cnf.
apply forallb_forall.
intros c Hc.
apply in_map_iff in Hc.
destruct Hc as [x [<- Hx]].
exact (H x Hx).
Qed.

Lemma satisfies_cnf_flat_map {A : Type} (rho : valuation)
    (f : A -> cnf) xs :
  (forall x, In x xs -> satisfies_cnf rho (f x)) ->
  satisfies_cnf rho (flat_map f xs).
Proof.
intro H.
unfold satisfies_cnf, eval_cnf.
apply forallb_forall.
intros c Hc.
apply in_flat_map in Hc.
destruct Hc as [x [Hx Hcx]].
pose proof (H x Hx) as Hfx.
unfold satisfies_cnf, eval_cnf in Hfx.
apply (proj1 (forallb_forall (eval_clause rho) (f x)) Hfx c Hcx).
Qed.

Lemma count_true_map_lookup (rho : valuation)
    (code : nat -> nat) (bits : nat -> bool) xs :
  (forall i, In i xs -> rho (code i) = bits i) ->
  count_true rho (map code xs) = count_true_bits (map bits xs).
Proof.
intro Hlookup.
unfold count_true.
rewrite map_map.
apply f_equal.
apply map_ext_in.
intros i Hi.
exact (Hlookup i Hi).
Qed.

Lemma count_true_bits_le_length bs : count_true_bits bs <= length bs.
Proof.
induction bs as [|b bs IH]; simpl; [lia |].
destruct b; simpl; lia.
Qed.

Lemma count_true_bits_map_negb bs :
  count_true_bits (map negb bs) = length bs - count_true_bits bs.
Proof.
induction bs as [|b bs IH]; simpl; [reflexivity |].
rewrite IH.
pose proof (count_true_bits_le_length bs) as Hle.
destruct b; simpl.
- reflexivity.
- destruct (count_true_bits bs) eqn:Hc; simpl in *; lia.
Qed.

Lemma cover_rotation_clause_complete rho n endpoint path :
  (rho (set_var n endpoint) = true ->
   (forall x, In x (path_chord_vars n path) -> rho x = true) ->
   rho (mark_var n (hd 0 path)) = true) ->
  satisfies_clause rho (cover_rotation_clause n endpoint path).
Proof.
intros Hcover.
unfold satisfies_clause, cover_rotation_clause.
change ((eval_literal rho (negative_literal (set_var n endpoint)) ||
         (eval_literal rho (positive_literal (mark_var n (hd 0 path))) ||
          eval_clause rho (map negative_literal (path_chord_vars n path)))) =
        true).
rewrite eval_negative_literal, eval_positive_literal,
  eval_negative_clause.
destruct (rho (set_var n endpoint)) eqn:Hset; simpl; [|reflexivity].
destruct (rho (mark_var n (hd 0 path))) eqn:Hmark; simpl;
  [reflexivity |].
destruct (forallb rho (path_chord_vars n path)) eqn:Hall;
  simpl; [|reflexivity].
exfalso.
assert (Hpoint : forall x, In x (path_chord_vars n path) -> rho x = true).
{ intros x Hx.
  exact (proj1 (forallb_forall rho (path_chord_vars n path)) Hall x Hx). }
specialize (Hcover eq_refl Hpoint).
congruence.
Qed.

Lemma c10_rotation_clause_complete rho endpoint path :
  (rho (mark_var 10 endpoint) = true ->
   rho (set_var 10 (cycle_predecessor 10 (hd 0 path))) = true ->
   (forall x, In x (path_chord_vars 10 path) -> rho x = true) -> False) ->
  satisfies_clause rho (c10_rotation_clause endpoint path).
Proof.
intros Hbad.
remember (cycle_predecessor 10 (hd 0 path)) as pred_start eqn:Hpred.
unfold satisfies_clause, c10_rotation_clause.
rewrite <- Hpred.
change ((eval_literal rho (negative_literal (mark_var 10 endpoint)) ||
         (eval_literal rho
            (negative_literal (set_var 10 pred_start)) ||
          eval_clause rho
            (map negative_literal (path_chord_vars 10 path)))) = true).
rewrite !eval_negative_literal, eval_negative_clause.
destruct (rho (mark_var 10 endpoint)) eqn:Hmark; simpl; [|reflexivity].
destruct (rho (set_var 10 pred_start)) eqn:Hset; simpl; [|reflexivity].
destruct (forallb rho (path_chord_vars 10 path)) eqn:Hall;
  simpl; [|reflexivity].
exfalso.
apply (Hbad eq_refl eq_refl).
intros x Hx.
exact (proj1 (forallb_forall rho (path_chord_vars 10 path)) Hall x Hx).
Qed.

Lemma positive_guard_exactly_complete rho x k xs :
  k <= length xs ->
  (rho x = true \/ count_true rho xs = k) ->
  satisfies_cnf rho (exactly_comb [positive_literal x] k xs).
Proof.
intros Hlen Hcase.
apply exactly_comb_complete; [exact Hlen |].
destruct Hcase as [Hx | Hcount].
- left. unfold eval_clause; simpl.
  rewrite eval_positive_literal, Hx. reflexivity.
- right. exact Hcount.
Qed.

Lemma negative_guard_exactly_complete rho x k xs :
  k <= length xs ->
  (rho x = false \/ count_true rho xs = k) ->
  satisfies_cnf rho (exactly_comb [negative_literal x] k xs).
Proof.
intros Hlen Hcase.
apply exactly_comb_complete; [exact Hlen |].
destruct Hcase as [Hx | Hcount].
- left. unfold eval_clause; simpl.
  rewrite eval_negative_literal, Hx. reflexivity.
- right. exact Hcount.
Qed.
