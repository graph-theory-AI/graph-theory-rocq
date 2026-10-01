(** * A concrete valuation for the finite CK-path certificates

    The certificate variable layout is arithmetic.  This module packages its
    inverse once, so the graph bridge only has to supply three Boolean
    predicates: arcs, membership in the distinguished set, and marked
    vertices. *)

From Stdlib Require Import Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cert_base.

Definition decoded_arc_source (n x : nat) : nat :=
  (x - 1) / (n - 1).

Definition decoded_arc_slot (n x : nat) : nat :=
  (x - 1) mod (n - 1).

Definition decoded_arc_target (n x : nat) : nat :=
  let u := decoded_arc_source n x in
  let r := decoded_arc_slot n x in
  if r <? u then r else S r.

Definition concrete_valuation
    (n : nat)
    (arc_bits : nat -> nat -> bool)
    (set_bits mark_bits : nat -> bool) : valuation :=
  fun x =>
    if x <? set_var n 0 then
      arc_bits (decoded_arc_source n x) (decoded_arc_target n x)
    else if x <? mark_var n 0 then
      set_bits (x - set_var n 0)
    else
      mark_bits (x - mark_var n 0).

Lemma arc_var_slot_bound n u v :
  2 <= n -> u < n -> v < n -> u <> v ->
  (if v <? u then v else v - 1) < n - 1.
Proof.
intros Hn Hu Hv Huv.
destruct (v <? u) eqn:Hvu.
- apply Nat.ltb_lt in Hvu. lia.
- apply Nat.ltb_ge in Hvu. lia.
Qed.

Lemma decoded_arc_source_arc_var n u v :
  2 <= n -> u < n -> v < n -> u <> v ->
  decoded_arc_source n (arc_var n u v) = u.
Proof.
intros Hn Hu Hv Huv.
pose proof (arc_var_slot_bound n u v Hn Hu Hv Huv) as Hr.
unfold decoded_arc_source, arc_var.
set (r := if v <? u then v else v - 1) in *.
replace (1 + u * (n - 1) + r - 1) with (u * (n - 1) + r) by nia.
rewrite Nat.div_add_l by lia.
rewrite Nat.div_small by lia.
lia.
Qed.

Lemma decoded_arc_slot_arc_var n u v :
  2 <= n -> u < n -> v < n -> u <> v ->
  decoded_arc_slot n (arc_var n u v) =
    if v <? u then v else v - 1.
Proof.
intros Hn Hu Hv Huv.
pose proof (arc_var_slot_bound n u v Hn Hu Hv Huv) as Hr.
unfold decoded_arc_slot, arc_var.
set (r := if v <? u then v else v - 1) in *.
replace (1 + u * (n - 1) + r - 1) with
    (r + u * (n - 1)) by nia.
rewrite Nat.Div0.mod_add.
rewrite Nat.mod_small by lia.
reflexivity.
Qed.

Lemma decoded_arc_target_arc_var n u v :
  2 <= n -> u < n -> v < n -> u <> v ->
  decoded_arc_target n (arc_var n u v) = v.
Proof.
intros Hn Hu Hv Huv.
unfold decoded_arc_target.
rewrite (decoded_arc_source_arc_var n u v Hn Hu Hv Huv).
rewrite (decoded_arc_slot_arc_var n u v Hn Hu Hv Huv).
destruct (v <? u) eqn:Hvu.
- pose proof (proj1 (Nat.ltb_lt v u) Hvu) as Hlt.
  rewrite Hvu. reflexivity.
- pose proof (proj1 (Nat.ltb_ge v u) Hvu) as Hge.
  assert (Huv' : u < v) by lia.
  assert (Hslot : (v - 1 <? u) = false).
  { apply Nat.ltb_ge. lia. }
  rewrite Hslot. lia.
Qed.

Lemma arc_var_injective n u v u' v' :
  2 <= n ->
  u < n -> v < n -> u <> v ->
  u' < n -> v' < n -> u' <> v' ->
  arc_var n u v = arc_var n u' v' ->
  u = u' /\ v = v'.
Proof.
intros Hn Hu Hv Huv Hu' Hv' Huv' Heq.
split.
- rewrite <-
    (decoded_arc_source_arc_var n u v Hn Hu Hv Huv).
  rewrite <-
    (decoded_arc_source_arc_var n u' v' Hn Hu' Hv' Huv').
  now rewrite Heq.
- rewrite <-
    (decoded_arc_target_arc_var n u v Hn Hu Hv Huv).
  rewrite <-
    (decoded_arc_target_arc_var n u' v' Hn Hu' Hv' Huv').
  now rewrite Heq.
Qed.

Lemma arc_var_before_set_vars n u v :
  2 <= n -> u < n -> v < n -> u <> v ->
  arc_var n u v < set_var n 0.
Proof.
intros Hn Hu Hv Huv.
pose proof (arc_var_slot_bound n u v Hn Hu Hv Huv) as Hr.
unfold arc_var, set_var.
set (r := if v <? u then v else v - 1) in *.
nia.
Qed.

Lemma concrete_valuation_arc n arc_bits set_bits mark_bits u v :
  2 <= n -> u < n -> v < n -> u <> v ->
  concrete_valuation n arc_bits set_bits mark_bits (arc_var n u v) =
    arc_bits u v.
Proof.
intros Hn Hu Hv Huv.
unfold concrete_valuation.
pose proof (arc_var_before_set_vars n u v Hn Hu Hv Huv) as Hrange.
rewrite (proj2 (Nat.ltb_lt _ _) Hrange).
rewrite (decoded_arc_source_arc_var n u v Hn Hu Hv Huv).
rewrite (decoded_arc_target_arc_var n u v Hn Hu Hv Huv).
reflexivity.
Qed.

Lemma concrete_valuation_set n arc_bits set_bits mark_bits u :
  u < n ->
  concrete_valuation n arc_bits set_bits mark_bits (set_var n u) =
    set_bits u.
Proof.
intro Hu.
unfold concrete_valuation, set_var, mark_var.
assert (Hfirst : (n * (n - 1) + 1 + u <? n * (n - 1) + 1 + 0) = false).
{ apply Nat.ltb_ge. lia. }
assert (Hsecond :
    (n * (n - 1) + 1 + u <? n * (n - 1) + n + 1 + 0) = true).
{ apply Nat.ltb_lt. lia. }
rewrite Hfirst, Hsecond.
f_equal. lia.
Qed.

Lemma concrete_valuation_mark n arc_bits set_bits mark_bits u :
  concrete_valuation n arc_bits set_bits mark_bits (mark_var n u) =
    mark_bits u.
Proof.
unfold concrete_valuation, set_var, mark_var.
assert (Hfirst :
    (n * (n - 1) + n + 1 + u <? n * (n - 1) + 1 + 0) = false).
{ apply Nat.ltb_ge. lia. }
assert (Hsecond :
    (n * (n - 1) + n + 1 + u <? n * (n - 1) + n + 1 + 0) = false).
{ apply Nat.ltb_ge. lia. }
rewrite Hfirst, Hsecond.
f_equal. lia.
Qed.
