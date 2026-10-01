(** * Rotation-normalized reductions for the k=7 C12 low-endpoint branch *)

From mathcomp Require Import all_boot.
From Stdlib Require Import List Bool Arith Lia.
From Digraph Require Import ckpath_cnf ckpath_cnf_reduction ckpath_cert_base
  ckpath_cert_k7_base ckpath_cert_k7_c12_low3_base ckpath_k7_orbits.
Import ListNotations.

(** Select only the variables whose mask bit is true.  The start index is
    explicit so the executable order agrees with the Python specializer. *)
Fixpoint selected_assignment_from
    (variable : nat -> nat) (value : bool)
    (start : nat) (mask : list bool) : assignment :=
  match mask with
  | [] => []
  | selected :: mask' =>
      if selected then
        (variable start, value) ::
          selected_assignment_from variable value (S start) mask'
      else selected_assignment_from variable value (S start) mask'
  end.

(** The generator first substitutes all selected set variables with [false],
    then all selected low marks with [true]. *)
Definition c12_k7_low_subset_assignment (mask : list bool) : assignment :=
  selected_assignment_from (set_var 12) false 0 mask ++
  selected_assignment_from (mark_var 12) true 0 mask.

Definition c12_k7_low3_instance (mask : list bool) : cnf :=
  reduce_cnf (c12_k7_low_subset_assignment mask) c12_k7_low3_base.

Lemma selected_assignment_from_bits_extends
    (rho : valuation) (variable : nat -> nat) (value : bool)
    (start len : nat) (bits : nat -> bool) :
  (forall i,
      (start <= i < start + len)%coq_nat ->
      bits i = true -> rho (variable i) = value) ->
  extends rho
    (selected_assignment_from variable value start
       (List.map bits (List.seq start len))).
Proof.
revert start.
induction len as [|len IH]; intros start Hbits x b Hin.
- inversion Hin.
- simpl in Hin.
  destruct (bits start) eqn:Hstart; simpl in Hin.
  + destruct Hin as [Heq | Hin].
    * inversion Heq; subst x b.
      apply Hbits; [lia | exact Hstart].
    * apply (IH (S start)).
      -- intros i Hi Htrue. apply Hbits; [lia | exact Htrue].
      -- exact Hin.
  + apply (IH (S start)).
    * intros i Hi Htrue. apply Hbits; [lia | exact Htrue].
    * exact Hin.
Qed.

Lemma extends_app_intro (rho : valuation) (a b : assignment) :
  extends rho a -> extends rho b -> extends rho (a ++ b).
Proof.
intros Ha Hb x value Hin.
apply List.in_app_or in Hin.
destruct Hin as [Hin | Hin]; [exact (Ha x value Hin) | exact (Hb x value Hin)].
Qed.

Lemma c12_k7_low_subset_assignment_bits_extends
    (rho : valuation) (bits : nat -> bool) :
  (forall i,
      (i < 12)%coq_nat -> bits i = true ->
      rho (set_var 12 i) = false) ->
  (forall i,
      (i < 12)%coq_nat -> bits i = true ->
      rho (mark_var 12 i) = true) ->
  extends rho
    (c12_k7_low_subset_assignment
       (List.map bits (vertex_list 12))).
Proof.
intros Hset Hmark.
unfold c12_k7_low_subset_assignment, vertex_list.
apply extends_app_intro.
- apply selected_assignment_from_bits_extends.
  intros i Hi Htrue. apply Hset; [lia | exact Htrue].
- apply selected_assignment_from_bits_extends.
  intros i Hi Htrue. apply Hmark; [lia | exact Htrue].
Qed.

Lemma c12_k7_low3_instance_satisfied rho mask :
  extends rho (c12_k7_low_subset_assignment mask) ->
  satisfies_cnf rho c12_k7_low3_base ->
  satisfies_cnf rho (c12_k7_low3_instance mask).
Proof.
intros Hextends Hbase.
unfold c12_k7_low3_instance.
exact (reduce_cnf_sound rho _ _ Hextends Hbase).
Qed.

(** There are only nineteen cyclic orbits of three selected positions. *)
Lemma k7_orbit_representatives_12_3_checked :
  List.length (orbit_representatives 12 3) = 19 /\
  representatives_rootedb 12 3 = true.
Proof. vm_compute. split; reflexivity. Qed.

Lemma k7_orbit_representatives_12_3_count :
  List.length (orbit_representatives 12 3) = 19.
Proof. exact (proj1 k7_orbit_representatives_12_3_checked). Qed.

Lemma k7_orbit_representatives_12_3_rooted :
  representatives_rootedb 12 3 = true.
Proof. exact (proj2 k7_orbit_representatives_12_3_checked). Qed.
