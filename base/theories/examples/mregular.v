(** Downstream use of multigraph incidence regularity ([mregular], [mcubic]) and of the guarded
    [loopless_cubic], without corpus imports: parallel edges, loops and the empty multigraph. *)
From GTBase Require Import base.
From GraphTheory Require Import mgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Two vertices joined by three parallel edges. *)
Definition three_parallel : mgraph :=
  @Graph unit unit 'I_2 'I_3 (fun b _ => if b then ord_max else ord0) (fun _ => tt) (fun _ => tt).

(** One vertex carrying three loops. *)
Definition three_loops : mgraph :=
  @Graph unit unit 'I_1 'I_3 (fun _ _ => ord0) (fun _ => tt) (fun _ => tt).

(** No vertex and no edge. *)
Definition void_mgraph : mgraph :=
  @Graph unit unit 'I_0 'I_0 (fun _ e => e) (fun _ => tt) (fun _ => tt).

Lemma three_parallel_incident (v : three_parallel) (e : edge three_parallel) : incident v e.
Proof.
apply/existsP; exists (v != ord0).
by case: v => -[|[|m]] //= i; apply/eqP/val_inj.
Qed.

(** Parallel edges count separately: each vertex lies on three edges, and no edge is a loop. *)
Example three_parallel_loopless_cubic : loopless_cubic three_parallel.
Proof.
split; first by [].
move=> v; rewrite (_ : edges_at v = setT) ?cardsT ?card_ord //.
by apply/setP => e; rewrite !inE three_parallel_incident.
Qed.

Example three_parallel_max_degree : mDelta three_parallel = 3.
Proof. exact: (mregular_mDelta (ord0 : three_parallel) (loopless_cubic_mcubic three_parallel_loopless_cubic)). Qed.

(** Wrong degrees fail. *)
Example three_parallel_not_2_regular : ~ mregular three_parallel 2.
Proof.
move=> h; have := mregular_uniq (ord0 : three_parallel) h (loopless_cubic_mcubic three_parallel_loopless_cubic).
by [].
Qed.

(** A loop counts ONCE in the incidence degree: three loops on one vertex give an incidence-cubic
    multigraph, which is not loopless, so it is not [loopless_cubic]. *)
Example three_loops_mcubic : mcubic three_loops.
Proof.
move=> v; rewrite (_ : edges_at v = setT) ?cardsT ?card_ord //.
apply/setP => e; rewrite !inE; apply/existsP; exists false.
by rewrite (ord1 v).
Qed.

Example three_loops_not_loopless_cubic : ~ loopless_cubic three_loops.
Proof. by case=> /(_ ord0). Qed.

(** The empty multigraph is regular of every degree. *)
Example void_regular (r : nat) : mregular void_mgraph r.
Proof. by apply: mregular_void; rewrite card_ord. Qed.

(** Transport along an incidence-preserving pair of bijections: swapping the two vertices. *)
Example three_parallel_swap :
  mcubic three_parallel ->
  mcubic three_parallel.
Proof.
apply: (@mregular_bij three_parallel three_parallel (@rev_ord 2) id).
- by exists (@rev_ord 2); exact: rev_ordK.
- by exists id.
- by move=> x e; rewrite !three_parallel_incident.
Qed.

Print Assumptions three_parallel_loopless_cubic.
Print Assumptions three_loops_mcubic.
Print Assumptions three_loops_not_loopless_cubic.
Print Assumptions void_regular.
