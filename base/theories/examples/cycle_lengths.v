(** Downstream use of the cycle-length predicates of a sequence relation ([GTBase.walks_paths]:
    [has_ucycle_length], [has_cycle_length], [no_ucycle_length_between], [no_cycle_length_between]
    and [no_cycle_length]), without corpus imports.  Each example uses public API lemmas only; the
    negative examples are stated explicitly. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnyRelation.
Variables (T : eqType) (r : rel T).
Implicit Types (n lo hi : nat) (x y : T).

(** Raw length 0 is always witnessed, by the empty [ucycle]; genuine lengths at most 2 never are. *)
Example raw_zero_genuine_small n : has_ucycle_length r 0 /\ (n <= 2 -> ~ has_cycle_length r n).
Proof. by split; [exact: has_ucycle_length0 | exact: has_cycle_length_le2]. Qed.

(** Raw length 1 is a loop; raw length 2 is a two-way pair of distinct entries. *)
Example raw_one_two :
  (has_ucycle_length r 1 <-> exists x, r x x) /\
  (has_ucycle_length r 2 <-> exists x y, [/\ x != y, r x y & r y x]).
Proof. by split; [exact: has_ucycle_length1 | exact: has_ucycle_length2]. Qed.

(** The genuine view is reached only through the explicit guard [2 < n]. *)
Example guarded_bridge n : 2 < n -> (has_ucycle_length r n <-> has_cycle_length r n).
Proof. exact: has_ucycle_lengthE. Qed.

(** Interval exclusions are the negation of every exact length in the inclusive interval. *)
Example interval_duality lo hi :
  (no_ucycle_length_between r lo hi <-> forall n, lo <= n -> n <= hi -> ~ has_ucycle_length r n) /\
  (no_cycle_length_between r lo hi <-> forall n, lo <= n -> n <= hi -> ~ has_cycle_length r n).
Proof. by split; [exact: no_ucycle_length_betweenP | exact: no_cycle_length_betweenP]. Qed.

(** NEGATIVE: an interval containing 0 is never raw-excluded; reversed intervals are vacuous. *)
Example zero_and_reversed hi lo :
  ~ no_ucycle_length_between r 0 hi /\ (hi < lo -> no_ucycle_length_between r lo hi).
Proof. by split; [exact: no_ucycle_length_between0 | exact: no_ucycle_length_between_rev]. Qed.

(** Raw exclusion implies genuine exclusion; the converse needs the explicit guard [2 < lo]. *)
Example interval_bridge lo hi :
  (no_ucycle_length_between r lo hi -> no_cycle_length_between r lo hi) /\
  (2 < lo -> (no_ucycle_length_between r lo hi <-> no_cycle_length_between r lo hi)).
Proof. by split; [exact: no_ucycle_length_between_cycle | exact: no_ucycle_length_betweenE]. Qed.

(** Exact absence: the interval at identical endpoints, the negation of existence, and the Boolean
    disequality read as a proposition. *)
Example exact_absence n :
  [/\ no_cycle_length r n <-> no_cycle_length_between r n n,
      no_cycle_length r n <-> ~ has_cycle_length r n
    & no_cycle_length r n <-> forall c, seq_cycle r c -> size c <> n].
Proof. by split; [exact: no_cycle_lengthE | exact: no_cycle_lengthP | exact: no_cycle_length_neq]. Qed.

End AnyRelation.

(** Simple graphs: no raw length 1; raw length 2 exactly with an edge, which a raw interval
    containing 2 therefore excludes (NEGATIVE for the raw exclusion). *)
Example sgraph_small_lengths (G : sgraph) (x y : G) :
  ~ has_ucycle_length (@edge_rel G) 1 /\
  (has_ucycle_length (@edge_rel G) 2 <-> exists x y : G, x -- y) /\
  (x -- y -> ~ no_ucycle_length_between (@edge_rel G) 2 5).
Proof.
split; [exact: has_ucycle_length1_sgraph | split; first exact: has_ucycle_length2_sgraph].
move=> xy; apply: (@no_ucycle_length_between_pair _ _ _ _ x y) => //.
  by rewrite (sg_edgeNeq xy).
by rewrite sg_sym.
Qed.

(** Concrete corners on [K_2] and [K_3]. *)
Example K2_corners :
  [/\ has_ucycle_length (@edge_rel 'K_2) 2, ~ has_cycle_length (@edge_rel 'K_2) 2,
      ~ no_ucycle_length_between (@edge_rel 'K_2) 2 2 & no_cycle_length_between (@edge_rel 'K_2) 2 2].
Proof. exact: cycle_lengths_ground_K2. Qed.

Example K3_corners :
  [/\ has_cycle_length (@edge_rel 'K_3) 3, ~ has_ucycle_length (@edge_rel 'K_3) 4,
      no_ucycle_length_between (@edge_rel 'K_3) 4 6, no_cycle_length (@edge_rel 'K_3) 5
    & no_ucycle_length_between (@edge_rel 'K_3) 3 2].
Proof. exact: cycle_lengths_ground_K3. Qed.

Print Assumptions sgraph_small_lengths.
Print Assumptions K3_corners.
