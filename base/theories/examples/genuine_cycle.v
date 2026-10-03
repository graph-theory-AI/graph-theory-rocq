(** Downstream use of genuine cycles of a sequence ([GTBase.walks_paths]:
    [seq_cycle] and [seq_cycleb]), without corpus imports.  Each example uses
    public API lemmas only. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnyRelation.
Variables (T : eqType) (r : rel T).
Implicit Types (c : seq T) (x y z : T).

(** The Boolean and Prop forms agree. *)
Example bool_prop_forms c : reflect (seq_cycle r c) (seq_cycleb r c).
Proof. exact: seq_cycleP. Qed.

(** Short sequences are never cycles, even with loops or two-way pairs in [r]. *)
Example short_sequences_excluded x y :
  [/\ ~ seq_cycle r [::], ~ seq_cycle r [:: x] & ~ seq_cycle r [:: x; y]].
Proof. by split; [exact: seq_cycle_nil | exact: seq_cycle_seq1 | exact: seq_cycle_pair]. Qed.

(** A triangle, read around its closing pair. *)
Example triangle x y z :
  seq_cycle r [:: x; y; z] <-> [/\ uniq [:: x; y; z], r x y, r y z & r z x].
Proof. exact: seq_cycle_triangle. Qed.

(** Repeated entries are excluded and rotations are cycles. *)
Example repeats_and_rotation c n :
  (~~ uniq c -> ~ seq_cycle r c) /\ (seq_cycle r (rot n c) <-> seq_cycle r c).
Proof. by split; [exact: seq_cycle_repeat | exact: seq_cycle_rot]. Qed.

(** Reversal gives a cycle of the converse relation. *)
Example reversal_converse c : seq_cycle r (rev c) <-> seq_cycle (fun x y => r y x) c.
Proof. exact: seq_cycle_rev_converse. Qed.

End AnyRelation.

(** For a symmetric relation, such as the adjacency of a simple graph, reversal
    keeps cycles. *)
Example undirected_reversal (G : sgraph) (c : seq G) :
  seq_cycle (@edge_rel G) (rev c) <-> seq_cycle (@edge_rel G) c.
Proof. by apply: seq_cycle_rev; exact: sg_sym. Qed.

(** Concrete corners: the triangle of [K_3] is a cycle; a directed 3-cycle does not
    reverse. *)
Example concrete_corners :
  seq_cycle (@edge_rel 'K_3) [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT].
Proof. exact: seq_cycle_ground_K3. Qed.

Print Assumptions undirected_reversal.
Print Assumptions concrete_corners.
