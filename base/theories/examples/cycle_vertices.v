(** Downstream use of the vertex set of a cyclic sequence ([GTBase.walks_paths.seq_vertices], reused by
    the cycle-vertices family), without corpus imports.  Each example uses public API lemmas only. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnySequence.
Variable T : finType.
Implicit Types (c d : seq T) (x : T).

(** No validity premise: the empty sequence and a single entry. *)
Example short_sequences x : seq_vertices ([::] : seq T) = set0 /\ seq_vertices [:: x] = [set x].
Proof. by split; [exact: seq_vertices_nil | exact: seq_vertices_seq1]. Qed.

(** Rotation, reversal and repetitions do not change the support. *)
Example rotation_reversal_repeats n c :
  [/\ seq_vertices (rot n c) = seq_vertices c, seq_vertices (rev c) = seq_vertices c
    & seq_vertices (undup c) = seq_vertices c].
Proof. by split; [exact: seq_vertices_rot | exact: seq_vertices_rev | exact: seq_vertices_undup]. Qed.

(** Membership, and the cardinality, which equals the length exactly without repetitions. *)
Example membership_cardinality c x :
  (x \in seq_vertices c) = (x \in c) /\ (#|seq_vertices c| = size c <-> uniq c).
Proof. by split; [exact: in_seq_vertices | exact: rwP (card_seq_verticesP c)]. Qed.

(** Vertex-disjoint sequences. *)
Example disjoint_supports c d :
  reflect (forall v, v \in c -> v \notin seq_vertices d) [disjoint seq_vertices c & seq_vertices d].
Proof. exact: seq_vertices_disjointP. Qed.

End AnySequence.

(** A genuine cycle has as many vertices as entries. *)
Example genuine_cycle_card (T : finType) (r : rel T) (c : seq T) :
  seq_cycle r c -> #|seq_vertices c| = size c.
Proof. by move/seq_cycle_uniq/card_seq_verticesP. Qed.

(** Concrete corner: a repeated entry is counted once. *)
Example repeated_corner :
  seq_vertices [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 0 isT] =
  [set @Ordinal 3 0 isT; @Ordinal 3 1 isT].
Proof. exact: seq_vertices_ground_repeat. Qed.

Print Assumptions genuine_cycle_card.
Print Assumptions repeated_corner.
