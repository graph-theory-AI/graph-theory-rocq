(** Downstream use of longest genuine cycles ([GTBase.walks_paths.seq_longest_cycle]), without corpus
    imports.  Each example uses public API lemmas only. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnyRelation.
Variables (T : eqType) (r : rel T).
Implicit Types (c d : seq T) (x y : T).

(** Empty, one-entry and two-entry sequences are never longest cycles. *)
Example degenerate_rejected x y :
  [/\ ~ seq_longest_cycle r [::], ~ seq_longest_cycle r [:: x] & ~ seq_longest_cycle r [:: x; y]].
Proof.
by split; [exact: seq_longest_cycle_nil | exact: seq_longest_cycle_seq1 | exact: seq_longest_cycle_pair].
Qed.

(** A longest cycle is a duplicate-free genuine cycle of more than two entries, and no genuine cycle,
    nor any [ucycle], is longer. *)
Example projections c d :
  seq_longest_cycle r c ->
  [/\ uniq c, 2 < size c, (seq_cycle r d -> size d <= size c) & (ucycle r d -> size d <= size c)].
Proof.
move=> lc; split; [exact: seq_longest_cycle_uniq lc | exact: seq_longest_cycle_size lc |
  exact: seq_longest_cycle_max lc | exact: seq_longest_cycle_max_ucycle lc].
Qed.

(** Ties: two longest cycles have the same length. *)
Example ties c d : seq_longest_cycle r c -> seq_longest_cycle r d -> size c = size d.
Proof. exact: seq_longest_cycle_size_eq. Qed.

(** Rotation keeps a longest cycle. *)
Example rotation n c : seq_longest_cycle r (rot n c) <-> seq_longest_cycle r c.
Proof. exact: seq_longest_cycle_rot. Qed.

(** Reversal: of the converse relation in general ... *)
Example reversal_converse c : seq_longest_cycle r (rev c) <-> seq_longest_cycle (fun x y => r y x) c.
Proof. exact: seq_longest_cycle_rev_converse. Qed.

(** ... and without any genuine cycle there is no longest cycle. *)
Example none_without_cycle : (forall d, ~ seq_cycle r d) -> forall c, ~ seq_longest_cycle r c.
Proof. exact: seq_longest_cycle_none. Qed.

End AnyRelation.

(** For a symmetric relation, reversal stays in the same relation, as for simple-graph adjacency. *)
Example undirected_reversal (G : sgraph) (c : seq G) :
  seq_longest_cycle (@edge_rel G) (rev c) <-> seq_longest_cycle (@edge_rel G) c.
Proof. by apply: seq_longest_cycle_rev; exact: sg_sym. Qed.

(** On a finite carrier a longest cycle exists exactly when a genuine cycle does. *)
Example conditional_existence (T : finType) (r : rel T) :
  (exists c, seq_longest_cycle r c) <-> (exists c, seq_cycle r c).
Proof. exact: seq_longest_cycle_existsP. Qed.

(** Concrete corners: the triangle of [K_3] is longest; a triangle of [K_4] is a genuine cycle that is
    not longest. *)
Example K3_triangle_longest :
  seq_longest_cycle (@edge_rel 'K_3) [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT].
Proof. by case: seq_longest_cycle_ground_K3. Qed.

Example K4_triangle_not_longest :
  ~ seq_longest_cycle (@edge_rel 'K_4) [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 2 isT].
Proof. by case: seq_longest_cycle_ground_K4_triangle. Qed.

Print Assumptions undirected_reversal.
Print Assumptions conditional_existence.
Print Assumptions K4_triangle_not_longest.
