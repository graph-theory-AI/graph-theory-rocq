(** Downstream use of the edges of a cyclic sequence ([GTBase.walks_paths]:
    [seq_cycle_edge_list], [seq_cycle_edge_set], [seq_cycle_graph_edge_set] and
    [seq_next_edge_set]), without corpus imports.  Each example uses public API
    lemmas only. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AnySequence.
Variable T : finType.
Implicit Types (c s : seq T) (x y : T).

(** The list keeps one entry per position, the closing pair included. *)
Example list_closing x s :
  seq_cycle_edge_list (x :: s) = rcons (seq_edge_list (x :: s)) [set last x s; x].
Proof. exact: seq_cycle_edge_list_rcons. Qed.

(** Degenerate sequences: a loop for one entry, the pair twice for two. *)
Example short_lists x y :
  [/\ seq_cycle_edge_list ([::] : seq T) = [::], seq_cycle_edge_list [:: x] = [:: [set x]]
    & seq_cycle_edge_list [:: x; y] = [:: [set x; y]; [set x; y]]].
Proof.
by split; [exact: seq_cycle_edge_list_nil | exact: seq_cycle_edge_list_seq1 |
  exact: seq_cycle_edge_list_pair].
Qed.

(** Rotation and reversal: the list only up to permutation, the support exactly. *)
Example rotation_reversal n c :
  [/\ perm_eq (seq_cycle_edge_list (rot n c)) (seq_cycle_edge_list c),
      seq_cycle_edge_set (rot n c) = seq_cycle_edge_set c
    & seq_cycle_edge_set (rev c) = seq_cycle_edge_set c].
Proof.
by split; [exact: perm_seq_cycle_edge_list_rot | exact: seq_cycle_edge_set_rot |
  exact: seq_cycle_edge_set_rev].
Qed.

(** The successor image lies in the support, and equals it without repetitions. *)
Example image_support c :
  seq_next_edge_set c \subset seq_cycle_edge_set c /\
  (uniq c -> seq_next_edge_set c = seq_cycle_edge_set c).
Proof. by split; [exact: seq_next_edge_set_sub | exact: seq_next_edge_set_uniq]. Qed.

End AnySequence.

Section SimpleGraph.
Variable G : sgraph.
Implicit Types (c : seq G) (x y : G).

(** The actual edges are the support restricted to [E(G)]; a closed walk needs no
    filter, and a genuine cycle makes all four representations agree. *)
Example actual_edges c :
  [/\ seq_cycle_graph_edge_set c = seq_cycle_edge_set c :&: E(G),
      cycle (--) c -> seq_cycle_graph_edge_set c = seq_cycle_edge_set c
    & ucycle (--) c -> seq_next_edge_set c = seq_cycle_graph_edge_set c].
Proof.
by split; [exact: seq_cycle_graph_edge_setE | exact: seq_cycle_graph_edge_set_cycle |
  exact: seq_next_edge_set_ucycle].
Qed.

(** A loop or a non-edge contributes no actual edge. *)
Example no_actual_edge x y :
  seq_cycle_graph_edge_set [:: x] = set0 /\
  (~~ x -- y -> seq_cycle_graph_edge_set [:: x; y] = set0).
Proof. by split; [exact: seq_cycle_graph_edge_set_seq1 | exact: seq_cycle_graph_edge_set_nonedge]. Qed.

End SimpleGraph.

(** Concrete corner: on the closed walk [0, 1, 0, 2, 3] of [K_4] the successor
    image misses the edge [{0, 2}]. *)
Example first_occurrence_corner :
  [set @Ordinal 4 0 isT; @Ordinal 4 2 isT] \notin
    seq_next_edge_set [:: @Ordinal 4 0 isT; @Ordinal 4 1 isT; @Ordinal 4 0 isT;
                          @Ordinal 4 2 isT; @Ordinal 4 3 isT].
Proof. exact: seq_cycle_edges_ground_repeat_next. Qed.

Print Assumptions actual_edges.
Print Assumptions first_occurrence_corner.
