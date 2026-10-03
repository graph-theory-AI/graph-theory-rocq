(** Downstream use of the edges traversed by a vertex sequence
    ([GTBase.walks_paths]: [seq_edge_list], [seq_edge_set], [seq_index_edge_set]),
    without corpus imports.  Each example uses public API lemmas only. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RawSequences.
Variable T : finType.
Implicit Types (s : seq T) (x y : T).

(** The ordered list keeps every traversal; its support keeps each edge once. *)
Example list_keeps_repetitions x y :
  seq_edge_list [:: x; y; x] = [:: [set x; y]; [set x; y]] /\
  seq_edge_set [:: x; y; x] = [set [set x; y]].
Proof. by split; [exact: seq_edge_list_back | exact: seq_edge_set_back]. Qed.

(** A repeated entry gives a one-vertex set; there is no irreflexivity filter. *)
Example repeated_entry x : seq_edge_list [:: x; x] = [:: [set x]].
Proof. exact: seq_edge_list_loop. Qed.

(** Degenerate sequences have no edge. *)
Example no_edge_on_short_sequences x :
  seq_edge_set ([::] : seq T) = set0 /\ seq_edge_set [:: x] = set0.
Proof. by split; [exact: seq_edge_set_nil | exact: seq_edge_set_seq1]. Qed.

(** One entry per consecutive pair, and at most that many distinct edges. *)
Example sizes s : size (seq_edge_list s) = (size s).-1 /\ #|seq_edge_set s| <= (size s).-1.
Proof. by split; [exact: size_seq_edge_list | exact: card_seq_edge_set]. Qed.

(** Reversal reverses the list and keeps the support. *)
Example reversal s :
  seq_edge_list (rev s) = rev (seq_edge_list s) /\ seq_edge_set (rev s) = seq_edge_set s.
Proof. by split; [exact: seq_edge_list_rev | exact: seq_edge_set_rev]. Qed.

(** The support is also the existential image of the consecutive pairs. *)
Example support_as_image s :
  seq_edge_set s =
  [set e : {set T} | [exists xy : T * T, (xy \in zip s (behead s)) && (e == [set xy.1; xy.2])]].
Proof. exact: seq_edge_set_image. Qed.

End RawSequences.

Section Graphs.
Variable G : sgraph.
Implicit Types (p : seq G) (x y : G).

(** Only a walk puts the listed pairs in the edge set. *)
Example walk_edges_are_edges p : sorted (--) p -> seq_edge_set p \subset E(G).
Proof. exact: seq_edge_set_sorted. Qed.

Example packaged_path_edges x y (q : Path x y) : seq_edge_set (nodes q) \subset E(G).
Proof. exact: seq_edge_set_nodes. Qed.

(** A non-adjacent pair: listed by the raw support, dropped by the first-index set. *)
Example nonedge x y :
  ~~ x -- y -> seq_edge_set [:: x; y] = [set [set x; y]] /\ seq_index_edge_set [:: x; y] = set0.
Proof. by move=> nxy; split; [exact: seq_edge_set_pair | exact: seq_index_edge_set_nonedge]. Qed.

(** The first-index set always consists of edges, and it is the raw support
    on duplicate-free walks, in particular on simple paths. *)
Example first_index_edges p : seq_index_edge_set p \subset E(G).
Proof. exact: seq_index_edge_set_sub. Qed.

Example first_index_on_simple_paths p :
  seq_simple_path p -> seq_index_edge_set p = seq_edge_set p.
Proof. exact: seq_index_edge_set_simple_path. Qed.

End Graphs.

(** With a repeated vertex the two differ, in [K_3] on [[:: 0; 1; 0; 2]]. *)
Example first_index_misses_a_repeated_traversal :
  [set (@Ordinal 3 0 isT); (@Ordinal 3 2 isT)] \in
    seq_edge_set [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 0 isT; @Ordinal 3 2 isT] /\
  [set (@Ordinal 3 0 isT); (@Ordinal 3 2 isT)] \notin
    seq_index_edge_set (G := 'K_3)
      [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 0 isT; @Ordinal 3 2 isT].
Proof. by split; [exact: seq_edge_set_ground_repeat | exact: seq_index_edge_set_ground_repeat]. Qed.

Print Assumptions first_index_on_simple_paths.
Print Assumptions first_index_misses_a_repeated_traversal.
