(** * GTMisc.conjectures.X169 -- v2 token-sliding chordal algorithm row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X169 vocabulary ***********************************************)

Definition x169_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  is_tree [set: T] /\
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).

Definition x169_clique_tree (G T : sgraph) (bag : T -> {set G}) : Prop :=
  x169_tree_decomposition bag /\ forall t : T, cliqueb (bag t).

Definition x169_chordal (G : sgraph) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}), x169_clique_tree bag.

Definition x169_clique_tree_degree_at_most (G : sgraph) (D : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    x169_clique_tree bag /\ forall t : T, #|N(t)| <= D.

Definition x169_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x169_ts_step (G : sgraph) (k : nat) : rel {set G} :=
  fun A B =>
    [exists a in A,
      [exists b : G,
        [&& b \notin A, a -- b, #|A| == k, #|B| == k &
            B == (A :\ a) :|: [set b]]]].

Definition x169_token_sliding_connected (G : sgraph) (k : nat) : Prop :=
  forall A B : {set G},
    x169_stable_set A -> #|A| = k ->
    x169_stable_set B -> #|B| = k ->
    exists p : seq {set G}, path (x169_ts_step k) A p /\ last A p = B.

Definition x169_polytime_decides_TS_connectivity (k D : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x169_chordal G /\ x169_clique_tree_degree_at_most G D)
    (fun G : sgraph => x169_token_sliding_connected G k).

(** ** X169 statements *****************************************************)

(** Corpus row: arxiv:1605.00442#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1605.00442__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1605.00442__00.json
    English statement: (Bonamy and Bousquet 2016, "Token Sliding on Chordal Graphs",
      Question 1)
      For all k and D there is a program with polynomially bounded step count that decides, for
      every chordal graph of clique-tree degree at most D given by its adjacency matrix,
      whether any two k-element stable sets can be transformed into one another by a sequence
      of single-token slides along edges.
    Definitions: [x169_tree_decomposition bag] - the bags cover every vertex and every edge and
      each vertex occupies a connected part of the tree (this file); [x169_clique_tree bag] -
      a tree decomposition all of whose bags are cliques (this file); [x169_chordal G] - some
      clique tree exists (this file); [x169_clique_tree_degree_at_most G D] - some clique tree
      has all node degrees at most D (this file); [x169_stable_set S] - S is stable (this
      file); [x169_ts_step k] - a one-token slide between k-element vertex sets: one element is
      replaced by an adjacent vertex outside the set (this file);
      [x169_token_sliding_connected G k] - all k-element stable sets are joined by slide paths
      (this file); [polytime_decides_graph_on Class P] - some [prog] with polynomially bounded
      step count decides P on the adjacency-matrix encoding of every graph in Class (GTBase
      complexity.v, via [poly_cost_on] and [decides_on_class]).
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The decided predicate is not TS_k connectivity:
      [x169_ts_step] constrains only the cardinality, the replaced element, the adjacency and
      the resulting set, and never requires the INTERMEDIATE sets along the path to be stable.
      Intermediate independence is the defining constraint of token sliding of independent sets
      and the sole source of the problem's hardness, so the formalized predicate is a different
      and much weaker reachability notion.  The corpus row is disproved (Adak, Nanoti and Tale,
      arXiv:2502.12749), but the disproof concerns the true predicate.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition token_sliding_chordal_clique_tree_degree_polytime_statement : Prop :=
  forall k D : nat, x169_polytime_decides_TS_connectivity k D.
