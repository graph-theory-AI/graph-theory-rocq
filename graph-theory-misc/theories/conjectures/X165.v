(** * GTMisc.conjectures.X165 -- v2 Szeged-Wiener difference row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X165 vocabulary ***********************************************)

Definition x165_wiener_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G) graph_dist u v) %/ 2.

Definition x165_closer_count (G : sgraph) (u v : G) : nat :=
  #|[set x : G | graph_dist x u < graph_dist x v]|.

Definition x165_szeged_index (G : sgraph) : nat :=
  (\sum_(u : G) \sum_(v : G | u -- v)
      x165_closer_count u v * x165_closer_count v u) %/ 2.

Definition x165_eta (G : sgraph) : nat :=
  x165_szeged_index G - x165_wiener_index G.

Definition x165_K_n_t (G : sgraph) (n t : nat) : Prop :=
  #|G| = n /\
  exists apex : G,
    #|N(apex)| = t /\ cliqueb (~: [set apex]).

Definition x165_exceptional_family (G : sgraph) (n : nat) : Prop :=
  inhabited (G ≃ 'K_n) \/
  x165_K_n_t G n 2 \/
  x165_K_n_t G n (n - 2).

(** ** X165 statements *****************************************************)

(** Corpus row: arxiv:1602.05184#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1602.05184__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1602.05184__00.json
    English statement: (Bonamy, Knor, Luzar, Pinlou and Skrekovski 2016, "On the difference
      between the Szeged and Wiener index", Conjecture 5)
      For every n >= 10 and every 2-connected finite simple graph G on n vertices that is
      neither the complete graph nor a complete graph with one vertex of degree 2 nor one with
      a vertex of degree n-2, the difference between the Szeged index and the Wiener index of G
      is at least 2n.
    Definitions: [x165_wiener_index G] - half the sum over ordered vertex pairs of the graph
      distance (this file); [x165_closer_count u v] - the number of vertices strictly closer to
      u than to v (this file); [x165_szeged_index G] - half the sum over ordered adjacent pairs
      of the product of the two closer-counts (this file); [x165_eta G] - the Szeged index
      minus the Wiener index (this file); [x165_K_n_t G n t] - G has n vertices and a vertex of
      degree t whose removal leaves a clique (this file); [x165_exceptional_family G n] - G is
      the complete graph, or of the previous shape with t = 2, or with t = n-2 (this file);
      [k_connected G 2] - 2-connectedness (GTBase); [graph_dist] - graph distance (GTBase
      graph_metric.v); [cliqueb] - coq-graph-theory.
    Notes: retargeted on 2026-07-16 from a blocked placeholder to this axiom-free finite-witness
      formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md.  Both indices are natural
      numbers computed by truncated halving of the ordered-pair sums, and eta uses truncated
      subtraction, so eta is 0 rather than negative should the Szeged index be smaller; this is
      harmless here because the Szeged index dominates the Wiener index on connected graphs.
      The paper's exceptional graphs K_n^2 and K_n^(n-2) are modelled by the apex shape
      [x165_K_n_t], a vertex of the stated degree whose removal leaves a clique, rather than
      by an explicit construction. *)
Definition szeged_wiener_difference_exceptional_graphs_statement : Prop :=
  forall (n : nat) (G : sgraph),
    10 <= n ->
    #|G| = n ->
    k_connected G 2 ->
    ~ x165_exceptional_family G n ->
    2 * n <= x165_eta G.
