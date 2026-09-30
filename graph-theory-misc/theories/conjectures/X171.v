(** * GTMisc.conjectures.X171 -- v2 Chen-Chvatal graph-metric finite exceptions row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X171 vocabulary ***********************************************)

(** The Chen-Chvatal metric-line/bridge lower bound [ell(G) + br(G) >= |G|]. *)
Definition x171_metric_lines_bridges_bound (G : sgraph) : Prop :=
  #|G| <= metric_line_count G + bridge_count G.

Definition x171_has_pendant_edge (G : sgraph) : Prop :=
  exists v : G, #|N(v)| = 1.

(** ** X171 statements *****************************************************)

(** Corpus row: arxiv:1606.06011#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1606.06011__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1606.06011__00.json
    English statement: (Aboulker, Matamala, Rochet and Zamora 2016, "A new class of graphs that
      satisfies the Chen-Chvatal Conjecture", Conjecture 2.2)
      There is a bound B such that every connected finite simple graph G with more than B
      vertices either has a vertex of degree 1 or satisfies |V(G)| <= l(G) + br(G), where l(G)
      is the number of distinct metric lines of G and br(G) its number of bridges.
    Definitions: [x171_metric_lines_bridges_bound G] - the inequality
      |V(G)| <= [metric_line_count G] + [bridge_count G] (this file);
      [x171_has_pendant_edge G] - some vertex has exactly one neighbour (this file);
      [metric_line a b] - the Chen-Chvatal line through a and b in the shortest-path metric,
      i.e. the vertices collinear with a and b (GTBase graph_metric.v);
      [metric_line_count G] - the number of distinct such lines over pairs of distinct vertices
      (same file); [graph_bridge e] - an edge whose deletion disconnects its endpoints, and
      [bridge_count G] its number (same file); [connected] - coq-graph-theory.
    Notes: the source's finite exceptional set F0 is encoded by an order bound: only graphs
      with more than B vertices are required to satisfy the dichotomy, which is implied by,
      but formally weaker than, "all graphs outside a fixed finite set F0" - it does not
      constrain the finitely many small graphs at all.  Distances are the finite shortest-path
      distances of GTBase, so the metric is the graph metric and not an arbitrary one. *)
Definition finite_exception_pendant_or_metric_lines_bridges_statement : Prop :=
  exists exceptional_order_bound : nat,
    forall G : sgraph,
      connected [set: G] ->
      exceptional_order_bound < #|G| ->
      x171_has_pendant_edge G \/ x171_metric_lines_bridges_bound G.
