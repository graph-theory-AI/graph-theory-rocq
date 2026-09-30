(** * GTMisc.conjectures.X172 -- v2 Chen-Chvatal bridge-replacement row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X172 vocabulary ***********************************************)

Definition x172_path_edges (G : sgraph) (s : seq G) : {set {set G}} :=
  [set e in [seq [set p.1; p.2] | p <- zip s (behead s)]].

Definition x172_path_internal (G : sgraph) (s : seq G) : {set G} :=
  [set x : G | (x \in s) && (x != head x s) && (x != last x s)].

Definition x172_one_bridge_replacement (G H : sgraph) : Prop :=
  exists (a b : G) (f : G -> H) (p : seq H),
    a != b /\
    graph_bridge [set a; b] /\
    injective f /\
    path (--) (f a) p /\
    last (f a) p = f b /\
    uniq (f a :: p) /\
    [disjoint x172_path_internal (f a :: p)
     & [set y : H | [exists x : G, f x == y]]] /\
    (forall x y : G,
      [set x; y] != [set a; b] ->
      (x -- y <-> f x -- f y)) /\
    forall u v : H,
      u -- v ->
      ([set u; v] \in x172_path_edges (f a :: p)) \/
      (exists x y : G,
        [set x; y] != [set a; b] /\
        x -- y /\
        u = f x /\
        v = f y).

Inductive x172_generated_by_bridge_replacement : sgraph -> sgraph -> Prop :=
| x172_generated_refl G :
    x172_generated_by_bridge_replacement G G
| x172_generated_step G H K :
    x172_one_bridge_replacement G H ->
    x172_generated_by_bridge_replacement H K ->
    x172_generated_by_bridge_replacement G K.

Definition x172_counterexample_to_lines_bridges_bound (G : sgraph) : Prop :=
  connected [set: G] /\ metric_line_count G + bridge_count G < #|G|.

(** ** X172 statements *****************************************************)

(** Corpus row: arxiv:1606.06011#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1606.06011__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1606.06011__01.json
    English statement: (Aboulker, Matamala, Rochet and Zamora 2016, "A new class of graphs that
      satisfies the Chen-Chvatal Conjecture", open question on counter-examples)
      There is a bound B such that every connected finite simple graph G with
      l(G) + br(G) < |V(G)| is obtained from some graph with at most B vertices by finitely
      many steps, each replacing one bridge by a path of arbitrary length.
    Definitions: [x172_path_edges s] / [x172_path_internal s] - the edge set and the internal
      vertices of a vertex sequence (this file); [x172_one_bridge_replacement G H] - H arises
      from G by picking a bridge ab, embedding V(G) injectively into V(H) and replacing that
      bridge by a path from the image of a to the image of b whose internal vertices are new,
      all other adjacencies being preserved and no other edges of H existing (this file);
      [x172_generated_by_bridge_replacement] - the reflexive transitive closure of that step
      (this file); [x172_counterexample_to_lines_bridges_bound G] - G is connected and
      l(G) + br(G) < |V(G)| (this file); [metric_line_count], [bridge_count], [graph_bridge] -
      the Chen-Chvatal metric-line count, the bridge count and the bridge predicate (GTBase
      graph_metric.v).
    Notes: retargeted on 2026-07-16 from a blocked placeholder to this axiom-free finite-witness
      formulation, see meta/BLOCKED_RETARGETING_FOUNDATIONS.md.  "A finite set of graphs" is
      encoded by an order bound on the seed rather than by an explicit finite family, which is
      equivalent up to the fact that finitely many graphs of bounded order exist for each
      bound.  The source phrases the question as "it remains unknown whether"; the Rocq body is
      the positive answer. *)
Definition metric_lines_bridges_counterexamples_finitely_generated_statement : Prop :=
  exists finite_seed_bound : nat,
    forall G : sgraph,
      x172_counterexample_to_lines_bridges_bound G ->
      exists seed : sgraph,
        #|seed| <= finite_seed_bound /\
        x172_generated_by_bridge_replacement seed G.
