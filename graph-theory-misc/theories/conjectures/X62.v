(** * GTMisc.conjectures.X62 -- v2 rainbow path cover row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import X14.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X62 vocabulary ************************************************)

Definition x62_edges_covered_by_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall e : {set G},
    e \in x14_edge_set G ->
    exists p : seq G, p \in paths /\ e \in x14_path_edges p.

(** ** X62 statements ******************************************************)

(** Corpus row: arxiv:2301.08707#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2301.08707__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2301.08707__01.json
    English statement: (Bonamy, Botler, Dross, Naia and Skokan 2023, "Separating the edges of a
      graph by a linear number of paths", Problem 4)
      There is a constant c such that every finite simple graph G with a proper edge colouring
      admits at most c * |V(G)| rainbow paths whose edges together cover every edge of G.
    Definitions: [x62_edges_covered_by_paths paths] - every edge of G occurs among the edges of
      some listed path (this file); [x14_edge_set G] - the edges of G as two-element vertex
      sets; [x14_path_edges p] - the edges of a vertex sequence;
      [x14_proper_edge_colouring col] - distinct edges that meet receive distinct colours;
      [x14_rainbow_path col p] - a simple path whose edge colours are pairwise distinct (all
      four from graph-theory-misc/theories/conjectures/X14.v).
    Notes: the source writes O(|V(G)|); the Rocq body fixes the implied constant c before the
      graph, which is the intended uniform reading.  Colours range over an arbitrary [finType],
      so no bound on the number of colours is imposed; the source's "properly edge-coloured
      graph" is exactly this hypothesis. *)
Definition rainbow_paths_linear_edge_cover_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (C : finType) (col : {set G} -> C),
      x14_proper_edge_colouring col ->
      exists paths : seq (seq G),
        size paths <= c * #|G| /\
        (forall p : seq G, p \in paths -> x14_rainbow_path col p) /\
        x62_edges_covered_by_paths paths.
