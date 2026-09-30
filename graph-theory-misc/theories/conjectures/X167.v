(** * GTMisc.conjectures.X167 -- v2 spanning-tree polytope fixed-surface row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X167 vocabulary ***********************************************)

Definition x167_embedded_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x167_spanning_tree (G : sgraph) (T : {set {set G}}) : Prop :=
  T \subset fg_edges G /\
  is_tree [set: fg_labelled_sgraph T].

Record x167_extension_system (G : sgraph) (facets : nat) := {
  x167_aux_dim : nat;
  x167_ineq_index : finType;
  x167_ineq_count : #|{: x167_ineq_index}| <= facets;
  x167_accepts_tree : forall T : {set {set G}}, x167_spanning_tree T -> True;
  x167_rejects_non_tree : forall T : {set {set G}}, ~ x167_spanning_tree T -> True
}.

Definition x167_spanning_tree_polytope_xc (G : sgraph) (facets : nat) : Prop :=
  exists _ : x167_extension_system G facets, True.

(** ** X167 statements *****************************************************)

(** Corpus row: arxiv:1604.07976#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1604.07976__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1604.07976__00.json
    English statement: (Fiorini, Huynh, Joret and Pashkovich 2016, "Smaller Extended
      Formulations for the Spanning Tree Polytope of Bounded-genus Graphs", Conjecture 1)
      For every surface, i.e. every Euler-genus bound, there is a constant C such that every
      connected finite simple graph G embeddable in that surface admits an extension system for
      its spanning-tree polytope with at most C * (|V(G)| + 1) inequalities; that is, the
      extension complexity of the spanning-tree polytope is O(|V(G)|).
    Definitions: [x167_embedded_in_fixed_surface surface G] - G embeds in a surface of Euler
      genus at most the given bound, via [surface_embeddable] (this file, GTBase surface.v);
      [x167_spanning_tree G T] - T is a set of edges of G whose labelled graph is a tree (this
      file); [x167_extension_system G facets] - a record carrying an auxiliary dimension, a
      finite index of inequalities of cardinality at most [facets], and two linking fields
      (this file); [x167_spanning_tree_polytope_xc G facets] - such a record exists (this
      file); [fg_edges], [fg_labelled_sgraph] - edges as two-element vertex sets and the graph
      of such a set (GTBase finite_graph.v); [is_tree], [connected] - coq-graph-theory.
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  Extension complexity - the least number of facets of
      a higher-dimensional polyhedron projecting onto the spanning-tree polytope - is not
      modelled: the two linking fields [x167_accepts_tree] and [x167_rejects_non_tree] have
      conclusion [True], so they constrain nothing, and the only real field is the cardinality
      bound on an index type, which an empty index satisfies for every value of [facets].  The
      statement is therefore vacuously provable and carries no polytope content.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition fixed_surface_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall surface : nat,
    exists C : nat,
      forall G : sgraph,
        connected [set: G] ->
        x167_embedded_in_fixed_surface surface G ->
        x167_spanning_tree_polytope_xc G (C * #|G|.+1).
