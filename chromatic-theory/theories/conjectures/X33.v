(** * Chromatic.conjectures.X33 -- v2 total list-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X33 vocabulary ************************************************)

Definition x33_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x33_total_vertex (G : sgraph) : Type :=
  (G + {e : {set G} | e \in x33_edge_set G})%type.

Definition x33_total_rel (G : sgraph) : rel (x33_total_vertex G) :=
  fun a b =>
    match a, b with
    | inl x, inl y => x -- y
    | inr e, inr f => (val e != val f) && (val e :&: val f != set0)
    | inl x, inr e => x \in val e
    | inr e, inl x => x \in val e
    end.

Lemma x33_total_rel_sym (G : sgraph) : symmetric (@x33_total_rel G).
Proof.
move=> [x|e] [y|f] //=.
- by rewrite sg_sym.
- by rewrite eq_sym setIC.
Qed.

Lemma x33_total_rel_irrefl (G : sgraph) : irreflexive (@x33_total_rel G).
Proof. by move=> [x|e] //=; rewrite ?sg_irrefl ?eqxx. Qed.

Definition x33_total_graph (G : sgraph) : sgraph :=
  SGraph (@x33_total_rel_sym G) (@x33_total_rel_irrefl G).

(** ** X33 statements ******************************************************)

(** Corpus row: arxiv:1904.12060#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1904.12060__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1904.12060__00.json
    English statement: (Bonamy, Pierron and Sopena 2022, Conjecture 5, the list analogue of the Total Colouring Conjecture, arXiv:1904.12060)
      Every finite simple graph G is totally (Delta(G)+2)-choosable: the total graph of G, whose
      vertices are the vertices and the edges of G, is (Delta(G)+2)-choosable, so for every
      assignment of lists of at least Delta(G)+2 colours to vertices and edges there is a colouring
      from the lists giving different colours to adjacent vertices, to adjacent edges, and to a
      vertex and an edge incident with it.
    Definitions: [x33_total_graph G] - the total graph of a SIMPLE graph, built on the sum of the
      vertex type and the edge type where edges are 2-element vertex sets, with the three adjacency
      cases vertex-vertex, edge-edge sharing an endpoint, and vertex-edge incidence (this file);
      [x33_edge_set G] (this file); [choosable G k] (GTBase base/theories/base.v); [Delta] (base.v).
    Notes: This file builds its own total graph on [sgraph] rather than reusing base's multigraph
      [total_graph], because the source conjecture is about simple graphs. [choosable] requires
      lists of size at least Delta+2, equivalent to lists of size exactly Delta+2. *)
Definition total_list_colouring_delta_plus_two_statement : Prop :=
  forall G : sgraph,
    choosable (x33_total_graph G) (Delta G + 2).
