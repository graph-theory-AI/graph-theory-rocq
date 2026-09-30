(** * Topological.conjectures.X6 -- v2 milestone X6, clean planar induced-forest rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X6 statements *******************************************************)

(** Corpus row: studies:std_akiyama_watanabe_conjecture_induced_forest_on_5
    Site: none
    Review: none
    English statement: (Akiyama, Watanabe, studies slice)
      Every bipartite planar graph has an induced forest on at least five eighths of its
      vertices.  In the Rocq body: for every finite simple graph G with no K5 and no K3,3
      minor that is bipartite, there is a vertex set S inducing an acyclic subgraph with
      5 * |V(G)| <= 8 * |S|.
    Definitions: standard - [wagner_planar] (no K5 and no K3,3 minor) and [bipartite]
      (a 2-colouring of the vertices with no monochromatic edge), both base/theories/base.v;
      [is_forest S] - the subgraph induced on S is acyclic (coq-graph-theory sgraph.v).
    Notes: The fraction 5/8 is cross-multiplied over the naturals to avoid division, which
      makes the bound |S| >= 5n/8 exact rather than floored. *)
Definition bipartite_planar_induced_forest_five_eighths_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> bipartite G ->
    exists S : {set G}, is_forest S /\ 5 * #|G| <= 8 * #|S|.

(** Corpus row: studies:std_kowalik_lu_ar_krekovski_conjecture_induced_fores
    Site: none
    Review: none
    English statement: (Kowalik, Luzar, Skrekovski, studies slice)
      Every planar graph of girth at least five has an induced forest on at least seven
      tenths of its vertices.  In the Rocq body: for every finite simple graph G with no K5
      and no K3,3 minor in which every genuine cycle has length at least 5, there is a vertex
      set S inducing an acyclic subgraph with 7 * |V(G)| <= 10 * |S|.
    Definitions: standard - [wagner_planar] and [girth_geq G 5] (every cycle of size greater
      than 2 has length at least 5; acyclic graphs satisfy it), both base/theories/base.v;
      [is_forest S] - coq-graph-theory sgraph.v.
    Notes: The fraction 7/10 is cross-multiplied over the naturals, making the bound exact
      rather than floored.  The [2 < size c] guard inside [girth_geq] is load-bearing: without
      it the degenerate size-0 and size-2 [ucycle] artefacts would make the hypothesis
      unsatisfiable. *)
Definition girth_five_planar_induced_forest_seven_tenths_statement : Prop :=
  forall G : sgraph,
    wagner_planar G -> girth_geq G 5 ->
    exists S : {set G}, is_forest S /\ 7 * #|G| <= 10 * #|S|.
