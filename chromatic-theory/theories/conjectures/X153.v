(** * Chromatic.conjectures.X153 -- v2 planar girth-5 list-critical subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X153 vocabulary ***********************************************)

Definition x153_cycle_vertices (G : sgraph) (c : seq G) : {set G} :=
  [set v | v \in c].

Definition x153_short_cycle (G : sgraph) (k : nat) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\ size c <= k.

Definition x153_cycle_precoloured_lists
    (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G) : Prop :=
  forall v : G,
    if v \in x153_cycle_vertices c1 :|: x153_cycle_vertices c2
    then #|L v| = 1
    else 3 <= #|L v|.

Definition x153_list_colourable_induced
    (G : sgraph) (C : finType) (L : G -> {set C}) (S : {set G}) : Prop :=
  @list_colourable (induced S) C (fun v : induced S => L (val v)).

(** ** X153 statements *****************************************************)

(** Corpus row: arxiv:1302.2158#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1302.2158__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1302.2158__00.json
    English statement: (Dvorak, Kral and Thomas 2017, Conjecture 1.7, arXiv:1302.2158)
      For every integer k >= 5 there exists an integer K such that, for every planar finite simple
      graph G of girth at least five, every two cycles c1 and c2 of G of length at most k, and every
      list assignment giving a single colour to each vertex of c1 and c2 and at least three colours
      to all other vertices, if G has no proper colouring from the lists then some vertex set S of
      at most K vertices contains all vertices of c1 and of c2 and the subgraph induced on S already
      has no proper colouring from the lists.
    Definitions: [x153_short_cycle k c] - c is a [ucycle] with more than 2 and at most k vertices
      (this file); [x153_cycle_vertices c] - the vertex set of the listed cycle (this file);
      [x153_cycle_precoloured_lists L c1 c2] - lists of size exactly 1 on the vertices of the two
      cycles and of size at least 3 elsewhere (this file); [x153_list_colourable_induced L S] - the
      induced subgraph on S is list-colourable for the restricted lists (this file);
      [list_colourable] (GTBase base/theories/base.v); [wagner_planar], [girth_geq] (base.v).
    Notes: The source says "subgraph H on at most K vertices"; the Rocq body uses the INDUCED
      subgraph on a vertex set of size at most K, which is equivalent for non-colourability since
      adding edges can only destroy colourings. The bound K is chosen after k and before the graph,
      as in the source. *)
Definition planar_girth5_two_cycles_list_critical_subgraph_statement : Prop :=
  forall k : nat,
    5 <= k ->
    exists K : nat,
      forall (G : sgraph) (C : finType) (L : G -> {set C}) (c1 c2 : seq G),
        wagner_planar G ->
        girth_geq G 5 ->
        x153_short_cycle k c1 ->
        x153_short_cycle k c2 ->
        x153_cycle_precoloured_lists L c1 c2 ->
        ~ @list_colourable G C L ->
        exists S : {set G},
          [/\ #|S| <= K,
              x153_cycle_vertices c1 \subset S,
              x153_cycle_vertices c2 \subset S &
              ~ x153_list_colourable_induced L S].

