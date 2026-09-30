(** * Packing.conjectures.X47 -- v2 tree edge-decomposition row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X47 vocabulary ************************************************)

Definition x47_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x47_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x47_crossing_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in x47_edge_set G | (e :&: S != set0) && (e :&: (~: S) != set0)].

Definition x47_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 ->
    S != [set: G] ->
    k <= #|x47_crossing_edges S|.

Definition x47_copy_edge_set
    (G T : sgraph) (F : {set {set G}}) : Prop :=
  exists f : T -> G,
    injective f /\
    F = [set e : {set G} |
          [exists x : T, [exists y : T, (x -- y) && (e == [set f x; f y])]]].

Definition x47_tree_decomposition_by_copies (G T : sgraph) : Prop :=
  exists parts : seq {set {set G}},
    (forall F : {set {set G}}, F \in parts -> @x47_copy_edge_set G T F) /\
    (forall F : {set {set G}}, F \in parts -> F \subset x47_edge_set G) /\
    (forall e : {set G}, e \in x47_edge_set G ->
      exists F : {set {set G}}, F \in parts /\ e \in F) /\
    forall (F1 F2 : {set {set G}}) (e : {set G}),
      F1 \in parts -> F2 \in parts -> e \in F1 -> e \in F2 -> F1 = F2.

(** ** X47 statements ******************************************************)

(** Corpus row: arxiv:1507.08208#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1507.08208__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1507.08208__00.json
    English statement: (Bensmail, Harutyunyan, Le, Thomasse 2016, "Conjecture 1.2")
      There is a function f on natural numbers such that for every tree T and every
      simple graph G: if T has at least one edge, G is f(Delta(T))-edge-connected,
      every vertex of G has at least f(|E(T)|) neighbours, and |E(T)| divides |E(G)|,
      then the edge set of G decomposes into copies of T.
    Definitions: [x47_edge_set G] — the two-element vertex sets {x, y} with x -- y
      (this file); [x47_min_degree_at_least G d] — every vertex has at least d
      neighbours (this file); [x47_crossing_edges S] — the edges with an endpoint in S
      and an endpoint outside (this file); [x47_edge_connected G k] — every nonempty
      proper vertex set has at least k crossing edges (this file);
      [x47_copy_edge_set G T F] — F is the image edge set of an injection of V(T) into
      V(G) mapping every edge of T to a pair of F (this file);
      [x47_tree_decomposition_by_copies G T] — a list of such copies, all contained in
      E(G), covering every edge of G, with any two parts sharing an edge being equal
      (this file); [is_tree] — coq-graph-theory sgraph.v; [Delta] — GTBase base.
    Notes: the corpus row is DISPROVED (Klimosova and Thomasse, arXiv:1803.03704: no
      such f exists already for complete binary trees, of maximum degree 3); the body
      states the conjecture, not its refutation. Edge-connectivity is encoded as a
      cut-size condition on vertex sets rather than through edge deletions.
      Edge-disjointness of the parts is expressed as "two parts sharing an edge are
      equal", so repeated identical parts in the list are not excluded. *)
Definition tree_decomposition_delta_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (Delta T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.
