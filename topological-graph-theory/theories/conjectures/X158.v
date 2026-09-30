(** * Topological.conjectures.X158 -- v2 planar queue-number row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X158 vocabulary ***********************************************)

Definition x158_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x158_edge_ordered_endpoints
    (G : sgraph) (ord : seq G) (e : {set G}) (a b : G) : Prop :=
  a \in e /\ b \in e /\ a != b /\ index a ord < index b ord.

Definition x158_nested_edges
    (G : sgraph) (ord : seq G) (e f : {set G}) : Prop :=
  exists a b c d : G,
    x158_edge_ordered_endpoints ord e a d /\
    x158_edge_ordered_endpoints ord f b c /\
    index a ord < index b ord /\
    index b ord < index c ord /\
    index c ord < index d ord.

Definition x158_queue_layout (G : sgraph) (q : nat) : Prop :=
  exists (ord : seq G) (col : {set G} -> 'I_q),
    [/\ uniq ord,
        size ord = #|G| &
        forall e f : {set G},
          e \in x158_edge_set G ->
          f \in x158_edge_set G ->
          e != f ->
          col e = col f ->
          ~ x158_nested_edges ord e f].

(** ** X158 statements *****************************************************)

(** Corpus row: arxiv:1507.01120#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1507.01120__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1507.01120__00.json
    English statement: (Joret, Micek, Wiechert 2015, arXiv:1507.01120, "Queue Number of
      Planar Graphs")
      There is a constant q such that every planar graph has a q-queue layout, i.e. a linear
      order of its vertices and a partition of its edges into q queues, no queue containing
      two nested edges.  In the Rocq body: there is a natural q such that every finite simple
      graph with no K5 and no K3,3 minor has a [x158_queue_layout] with q queues.
    Definitions: [x158_edge_set G] - the set of 2-element vertex sets that are edges (this
      file); [x158_edge_ordered_endpoints ord e a b] - a and b are the two distinct endpoints
      of e, listed in the order [ord] (this file); [x158_nested_edges ord e f] - the endpoints
      satisfy a < b < c < d in [ord] with e = {a,d} and f = {b,c}, i.e. f is nested inside e
      (this file); [x158_queue_layout G q] - an enumeration [ord] of the vertices (uniq, of
      length |G|) together with a colouring of the edge sets by q colours such that two
      distinct edges of the same colour are never nested (this file); [wagner_planar] -
      base/theories/base.v.
    Notes: The corpus row is recorded SOLVED: Dujmovic, Joret, Micek, Morin, Ueckerdt and
      Wood proved in 2019 (J. ACM 2020) that every planar graph has queue number at most 49,
      via layered partitions; the statement here is the existential "bounded queue number"
      form of the question as it was posed.  Modelling choices: edges are 2-element vertex
      sets rather than a dedicated edge type, and the queue assignment is a total map on all
      vertex SETS, of which only the values on genuine edges are constrained - harmless,
      since the nesting condition is imposed only for members of [x158_edge_set].  [index]
      on a duplicate-free enumeration of all vertices is used as the linear order. *)
Definition planar_graphs_bounded_queue_number_statement : Prop :=
  exists q : nat,
    forall G : sgraph,
      wagner_planar G -> x158_queue_layout G q.

