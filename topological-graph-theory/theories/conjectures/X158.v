(** * Topological.conjectures.X158 -- v2 planar queue-number row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X158 vocabulary ***********************************************)

Definition x158_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

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

(** Solved external problem: planar graphs have bounded queue number.  A
    q-queue layout is a vertex order plus a q-colouring of the edges with no two
    nested edges in the same queue. *)
Definition planar_graphs_bounded_queue_number_statement : Prop :=
  exists q : nat,
    forall G : sgraph,
      wagner_planar G -> x158_queue_layout G q.
