(** * Chromatic.conjectures.X142 -- v2 neighbour-sum edge-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X142 vocabulary ***********************************************)

Definition x142_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x142_edges_incident (G : sgraph) (v : G) : {set {set G}} :=
  [set e in x142_edge_set G | v \in e].

Definition x142_incident_sum
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (v : G) : nat :=
  \sum_(e in x142_edges_incident v) (val (col e)).+1.

Definition x142_proper_edge_colouring
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  forall e f : {set G},
    e \in x142_edge_set G ->
    f \in x142_edge_set G ->
    e != f ->
    e :&: f != set0 ->
    col e != col f.

Definition x142_neighbour_sum_distinguishing
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  forall x y : G,
    x -- y ->
    x142_incident_sum col x != x142_incident_sum col y.

Definition x142_neighbour_sum_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : {set G} -> 'I_k,
    x142_proper_edge_colouring col /\
    x142_neighbour_sum_distinguishing col.

(** ** X142 statements *****************************************************)

(** Flandrin et al.: every connected graph of order at least three, except
    [C_5], has neighbour-sum-distinguishing edge chromatic number at most
    Delta(G)+2.  Colours are positive integers [1..k], encoded by ['I_k] values
    shifted by one in the incident sums. *)
Definition flandrin_neighbour_sum_distinguishing_edge_colouring_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    3 <= #|G| ->
    ~ inhabited (G ≃ cycle_graph 5) ->
    x142_neighbour_sum_edge_colourable G (Delta G + 2).
