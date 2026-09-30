(** * Chromatic.conjectures.X142 -- v2 neighbour-sum edge-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X142 vocabulary ***********************************************)

Definition x142_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

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

(** Corpus row: studies:std_flandrin_et_al_conjecture_neighbour_sum_distingu
    Site: none
    Review: none
    English statement: (Flandrin, Marczyk, Przybylo, Saclé and Wozniak, studies slice of the corpus)
      Every connected finite simple graph with at least three vertices that is not isomorphic to the
      5-cycle admits a proper edge colouring with Delta(G) + 2 colours in which, for any two
      adjacent vertices, the sums of the colours of their incident edges differ.
    Definitions: [x142_neighbour_sum_edge_colourable G k] - such a colouring with k colours exists
      (this file); [x142_proper_edge_colouring col] - two distinct edges that meet get different
      colours (this file); [x142_neighbour_sum_distinguishing col] - adjacent vertices have
      different incident colour sums (this file); [x142_incident_sum col v] - the sum over the edges
      at v of the colour value plus one (this file); [x142_edge_set G] and [x142_edges_incident v] -
      edges as 2-element vertex sets, and those containing v (this file); [cycle_graph 5] (GTBase
      base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above.
      Colours are the positive integers 1 to k, encoded as ['I_k] values shifted by one inside the
      incident sums, so that the sums really distinguish colour multisets. The exclusion of C5 is
      stated as the absence of an isomorphism with [cycle_graph 5]. *)
Definition flandrin_neighbour_sum_distinguishing_edge_colouring_statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    3 <= #|G| ->
    ~ inhabited (G ≃ cycle_graph 5) ->
    x142_neighbour_sum_edge_colourable G (Delta G + 2).

