(** * Chromatic.conjectures.X63 -- v2 two-homogeneous colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X63 vocabulary ************************************************)

Definition x63_proper_colouring
    (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x63_neighbour_colours
    (G : sgraph) (C : finType) (col : G -> C) (v : G) : {set C} :=
  [set c : C | [exists u : G, (u -- v) && (col u == c)]].

Definition x63_k_homogeneous_colouring (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (col : G -> C),
    x63_proper_colouring col /\
    forall v : G, #|x63_neighbour_colours col v| = k.

Definition x63_k_homogeneous_with
    (G : sgraph) (C : finType) (col : G -> C) (k : nat) : Prop :=
  x63_proper_colouring col /\
  forall v : G, #|x63_neighbour_colours col v| = k.

(** ** X63 statements ******************************************************)

(** Corpus row: arxiv:2511.02892#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.02892__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.02892__04.json
    English statement: (Barat, Dvorak, Haxell, Kardos, Luzar, Onderko, Rajnik, Sotak and Ulyanov 2025, Problem 5.1, arXiv:2511.02892)
      Every cubic finite simple graph that admits some 2-homogeneous colouring, i.e. a proper
      colouring in which exactly two colours appear in the open neighbourhood of every vertex,
      admits one with only four colours.
    Definitions: [x63_k_homogeneous_colouring G k] - there are a finite palette and a proper
      colouring in which every vertex sees exactly k colours in its open neighbourhood (this file);
      [x63_k_homogeneous_with col k] - the same condition for a GIVEN colouring (this file);
      [x63_neighbour_colours col v] - the set of colours occurring on the neighbours of v (this
      file); [x63_proper_colouring] (this file); [regular G 3] (GTBase base/theories/base.v).
    Notes: "Four colours are always sufficient" is encoded as the existence of a 2-homogeneous
      colouring into ['I_4], not merely as a bound on some chromatic parameter, which is the
      constructive reading of the source. *)
Definition cubic_two_homogeneous_four_colour_statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    x63_k_homogeneous_colouring G 2 ->
    exists col : G -> 'I_4,
      x63_k_homogeneous_with col 2.
