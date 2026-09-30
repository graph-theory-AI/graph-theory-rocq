(** * Chromatic.conjectures.X83 -- v2 rainbow induced path row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X83 vocabulary ************************************************)

Definition x83_rainbow_induced_path
    (G : sgraph) (C : finType) (col : G -> C) (p : seq G) : Prop :=
  x3_induced_path p /\ uniq (map col p).

(** ** X83 statements ******************************************************)

(** Corpus row: studies:std_aravind_s_rainbow_induced_path_conjecture
    Site: none
    Review: none
    English statement: (Aravind, studies slice of the corpus)
      For every nonempty triangle-free finite simple graph G and every proper colouring of G, not
      necessarily one with the minimum number of colours, there is an induced path on exactly chi(G)
      vertices all of whose vertices receive distinct colours.
    Definitions: [x83_rainbow_induced_path col p] - p is an [x3_induced_path] and its colour list
      has no repetition (this file); [x3_induced_path p] - a list of distinct vertices forming a
      path in which only consecutive vertices are adjacent (X3.v); [x3_proper_colouring] (X3.v);
      [triangle_free] (GTBase base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      source's "colouring (not necessarily optimal)" is a PROPER colouring with possibly more than
      chi(G) colours, which is what [x3_proper_colouring] over an arbitrary finite palette
      expresses. The guard 0 < #|G| excludes the empty graph. *)
Definition aravind_rainbow_induced_chromatic_path_statement : Prop :=
  forall (G : sgraph) (C : finType) (col : G -> C),
    0 < #|G| ->
    triangle_free G ->
    x3_proper_colouring col ->
    exists p : seq G,
      size p = χ([set: G]) /\
      x83_rainbow_induced_path col p.
