(** * Chromatic.conjectures.X75 -- v2 Albertson list-precolouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X75 vocabulary ************************************************)

Definition x75_lists_size_one_or_five
    (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  forall v : G, (#|L v| == 1) || (#|L v| == 5).

Definition x75_singleton_lists_far
    (G : sgraph) (C : finType) (L : G -> {set C}) (d : nat) : Prop :=
  forall x y : G,
    x != y -> #|L x| = 1 -> #|L y| = 1 -> y \notin ball d.-1 x.

(** ** X75 statements ******************************************************)

(** Corpus row: studies:std_albertson_s_problem_on_distance_constrained_list
    Site: none
    Review: none
    English statement: (Albertson, studies slice of the corpus)
      There is a constant d such that every planar finite simple graph with a list assignment giving
      each vertex a list of size one or five, and in which any two distinct vertices with singleton
      lists are at distance at least d, admits a proper colouring picking each vertex's colour from
      its own list.
    Definitions: [x75_lists_size_one_or_five L] - every list has size 1 or 5 (this file);
      [x75_singleton_lists_far L d] - two distinct vertices with singleton lists are never within
      distance d-1 of each other, expressed with base's [ball] (this file); [list_colourable]
      (GTBase base/theories/base.v); [wagner_planar] (base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. The singleton lists play
      the role of precoloured vertices. *)
Definition albertson_distance_constrained_list_colouring_statement : Prop :=
  exists d : nat,
    forall (G : sgraph) (C : finType) (L : G -> {set C}),
      wagner_planar G ->
      x75_lists_size_one_or_five L ->
      x75_singleton_lists_far L d ->
      list_colourable L.
