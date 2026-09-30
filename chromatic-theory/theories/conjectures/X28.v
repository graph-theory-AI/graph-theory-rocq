(** * Chromatic.conjectures.X28 -- v2 planar choosability row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X28 vocabulary ************************************************)

Definition x28_no_cycle_length_between (G : sgraph) (a b : nat) : Prop :=
  forall c : seq G,
    ucycle (--) c ->
    a <= size c ->
    size c <= b ->
    False.

(** ** X28 statements ******************************************************)

(** Corpus row: arxiv:1508.03437#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1508.03437__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1508.03437__00.json
    English statement: (Dvorak and Postle 2016, open question, arXiv:1508.03437)
      Every planar finite simple graph with no cycle of length 4, 5 or 6 is 3-choosable: for every
      assignment of lists of at least three colours to its vertices there is a proper colouring
      picking each vertex's colour from its own list.
    Definitions: [x28_no_cycle_length_between G a b] - G has no [ucycle] whose number of vertices
      lies between a and b (this file); [choosable G 3] (GTBase base/theories/base.v);
      [wagner_planar] (base.v).
    Notes: The source mentions two open questions, forbidding cycles of lengths 4 to 7 and
      forbidding 4 to 6; the Rocq body encodes the LATTER, wide-open one, which implies the former.
      [x28_no_cycle_length_between] has no size guard, which is harmless since the forbidden sizes
      are at least 4. *)
Definition planar_no_4_to_6_cycles_three_choosable_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    x28_no_cycle_length_between G 4 6 ->
    choosable G 3.
