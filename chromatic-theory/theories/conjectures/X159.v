(** * Chromatic.conjectures.X159 -- v2 planar DP-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X159 vocabulary ***********************************************)

Definition x159_no_cycle_length_between (G : sgraph) (lo hi : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> lo <= size c -> size c <= hi -> False.

Definition x159_correspondence_assignment
    (G : sgraph) (C : G -> G -> 'I_3 -> 'I_3 -> bool) : Prop :=
  (forall u v : G, u -- v ->
    forall a b : 'I_3, C u v a b = C v u b a) /\
  (forall (u v : G) (a b1 b2 : 'I_3),
    u -- v -> C u v a b1 -> C u v a b2 -> b1 = b2) /\
  (forall (u v : G) (a1 a2 b : 'I_3),
    u -- v -> C u v a1 b -> C u v a2 b -> a1 = a2).

Definition x159_correspondence_colouring
    (G : sgraph) (C : G -> G -> 'I_3 -> 'I_3 -> bool) : Prop :=
  exists col : G -> 'I_3,
    forall u v : G, u -- v -> ~~ C u v (col u) (col v).

Definition x159_correspondence_3_colourable (G : sgraph) : Prop :=
  forall C : G -> G -> 'I_3 -> 'I_3 -> bool,
    x159_correspondence_assignment C ->
    x159_correspondence_colouring C.

(** ** X159 statements *****************************************************)

(** Corpus row: arxiv:1508.03437#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1508.03437__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1508.03437__01.json
    English statement: (Dvorak and Postle 2016, informal conjecture, arXiv:1508.03437)
      Every planar finite simple graph with no cycle of length between 4 and 8 has correspondence
      chromatic number at most 3: for every correspondence assignment giving, for each edge, a
      partial matching between the three colours at its two ends, there is a choice of one colour
      per vertex such that no edge has its two chosen colours matched.
    Definitions: [x159_no_cycle_length_between G lo hi] - G has no cycle whose number of vertices
      lies between lo and hi (this file); [x159_correspondence_assignment C] - for every edge the
      relation C is symmetric under swapping the two ends and is a partial matching, i.e. functional
      in each argument (this file); [x159_correspondence_colouring C] - a colouring by ['I_3]
      avoiding all matched pairs on edges (this file); [x159_correspondence_3_colourable G] - such a
      colouring exists for every correspondence assignment (this file); [wagner_planar] (GTBase
      base/theories/base.v).
    Notes: The palette is fixed to three colours per vertex, as in DP-colouring with lists of size
      3, and no consistency assumption on closed walks of length 3 is imposed, which is exactly the
      stronger claim the source leaves open. Corpus status: solved, by Jin, Kang and Zhu 2024 who
      proved DP-3-colourability for planar graphs with no cycle of length 4, 6 or 8; stated only
      here. The row was retargeted in 2026-07-16 from a blocked placeholder, see
      meta/BLOCKED_RETARGETING_FOUNDATIONS.md. *)
Definition planar_no_cycles_4_to_8_correspondence_chromatic_three_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    x159_no_cycle_length_between G 4 8 ->
    x159_correspondence_3_colourable G.
