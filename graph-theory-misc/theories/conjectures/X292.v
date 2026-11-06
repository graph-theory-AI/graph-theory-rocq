(** * GTMisc.conjectures.X292 -- v2 row: the planar hat guessing conjecture of Bosek et al. (the maximum hat guessing
      number of a planar graph is 4) *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X99.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X292 statement ******************************************************)

(** Reused vocabulary: X99's hat guessing game (GTMisc conjectures/X99.v, as X285 reuses it) and GTBase's
    [wagner_planar] (base.v).  X292 declares no helper of its own. *)

(** Corpus row: studies:std_planar_hat_guessing_number_conjecture_bosek_et_a
    Site: none
    Review: none
    English statement: (Bosek et al.; studies slice of the corpus, record arXiv:2107.05995)
      The maximum possible hat guessing number of a planar graph is 4.
    Definitions: [x99_hat_guessing_number_at_most G k] - for no q > k do the players have a winning strategy,
      i.e. HG(G) <= k (GTMisc conjectures/X99.v); [x99_winning_hat_strategy G q] - a guess per vertex that
      depends only on the neighbours' hats and is right for at least one vertex on every assignment of q colours,
      i.e. HG(G) >= q (same file); [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor, which by Wagner's
      theorem is planarity for finite graphs (GTBase base.v).
    Notes: encoded as stated: "the maximum is 4" is the bound HG(G) <= 4 for every planar graph together with a
      planar graph that wins with 4 colours.  x99_hat_guessing_number_at_most quantifies over every q > 4, so no
      monotonicity of the game in q is assumed.  The graph with no vertex wins with no number of colours and is
      planar, so it satisfies the bound and is no attainment witness.  The conjecture is Bosek et al.'s ([BDFGM])
      as Alon and Chizewer state it (arXiv:2107.05995v2, main.tex l.99-102).  Pinned status open, but FALSE at the
      pin: their Theorem planar1 (l.104-107) gives a planar graph with hat guessing number 12 (two adjacent
      vertices and m = 66^144 adjacent pairs joined to both, l.176-180); graphs with hat guessing number 6 and
      14 are cited at l.112-115.  The status correction is a separate corpus item. *)
Definition planar_hat_guessing_max_four_statement : Prop :=
  (forall G : sgraph, wagner_planar G -> x99_hat_guessing_number_at_most G 4) /\
  (exists G : sgraph, wagner_planar G /\ x99_winning_hat_strategy G 4).
