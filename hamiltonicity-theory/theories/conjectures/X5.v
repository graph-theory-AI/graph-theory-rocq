(** * Hamilton.conjectures.X5 -- v2 milestone X5, clean TSP-walk row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local Hamiltonicity vocabulary **************************************)

Definition x5_tsp_walk (G : sgraph) (w : seq G) : Prop :=
  exists x p,
    [/\ w = x :: p,
        path (--) x p,
        last x p = x
      & forall v : G, v \in w].

Definition x5_tsp_walk_length (G : sgraph) (w : seq G) : nat :=
  if w is _ :: p then size p else 0.

Definition x5_degree_two_count (G : sgraph) : nat :=
  #|[set v : G | #|N(v)| == 2]|.

(** ** X5 statements *******************************************************)

(** Corpus row: arxiv:1608.07568#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.07568__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.07568__00.json
    English statement: (Dvorak, Kral', Mohar 2016, arXiv:1608.07568,
      "Conjecture 1") For every n and every 2-connected graph G on n vertices
      whose maximum degree is at most three, G has a TSP walk - a closed walk
      that starts and ends at the same vertex and visits every vertex - whose
      length L, the number of steps it takes, satisfies
      4*L <= 5*n + n_2 - 4, where n_2 is the number of vertices of G of degree
      exactly two.  This is the source bound L <= (5*n + n_2)/4 - 1 with
      denominators cleared.
    Definitions: [x5_tsp_walk G w] - w = x :: p with p an adjacency-path from x,
      [last x p = x] and every vertex of G occurring in w (this file, X5.v);
      [x5_tsp_walk_length w] - the number of steps, [size p] (X5.v);
      [x5_degree_two_count G] - the number of vertices with exactly two
      neighbours (X5.v); [k_connected G 2] - more than two vertices and deleting
      any single vertex leaves the rest connected (base/theories/base.v);
      [Delta G] - maximum degree (base.v).
    Notes: "subcubic" is [Delta G <= 3]; 2-connectedness is base's Whitney-form
      [k_connected G 2], which forces #|G| > 2, so the truncated natural
      subtraction 5*n + n_2 - 4 never truncates and the inequality is the exact
      cleared form.  A TSP walk may repeat vertices and edges, as [x5_tsp_walk]
      allows.  STATUS: the conjecture was resolved affirmatively by Wigal, Yoo
      and Yu (arXiv:2112.06278, JCTB); this file states it only, and proves
      nothing. *)
Definition subcubic_two_connected_tsp_walk_bound_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    k_connected G 2 ->
    Delta G <= 3 ->
    exists w : seq G,
      x5_tsp_walk w /\
      4 * x5_tsp_walk_length w <= 5 * n + x5_degree_two_count G - 4.
