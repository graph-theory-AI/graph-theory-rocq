(** * Chromatic.conjectures.X181 -- v2 random clique-colouring constant row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X181 vocabulary ***********************************************)

Definition x181_monochromatic
    (G : sgraph) (k : nat) (col : G -> 'I_k) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, col x == col y]].

Definition x181_maximal_clique (G : sgraph) (S : {set G}) : bool :=
  [&& 1 < #|S|, cliqueb S
    & [forall T : {set G}, (S \proper T) ==> ~~ cliqueb T]].

Definition x181_clique_colourable (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall S : {set G},
      x181_maximal_clique S ==> ~~ x181_monochromatic (fun v => col v) S]].

Definition x181_clique_chromatic_window
    (a b n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  [exists k : 'I_n.+1,
    [&& x181_clique_colourable G k,
        (b - a) * (trunc_log 2 n) <= b * (2 * k)
      & b * (2 * k) <= (b + a) * (trunc_log 2 n).+1]].

Definition x181_random_graph_clique_chromatic_constant : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n => @fg_gnp_weight 1 2 n)
      (x181_clique_chromatic_window a b).

(** ** X181 statements *****************************************************)

(** Corpus row: arxiv:1612.06539#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1612.06539__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1612.06539__00.json
    English statement: (Alon and Krivelevich 2017, informal conjecture on the tight constant, arXiv:1612.06539)
      For every positive rational a/b, with high probability over the uniform random graph on n
      labelled vertices, i.e. G(n,1/2), there is a k such that the graph is clique-k-colourable and
      2k lies within the relative window from (1 - a/b) * floor(log2 n) to (1 + a/b) * (floor(log2
      n) + 1); that is, the clique chromatic number of G(n,1/2) is (1/2 + o(1)) log2 n with high
      probability.
    Definitions: [x181_clique_colourable G k] - some colouring by k colours leaves no maximal
      clique monochromatic (this file); [x181_maximal_clique S] - S has at least two vertices, is a
      clique, and no proper superset is a clique (this file); [x181_monochromatic col S] (this
      file); [x181_clique_chromatic_window a b n E] - the window inequalities above for the labelled
      graph with edge set E (this file); [fg_whp] - the event weight ratio tends to 1 in the exact
      finite weight model (GTBase base/theories/finite_graph.v); [fg_gnp_weight 1 2 n] - the
      G(n,1/2) weight (finite_graph.v); [trunc_log 2 n] - floor of log2 n (mathcomp).
    Notes: PROXY ENCODING, corpus leg partial. Per the faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, the with-high-probability
      wrapper and the clique-colouring vocabulary are faithful, but the conjecture is an EQUALITY
      and the encoding captures only part of it: the window asserts the existence of SOME k in the
      window for which the graph is clique-k-colourable, which is the upper half, and does not
      assert that no smaller k works, so the clique chromatic number itself is not pinned to the
      window. Corpus status: solved by Demidovich and Zhukovskii 2023. The body is left untouched
      here, WP4 changes comments only. *)
Definition random_graph_clique_chromatic_tight_constant_statement : Prop :=
  x181_random_graph_clique_chromatic_constant.
