(** * Minor.conjectures.X174 -- v2 clique count without K_t immersion row *)

From GTBase Require Export base.
From Minor.conjectures Require Import U7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X174 vocabulary ***********************************************)

Definition x174_clique_count (G : sgraph) : nat :=
  #|[set S : {set G} | cliqueb S]|.

Definition x174_no_Kt_immersion (G : sgraph) (t : nat) : Prop :=
  ~ immersion G 'K_t.

Definition x174_extremal_bound (t n : nat) : nat :=
  (2 ^ (t - 2)) * (n - t + 3).

(** ** X174 statements *****************************************************)

(** Corpus row: arxiv:1606.06810#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1606.06810__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1606.06810__00.json
    English statement: (Fox and Wei 2018, conjecture in "On the number of cliques in graphs
      with a forbidden subdivision or immersion")
      For all t at least 2 and all n at least t-2, the maximum number of cliques in an
      n-vertex graph with no K_t immersion is exactly 2^(t-2) * (n - t + 3): every finite
      simple graph on n vertices that does not immerse K_t has at most that many cliques, and
      some finite simple graph on n vertices that does not immerse K_t has exactly that many.
    Definitions: [x174_clique_count G] - the number of vertex subsets of G that are cliques,
      the empty set included (minor-theory/theories/conjectures/X174.v);
      [x174_no_Kt_immersion G t] - G does not immerse the complete graph on t vertices (same
      file); [x174_extremal_bound t n] - the natural number 2^(t-2) * (n - t + 3) (same file);
      [immersion G H] - G contains an immersion of H, i.e. an injection of the vertices of H
      into those of G together with pairwise edge-disjoint walks realising the edges of H
      (minor-theory/theories/conjectures/U7.v).
    Notes: the exact maximum is split into a universal upper bound and an existence half, so
      no maximum operator is needed.  The immersion used is the weak (not strong) one, matching
      the paper's "no weak K_t-immersion", and every clique including the empty set is counted,
      which is what makes 2^(t-2)(n-t+3) match the extremal construction for n >= t.
      TRUNCATION CAVEAT (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md): [x174_extremal_bound] computes (n - t) + 3 in the
      naturals, so for the two admitted values n = t-2 and n = t-1 the bound reads
      2^(t-2) * 3 instead of the intended 2^(t-2) * 1 and 2^(t-2) * 2; on those two values the
      upper-bound half is too weak and the existence half asks for the wrong exact count. *)
Definition kt_immersion_clique_count_extremal_statement : Prop :=
  forall t n : nat,
    2 <= t ->
    t - 2 <= n ->
    (forall G : sgraph,
        #|G| = n ->
        x174_no_Kt_immersion G t ->
        x174_clique_count G <= x174_extremal_bound t n) /\
    (exists G : sgraph,
        #|G| = n /\
        x174_no_Kt_immersion G t /\
        x174_clique_count G = x174_extremal_bound t n).
