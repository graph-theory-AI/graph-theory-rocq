(** * Hypergraph.conjectures.X209 -- v2 hypergraph cut excess row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X209 vocabulary ***********************************************)

Definition x209_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = k.

Definition x209_cut_edge
    (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  [exists x in e, [exists y in e, col x != col y]].

Definition x209_cut_size
    (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  #|[set e in E | x209_cut_edge col e]|.

Definition x209_is_max_r_cut
    (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    x209_cut_size E col = c /\
    forall col' : T -> 'I_r, x209_cut_size E col' <= c.

(** Scale the excess by [r^(k-1)] to avoid rationals:
    [den * maxcut - (den - 1) * m], where [den = r^(k-1)]. *)
Definition x209_expected_den (r k : nat) : nat := r ^ k.-1.

Definition x209_scaled_excess
    (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat,
    x209_is_max_r_cut E r c /\
    x = x209_expected_den r k * c - (x209_expected_den r k).-1 * #|E|.

Definition x209_is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ x209_uniform E k, #|E| = m, x209_scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          x209_uniform E' k ->
          #|E'| = m ->
          x209_scaled_excess E' r k y ->
          x <= y].

(** ** X209 statements *****************************************************)

(** Corpus row: arxiv:1803.08462#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.08462__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.08462__00.json
    English statement: (Conlon, Fox, Kwan and Sudakov 2019, second plausible conjecture of
      "Hypergraph cuts above the average"; disproved in the same paper)
      For all fixed r and k with 2 <= r <= k, the smallest maximum r-cut over all k-uniform
      hypergraphs with m hyperedges has excess of order exactly the square root of m.
    Definitions: [x209_uniform E k] - every hyperedge has exactly k vertices
      (hypergraph-theory/theories/conjectures/X209.v); [x209_cut_edge col e] - the hyperedge e
      contains two vertices of different colours, i.e. it is cut (same file);
      [x209_cut_size E col] - the number of cut hyperedges (same file);
      [x209_is_max_r_cut E r c] - c is the largest cut size over all colourings with r colours
      (same file); [x209_expected_den r k] - the scaling denominator r^(k-1) (same file);
      [x209_scaled_excess E r k x] - x is r^(k-1) times the maximum r-cut minus (r^(k-1) - 1)
      times the number of hyperedges, i.e. the excess over the random-colouring average scaled
      to stay in the naturals (same file); [x209_is_min_scaled_excess r k m x] - x is the least
      such scaled excess over m-hyperedge k-uniform hypergraphs (same file);
      [big_Theta_nat f g] - f is bounded above and below by constant multiples of g
      (base/theories/asymptotics.v).
    Notes: the excess is scaled by the fixed denominator r^(k-1), which does not change the
      Theta order for fixed r and k, and the square-root envelope is expressed as
      excess(m)^2 = Theta(m).  MINIMALITY MIS-QUANTIFICATION (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md): in [x209_is_min_scaled_excess] the inner quantifier
      binds T' but never uses it, and E' is typed over the OUTER witness type T, so the minimum
      is taken over m-hyperedge k-uniform hypergraphs on ONE chooseable vertex set rather than
      over all of them.  The corpus records the row as disproved: the paper's own Theorem 1.2
      gives excess Omega(m^(5/9)) whenever r is at least 3 or k is at least 4. *)
Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, x209_is_min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).
