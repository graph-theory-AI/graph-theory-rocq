(** * Chromatic.conjectures.X109 -- v2 Cereceda recolouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X109 vocabulary ***********************************************)

Definition x109_proper_colouring
    (G : sgraph) (q : nat) (col : {ffun G -> 'I_q}) : bool :=
  [forall x : G, [forall y : G, (x -- y) ==> (col x != col y)]].

Definition x109_recolour_step
    (G : sgraph) (q : nat) (c d : {ffun G -> 'I_q}) : bool :=
  [exists v : G,
     (c v != d v) &&
     [forall u : G, (u == v) || (c u == d u)]].

Definition x109_recolour_walk
    (G : sgraph) (q : nat)
    (c d : {ffun G -> 'I_q}) (w : seq {ffun G -> 'I_q}) : Prop :=
  path (x109_recolour_step (G := G) (q := q)) c w /\
  last c w = d /\
  all (x109_proper_colouring (G := G) (q := q)) (c :: w).

Definition x109_recolour_diameter_at_most
    (G : sgraph) (q bound : nat) : Prop :=
  forall c d : {ffun G -> 'I_q},
    x109_proper_colouring c ->
    x109_proper_colouring d ->
    exists w : seq {ffun G -> 'I_q},
      size w <= bound /\ x109_recolour_walk c d w.

(** ** X109 statements *****************************************************)

(** Corpus row: studies:std_cereceda_s_conjecture
    Site: none
    Review: none
    English statement: (Cereceda, studies slice of the corpus)
      There is a constant C such that for every k and every k-degenerate finite simple graph G on n
      vertices, any two proper colourings of G with k+2 colours are joined by a sequence of at most
      C*n^2 single-vertex recolouring steps, each intermediate colouring being proper; that is, the
      recolouring graph R_{k+2}(G) has diameter O(n^2).
    Definitions: [x109_proper_colouring col] - adjacent vertices get different colours (this
      file); [x109_recolour_step c d] - c and d differ at exactly one vertex (this file);
      [x109_recolour_walk c d w] - w is a path of recolouring steps from c to d all of whose
      colourings are proper (this file); [x109_recolour_diameter_at_most G q bound] - any two proper
      q-colourings are joined by such a walk of length at most bound (this file); [k_degenerate G k]
      - every nonempty vertex subset contains a vertex of degree at most k inside it (GTBase
      base/theories/base.v).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      asymptotic O(n^2) is made concrete by an explicit constant C quantified OUTSIDE k, n and G,
      which is a slightly stronger reading than a constant depending on k. Colourings are finite
      functions [{ffun G -> 'I_q}] so that the recolouring graph is a genuine finite object. *)
Definition cereceda_degenerate_recolouring_quadratic_diameter_statement : Prop :=
  exists C : nat,
    forall (k n : nat) (G : sgraph),
      #|G| = n ->
      k_degenerate G k ->
      x109_recolour_diameter_at_most G (k + 2) (C * n ^ 2).
