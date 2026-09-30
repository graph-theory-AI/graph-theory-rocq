(** * Cycle.conjectures.X24 -- v2 rainbow cycle factorization row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X24 vocabulary ************************************************)

Definition x24_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x24_perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x24_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| = 1.

Definition x24_one_factorization
    (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) : Prop :=
  forall i : 'I_(n.-1),
    x24_perfect_matching [set e in x24_edge_set 'K_n | col e == i].

Definition x24_cycle_edge_seq (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition x24_rainbow_cycle
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\ uniq (map col (x24_cycle_edge_seq c)).

(** ** X24 statements ******************************************************)

(** Corpus row: studies:std_akbari_etesami_mahini_mahmoody_question_on_long
    Site: none
    Review: none
    English statement: (Akbari, Etesami, Mahini and Mahmoody, "Akbari-Etesami-Mahini-
      Mahmoody question on long rainbow cycles in 1-factorizations of K_n")
      For every even natural number n greater than 2 and every colouring of the vertex
      pairs of the complete graph on n vertices by n-1 colours which is a 1-factorization,
      meaning that each of the n-1 colour classes is a perfect matching, there is a rainbow
      cycle of length at least n-2: a cycle through more than two vertices whose
      consecutive edges all receive pairwise distinct colours.
    Definitions: [x24_edge_set G] - the two-element vertex sets that are edges (X24.v);
      [x24_perfect_matching M] - M is a set of edges in which every vertex lies on exactly
      one member (X24.v); [x24_one_factorization col] - for each of the n-1 colours the
      class of that colour is a perfect matching of the complete graph (X24.v);
      [x24_cycle_edge_seq c] and [x24_rainbow_cycle col c] - the consecutive-pair edges of
      c, and c being a [ucycle] of length more than two with duplicate-free colour list
      (X24.v); ['K_n], written [complete n] - the complete graph on n vertices
      (coq-graph-theory sgraph); [ucycle] (MathComp path.v).
    Notes: the parity hypothesis [~~ odd n] is what makes a 1-factorization of the complete
      graph exist; for odd n the hypothesis [x24_one_factorization] is unsatisfiable. The
      corpus row is a studies slice with no site or review page, and is phrased there as a
      question; the Rocq statement is its affirmative form. *)
Definition one_factorization_long_rainbow_cycle_statement : Prop :=
  forall (n : nat) (col : {set 'K_n} -> 'I_(n.-1)),
    2 < n ->
    ~~ odd n ->
    x24_one_factorization col ->
    exists c : seq (complete n),
      x24_rainbow_cycle col c /\
      (n - 2 <= size c)%N.
