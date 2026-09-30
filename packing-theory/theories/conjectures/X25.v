(** * Packing.conjectures.X25 -- v2 perfect one-factorization row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X25 vocabulary ************************************************)

Definition x25_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x25_perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x25_edge_set G /\
  forall v : G, #|[set e in M | v \in e]| = 1.

Definition x25_cycle_edge_seq (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition x25_hamiltonian_edge_set (G : sgraph) (F : {set {set G}}) : Prop :=
  exists c : seq G,
    ucycle (--) c /\
    size c = #|G| /\
    F = [set e : {set G} | e \in x25_cycle_edge_seq c].

Definition x25_perfect_one_factorization
    (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) : Prop :=
  (forall i : 'I_(n.-1),
      x25_perfect_matching [set e in x25_edge_set 'K_n | col e == i]) /\
  forall i j : 'I_(n.-1), i != j ->
    x25_hamiltonian_edge_set
      ([set e in x25_edge_set 'K_n | (col e == i) || (col e == j)]).

(** ** X25 statements ******************************************************)

(** Corpus row: studies:std_kotzig_s_perfect_1_factorization_conjecture
    Site: none
    Review: none
    English statement: (Kotzig, "Kotzig's perfect 1-factorization conjecture")
      For every even n > 2 there is a colouring col of the vertex pairs of the complete
      graph K_n by n-1 colours such that each colour class is a perfect matching of
      K_n, and the union of any two distinct colour classes is the edge set of a
      Hamiltonian cycle of K_n.
    Definitions: [x25_edge_set G] — the two-element vertex sets {x, y} with x -- y
      (this file); [x25_perfect_matching M] — a set of edges in which every vertex lies
      in exactly one (this file); [x25_cycle_edge_seq c] — the edges of the closed walk
      through the sequence c (this file); [x25_hamiltonian_edge_set F] — F is the edge
      set of some uniq cycle visiting all |V(G)| vertices (this file);
      [x25_perfect_one_factorization col] — the two conditions above (this file);
      ['K_n] — the complete graph, [ucycle] — MathComp / coq-graph-theory.
    Notes: col is typed as a total function on all vertex sets of K_n, but only its
      restriction to edges matters, since the colour classes are carved out of
      [x25_edge_set 'K_n]. "n even and n > 2" is written [2 < n] and [~~ odd n]. *)
Definition kotzig_perfect_one_factorization_statement : Prop :=
  forall n : nat,
    2 < n ->
    ~~ odd n ->
    exists col : {set 'K_n} -> 'I_(n.-1),
      x25_perfect_one_factorization col.
