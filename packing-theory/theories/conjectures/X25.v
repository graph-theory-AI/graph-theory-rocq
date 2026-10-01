(** * Packing.conjectures.X25 -- v2 perfect one-factorization row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X25 vocabulary ************************************************)

Definition x25_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

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

(** Studies slice: Kotzig's perfect 1-factorization conjecture. *)
Definition kotzig_perfect_one_factorization_statement : Prop :=
  forall n : nat,
    2 < n ->
    ~~ odd n ->
    exists col : {set 'K_n} -> 'I_(n.-1),
      x25_perfect_one_factorization col.
