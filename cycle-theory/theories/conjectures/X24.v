(** * Cycle.conjectures.X24 -- v2 rainbow cycle factorization row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X24 vocabulary ************************************************)

Definition x24_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

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

(** Studies slice: rainbow cycle in every 1-factorization of K_n. *)
Definition one_factorization_long_rainbow_cycle_statement : Prop :=
  forall (n : nat) (col : {set 'K_n} -> 'I_(n.-1)),
    2 < n ->
    ~~ odd n ->
    x24_one_factorization col ->
    exists c : seq (complete n),
      x24_rainbow_cycle col c /\
      (n - 2 <= size c)%N.
