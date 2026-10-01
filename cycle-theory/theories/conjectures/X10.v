(** * Cycle.conjectures.X10 -- v2 clean cycle continuation *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X10 vocabulary ************************************************)

Definition x10_rainbow_cycle
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  uniq (map col (map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)))).

Definition x10_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x10_colour_classes_large
    (G : sgraph) (n k : nat) (col : {set G} -> 'I_n) : Prop :=
  forall i : 'I_n, k <= #|[set e in x10_edge_set G | col e == i]|.

Definition x10_cycle_vertices (G : sgraph) (c : seq G) : {set G} :=
  [set v | v \in c].

Definition x10_longest_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  forall c' : seq G, ucycle (--) c' -> 2 < size c' -> size c' <= size c.

(** ** X10 statements ******************************************************)

(** Studies slice: Aharoni's rainbow generalisation of Caccetta-Haggkvist. *)
Definition aharoni_rainbow_caccetta_haggkvist_statement : Prop :=
  forall (n k : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < k -> #|G| = n ->
    @x10_colour_classes_large G n k col ->
    exists c : seq G,
      @x10_rainbow_cycle G n col c /\
      size c <= ceil_div n k.

(** Studies slice: Smith's conjecture on longest cycles in r-connected graphs. *)
Definition smith_longest_cycles_r_connected_statement : Prop :=
  forall (r : nat) (G : sgraph) (c d : seq G),
    2 <= r ->
    k_connected G r ->
    @x10_longest_cycle G c ->
    @x10_longest_cycle G d ->
    r <= #|@x10_cycle_vertices G c :&: @x10_cycle_vertices G d|.
