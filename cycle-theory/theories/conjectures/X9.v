(** * Cycle.conjectures.X9 -- v2 clean cycle rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X9 vocabulary *************************************************)

Definition x9_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x9_cycle_edges (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition x9_genuine_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition x9_colour_classes_large
    (G : sgraph) (n r : nat) (col : {set G} -> 'I_n) : Prop :=
  forall i : 'I_n, r <= #|[set e in x9_edge_set G | col e == i]|.

Definition x9_cycle_incident_edges_properly_coloured
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) : Prop :=
  forall e f : {set G},
    e \in @x9_cycle_edges G c ->
    f \in @x9_cycle_edges G c ->
    e != f ->
    ~~ [disjoint e & f] ->
    col e != col f.

Definition x9_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition x9_cycle_chord_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ x9_consecutive_in_cycle c p.1 p.2]]|.

(** ** X9 statements *******************************************************)

(** arXiv:1806.00825, Conjecture 4. *)
Definition proper_edge_coloured_short_cycle_statement : Prop :=
  forall (n r : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < r -> #|G| = n ->
    @x9_colour_classes_large G n r col ->
    exists c : seq G,
      @x9_genuine_cycle G c /\
      size c <= ceil_div n r /\
      @x9_cycle_incident_edges_properly_coloured G n col c.

(** arXiv:2502.04726, Question 4.3. *)
Definition min_degree_three_linearly_many_chords_cycle_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall G : sgraph,
      0 < #|G| ->
      (forall v : G, 3 <= #|N(v)|) ->
      exists c : seq G,
        @x9_genuine_cycle G c /\
        cden * @x9_cycle_chord_count G c >= cnum * size c.
