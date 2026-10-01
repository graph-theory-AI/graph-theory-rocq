(** * Cycle.conjectures.XE1 -- Erdős open clean/bounded rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition xe1_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set e : {set G} |
      [exists p : G * G,
        [&& p.1 \in c, p.2 \in c, p.1 -- p.2,
            e == [set p.1; p.2] &
            (((p.1, p.2) \in zip c (rot 1 c)) ||
             ((p.2, p.1) \in zip c (rot 1 c)))]]].

Definition xe1_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe1_cycle_or_edge_piece (G : sgraph) (P : {set {set G}}) : Prop :=
  (exists c : seq G, xe1_cycle c /\ P = xe1_cycle_edges c) \/
  (exists e : {set G}, e \in xe1_edge_set G /\ P = [set e]).

Definition xe1_pairwise_edge_disjoint
    (G : sgraph) (m : nat) (P : 'I_m -> {set {set G}}) : Prop :=
  forall i j : 'I_m, i != j -> [disjoint P i & P j].

Definition xe1_covers_edges
    (G : sgraph) (m : nat) (P : 'I_m -> {set {set G}}) : Prop :=
  forall e : {set G}, e \in xe1_edge_set G -> exists i : 'I_m, e \in P i.

(** Erdős Problems #184. *)
Definition erdos_184_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      exists m : nat, exists P : 'I_m -> {set {set G}},
        m <= C * #|G| /\
        xe1_pairwise_edge_disjoint P /\
        xe1_covers_edges P /\
        forall i : 'I_m, xe1_cycle_or_edge_piece (P i).
