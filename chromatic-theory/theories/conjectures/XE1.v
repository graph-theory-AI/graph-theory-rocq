(** * Chromatic.conjectures.XE1 -- Erdős open clean/bounded rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local vocabulary ****************************************************)

Definition xe1_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition xe1_edge_count (G : sgraph) : nat := #|xe1_edge_set G|.

Definition xe1_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ forall x y : H, x -- y -> f x -- f y.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition xe1_vertices_of_seq (G : sgraph) (c : seq G) : {set G} :=
  [set v : G | v \in c].

Definition xe1_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition xe1_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c.

Definition xe1_cycle_diagonal_count (G : sgraph) (c : seq G) : nat :=
  #|[set p : G * G |
      [&& p.1 \in c, p.2 \in c, (enum_rank p.1 < enum_rank p.2)%N,
          p.1 -- p.2 & ~~ xe1_consecutive_in_cycle c p.1 p.2]]|.

Definition xe1_odd_cycle_with_diagonals (G : sgraph) (d : nat) : Prop :=
  exists c : seq G,
    xe1_cycle c /\ odd (size c) /\ d <= xe1_cycle_diagonal_count c.

Definition xe1_induced_subgraph_chi_le (G : sgraph) (r b : nat) : Prop :=
  forall S : {set G}, #|S| <= r -> χ([set: induced S]) <= b.

Definition xe1_unbounded (f : nat -> nat) : Prop :=
  forall M : nat, exists n : nat, M <= f n.

Definition xe1_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma xe1_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@xe1_delete_edges_rel G F).
Proof.
move=> x y; rewrite /xe1_delete_edges_rel.
rewrite sgP.
by rewrite setUC.
Qed.

Lemma xe1_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@xe1_delete_edges_rel G F).
Proof. by move=> x; rewrite /xe1_delete_edges_rel sg_irrefl. Qed.

Definition xe1_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@xe1_delete_edges_sym G F) (@xe1_delete_edges_irrefl G F).

Definition xe1_vertex_critical (G : sgraph) (k : nat) : Prop :=
  forall v : G, χ([set: induced (~: [set v])]) < k.

Definition xe1_edge_critical_set (G : sgraph) (F : {set {set G}}) (k : nat) : Prop :=
  F \subset @xe1_edge_set G /\ χ([set: @xe1_delete_edges G F]) < k.

Definition xe1_all_edge_critical_sets_large (G : sgraph) (r k : nat) : Prop :=
  forall F : {set {set G}}, xe1_edge_critical_set F k -> r < #|F|.

Definition xe1_strongly_independent_edges (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset @xe1_edge_set G /\
  forall e1 e2 : {set G}, e1 \in F -> e2 \in F -> e1 != e2 ->
    [disjoint e1 & e2] /\
    forall x y : G, x \in e1 -> y \in e2 -> x -- y -> False.

Definition xe1_strong_edge_colouring (G : sgraph) (k : nat) : Prop :=
  if @xe1_edge_set G == set0 then k = 0 else
    exists col : {set G} -> 'I_k,
      forall i : 'I_k,
        @xe1_strongly_independent_edges G [set e in @xe1_edge_set G | col e == i].

Definition xe1_strong_chromatic_index (G : sgraph) (k : nat) : Prop :=
  xe1_strong_edge_colouring G k /\
  forall j : nat, xe1_strong_edge_colouring G j -> k <= j.

(** ** XE1 statements ******************************************************)

(** Erdős Problems #108. *)
Definition erdos_108_statement : Prop :=
  forall r k : nat, 4 <= r -> 2 <= k ->
    exists f : nat,
      forall G : sgraph,
        f <= χ([set: G]) ->
        exists H : sgraph,
          xe1_subgraph_of H G /\ girth_geq H r /\ k <= χ([set: H]).

(** Erdős Problems #149. *)
Definition erdos_149_statement : Prop :=
  forall (G : sgraph) (sq : nat),
    xe1_strong_chromatic_index G sq ->
    4 * sq <= 5 * (Delta G) ^ 2.

(** Erdős Problems #628. *)
Definition erdos_628_statement : Prop :=
  forall (G : sgraph) (k a b : nat),
    χ([set: G]) = k ->
    ~ xe1_subgraph_of 'K_k G ->
    2 <= a -> 2 <= b -> a + b = k.+1 ->
    exists A B : {set G},
      [disjoint A & B] /\
      a <= χ([set: induced A]) /\
      b <= χ([set: induced B]).

(** Erdős Problems #944. *)
Definition erdos_944_statement : Prop :=
  forall k r : nat, 4 <= k -> 1 <= r ->
    exists G : sgraph,
      χ([set: G]) = k /\
      xe1_vertex_critical G k /\
      xe1_all_edge_critical_sets_large G r k.
