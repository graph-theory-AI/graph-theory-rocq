(** * Packing.conjectures.XE1 -- Erdos open clean/bounded rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition xe1_maximal_clique (G : sgraph) (K : {set G}) : Prop :=
  clique K /\
  forall L : {set G}, K \proper L -> ~ clique L.

Definition xe1_clique_transversal (G : sgraph) (X : {set G}) : Prop :=
  forall K : {set G}, xe1_maximal_clique K -> 2 <= #|K| -> X :&: K != set0.

Definition xe1_clique_transversal_number (G : sgraph) (t : nat) : Prop :=
  (exists X : {set G}, xe1_clique_transversal X /\ #|X| = t) /\
  forall u : nat, (exists X : {set G}, xe1_clique_transversal X /\ #|X| = u) -> t <= u.

Definition xe1_triangle_free_independence_guarantee (n h : nat) : Prop :=
  (forall G : sgraph,
      #|G| = n -> triangle_free G ->
      exists A : {set G}, xe1_stable_set A /\ h <= #|A|) /\
  forall h' : nat,
    (forall G : sgraph,
      #|G| = n -> triangle_free G ->
      exists A : {set G}, xe1_stable_set A /\ h' <= #|A|) -> h' <= h.

Definition xe1_tree (T : sgraph) : Prop :=
  is_forest [set: T] /\ connected [set: T].

Definition xe1_image_edges (G T : sgraph) (f : T -> G) : {set {set G}} :=
  [set e : {set G} |
      [exists x : T, [exists y : T,
        (x -- y) && (e == [set f x; f y])]]].

Definition xe1_edge_disjoint_tree_packing
    (n : nat) (T : forall k : 'I_n, sgraph) (emb : forall k : 'I_n, T k -> 'I_n)
    : Prop :=
  (forall k : 'I_n, injective (emb k)) /\
  (forall i j : 'I_n, i != j ->
      [disjoint @xe1_image_edges 'K_n (T i) (emb i)
              & @xe1_image_edges 'K_n (T j) (emb j)]) /\
  (forall e : {set 'I_n}, #|e| = 2 ->
      exists k : 'I_n, e \in @xe1_image_edges 'K_n (T k) (emb k)).

Definition xe1_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  forall x y : G, x \in c -> y \in c -> x != y -> x -- y ->
    ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

Definition xe1_chordal (G : sgraph) : Prop :=
  forall c : seq G, xe1_induced_cycle c -> size c <= 3.

Definition xe1_clique_edge_set (G : sgraph) (K : {set G}) : {set {set G}} :=
  [set e in xe1_edge_set G | e \subset K].

Definition xe1_clique_edge_partition
    (G : sgraph) (m : nat) (K : 'I_m -> {set G}) : Prop :=
  (forall i : 'I_m, clique (K i)) /\
  (forall i j : 'I_m, i != j ->
      [disjoint xe1_clique_edge_set (K i) & xe1_clique_edge_set (K j)]) /\
  (forall e : {set G}, e \in xe1_edge_set G ->
      exists i : 'I_m, e \in xe1_clique_edge_set (K i)).

Definition xe1_independent_set_count (G : sgraph) (k : nat) : nat :=
  #|[set S : {set G} | (#|S| == k) && [forall x in S, [forall y in S, ~~ (x -- y)]] ]|.

Definition xe1_unimodal_independent_sequence (G : sgraph) : Prop :=
  exists m : nat,
    (forall i : nat, i < m -> xe1_independent_set_count G i <= xe1_independent_set_count G i.+1) /\
    forall i : nat, m <= i -> xe1_independent_set_count G i.+1 <= xe1_independent_set_count G i.

(** Erdos Problems #151. *)
Definition erdos_151_statement : Prop :=
  forall (G : sgraph) (n h t : nat),
    #|G| = n ->
    xe1_triangle_free_independence_guarantee n h ->
    xe1_clique_transversal_number G t ->
    t <= n - h.

(** Erdos Problems #743. *)
Definition erdos_743_statement : Prop :=
  forall n : nat, 2 <= n ->
    forall T : forall k : 'I_n, sgraph,
      (forall k : 'I_n, #|T k| = (val k).+1 /\ xe1_tree (T k)) ->
      exists emb : forall k : 'I_n, T k -> 'I_n,
        @xe1_edge_disjoint_tree_packing n T emb.

(** Erdos Problems #81. *)
Definition erdos_81_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n : nat),
      #|G| = n -> xe1_chordal G ->
      exists m : nat, exists K : 'I_m -> {set G},
        xe1_clique_edge_partition K /\
        6 * m <= n ^ 2 + C * n.

(** Erdos Problems #993. *)
Definition erdos_993_statement : Prop :=
  forall T : sgraph,
    is_forest [set: T] ->
    xe1_unimodal_independent_sequence T.
