(** * Packing.conjectures.X5 -- v2 milestone X5, clean packing rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local packing vocabulary ********************************************)

Definition x5_is_triangle (G : sgraph) (T : {set G}) : Prop :=
  clique T /\ #|T| = 3.

Definition x5_tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

Definition x5_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x5_edge_disjoint_triangles (G : sgraph) (ts : seq {set G}) : Prop :=
  uniq ts /\
  (forall T : {set G}, T \in ts -> x5_is_triangle T) /\
  forall T U : {set G}, T \in ts -> U \in ts -> T != U ->
    [disjoint x5_tri_edges T & x5_tri_edges U].

Definition x5_triangle_edge_transversal
    (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x5_edge_set G /\
  forall T : {set G}, x5_is_triangle T ->
    exists e : {set G}, e \in F /\ e \in x5_tri_edges T.

Definition x5_pairwise_disjoint_sets
    (G : sgraph) (m : nat) (A : 'I_m -> {set G}) : Prop :=
  forall i j : 'I_m, i != j -> [disjoint A i & A j].

(** ** X5 statements *******************************************************)

(** Erdos Problems #167. *)
Definition triangle_packing_transversal_statement : Prop :=
  forall (G : sgraph) (k : nat),
    (forall ts : seq {set G}, x5_edge_disjoint_triangles ts -> size ts <= k) ->
    exists F : {set {set G}},
      x5_triangle_edge_transversal F /\ #|F| <= 2 * k.

(** Erdos Problems #914. *)
Definition clique_factor_min_degree_statement : Prop :=
  forall (r m : nat) (G : sgraph),
    2 <= r -> 1 <= m ->
    #|G| = r * m ->
    (forall v : G, m * (r - 1) <= #|N(v)|) ->
    exists A : 'I_m -> {set G},
      x5_pairwise_disjoint_sets A /\
      forall i : 'I_m, #|A i| = r /\ clique (A i).
