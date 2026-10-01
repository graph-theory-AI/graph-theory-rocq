(** * Packing.conjectures.X47 -- v2 tree edge-decomposition row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X47 vocabulary ************************************************)

Definition x47_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

Definition x47_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x47_crossing_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in x47_edge_set G | (e :&: S != set0) && (e :&: (~: S) != set0)].

Definition x47_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 ->
    S != [set: G] ->
    k <= #|x47_crossing_edges S|.

Definition x47_copy_edge_set
    (G T : sgraph) (F : {set {set G}}) : Prop :=
  exists f : T -> G,
    injective f /\
    F = [set e : {set G} |
          [exists x : T, [exists y : T, (x -- y) && (e == [set f x; f y])]]].

Definition x47_tree_decomposition_by_copies (G T : sgraph) : Prop :=
  exists parts : seq {set {set G}},
    (forall F : {set {set G}}, F \in parts -> @x47_copy_edge_set G T F) /\
    (forall F : {set {set G}}, F \in parts -> F \subset x47_edge_set G) /\
    (forall e : {set G}, e \in x47_edge_set G ->
      exists F : {set {set G}}, F \in parts /\ e \in F) /\
    forall (F1 F2 : {set {set G}}) (e : {set G}),
      F1 \in parts -> F2 \in parts -> e \in F1 -> e \in F2 -> F1 = F2.

(** ** X47 statements ******************************************************)

(** arXiv:1507.08208, tree decomposition under edge-connectivity and minimum
    degree bounds. *)
Definition tree_decomposition_delta_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (Delta T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.
