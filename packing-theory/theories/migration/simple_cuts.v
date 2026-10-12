(** Frozen simple-cut contracts at a69e27fedb17b9a509dc794b45f6e2aa5c8f4e9e.
    X47's cut bound has no graph-order guard. The two entire Packing rows keep
    their quantifiers, positive pattern edge count and repeated-part semantics.
    The Originals compose A11's raw minimum degree with M1's raw edge set and
    this family's raw cuts. Older certificate files remain unchanged. *)
From GTBase Require Import base common.
From GTBase Require simple_cuts.
From Packing.conjectures Require Import X47 X48.
From Packing.migration Require simple_edges min_degree_at_least.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SE := Packing.migration.simple_edges.
Module MD := Packing.migration.min_degree_at_least.

Module Legacy.

Definition x47_crossing_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in x47_edge_set G | (e :&: S != set0) && (e :&: (~: S) != set0)].

Definition x47_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 ->
    S != [set: G] ->
    k <= #|Legacy.x47_crossing_edges S|.

End Legacy.

Module X47Legacy.

Definition tree_decomposition_delta_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @Legacy.x47_edge_connected G (f (Delta T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.

End X47Legacy.

Module X48Legacy.

Definition tree_decomposition_leaf_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @Legacy.x47_edge_connected G (f (x48_leaf_count T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @x47_tree_decomposition_by_copies G T.

End X48Legacy.

Module Original.

Definition x47_crossing_edges (G : sgraph) (S : {set G}) : {set {set G}} :=
  [set e in SE.Legacy.edge_set G | (e :&: S != set0) && (e :&: (~: S) != set0)].

Definition x47_edge_connected (G : sgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 ->
    S != [set: G] ->
    k <= #|Original.x47_crossing_edges S|.

Definition x47_tree_decomposition_by_copies (G T : sgraph) : Prop :=
  exists parts : seq {set {set G}},
    (forall F : {set {set G}}, F \in parts -> @x47_copy_edge_set G T F) /\
    (forall F : {set {set G}}, F \in parts -> F \subset SE.Legacy.edge_set G) /\
    (forall e : {set G}, e \in SE.Legacy.edge_set G ->
      exists F : {set {set G}}, F \in parts /\ e \in F) /\
    forall (F1 F2 : {set {set G}}) (e : {set G}),
      F1 \in parts -> F2 \in parts -> e \in F1 -> e \in F2 -> F1 = F2.

End Original.

Module X47Original.

Definition tree_decomposition_delta_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@SE.Legacy.edge_set T| ->
      @Original.x47_edge_connected G (f (Delta T)) ->
      @MD.Legacy.x47_min_degree_at_least G (f #|@SE.Legacy.edge_set T|) ->
      #|@SE.Legacy.edge_set T| %| #|@SE.Legacy.edge_set G| ->
      @Original.x47_tree_decomposition_by_copies G T.

End X47Original.

Module X48Original.

Definition tree_decomposition_leaf_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@SE.Legacy.edge_set T| ->
      @Original.x47_edge_connected G (f (x48_leaf_count T)) ->
      @MD.Legacy.x47_min_degree_at_least G (f #|@SE.Legacy.edge_set T|) ->
      #|@SE.Legacy.edge_set T| %| #|@SE.Legacy.edge_set G| ->
      @Original.x47_tree_decomposition_by_copies G T.

End X48Original.

Lemma x47_crossing_edges_compat (G : sgraph) (S : {set G}) :
  Legacy.x47_crossing_edges S = x47_crossing_edges S.
Proof. by []. Qed.

Lemma x47_edge_connected_compat (G : sgraph) (k : nat) :
  Legacy.x47_edge_connected G k <-> x47_edge_connected G k.
Proof. exact: iff_refl. Qed.

Lemma tree_decomposition_delta_edge_connected_statement_compat :
  X47Legacy.tree_decomposition_delta_edge_connected_statement <->
  tree_decomposition_delta_edge_connected_statement.
Proof. exact: iff_refl. Qed.

Lemma tree_decomposition_leaf_edge_connected_statement_compat :
  X48Legacy.tree_decomposition_leaf_edge_connected_statement <->
  tree_decomposition_leaf_edge_connected_statement.
Proof. exact: iff_refl. Qed.

Lemma x47_crossing_edges_original_compat (G : sgraph) (S : {set G}) :
  Original.x47_crossing_edges S = x47_crossing_edges S.
Proof. by rewrite /Original.x47_crossing_edges SE.x47_edge_set_compat. Qed.

Lemma x47_edge_connected_original_compat (G : sgraph) (k : nat) :
  Original.x47_edge_connected G k <-> x47_edge_connected G k.
Proof.
split=> H S S0 ST; have := H S S0 ST.
- by rewrite x47_crossing_edges_original_compat.
- by rewrite x47_crossing_edges_original_compat.
Qed.

Lemma x47_tree_decomposition_original_compat (G T : sgraph) :
  Original.x47_tree_decomposition_by_copies G T <->
  x47_tree_decomposition_by_copies G T.
Proof.
by rewrite /Original.x47_tree_decomposition_by_copies SE.x47_edge_set_compat.
Qed.

Lemma tree_decomposition_delta_edge_connected_statement_original_compat :
  X47Original.tree_decomposition_delta_edge_connected_statement <->
  tree_decomposition_delta_edge_connected_statement.
Proof.
rewrite -MD.tree_decomposition_delta_edge_connected_statement_compat.
split=> -[f H]; exists f => T G tr te conn deg dvd.
- apply: (proj1 (x47_tree_decomposition_original_compat G T)); apply: (H T G tr).
  + by rewrite SE.x47_edge_set_compat.
  + exact: (proj2 (x47_edge_connected_original_compat G (f (Delta T))) conn).
  + by rewrite SE.x47_edge_set_compat.
  + by rewrite !SE.x47_edge_set_compat.
- rewrite !SE.x47_edge_set_compat in te deg dvd.
  apply: (proj2 (x47_tree_decomposition_original_compat G T)).
  exact: (H T G tr te (proj1 (x47_edge_connected_original_compat G (f (Delta T))) conn) deg dvd).
Qed.

Lemma tree_decomposition_leaf_edge_connected_statement_original_compat :
  X48Original.tree_decomposition_leaf_edge_connected_statement <->
  tree_decomposition_leaf_edge_connected_statement.
Proof.
rewrite -MD.tree_decomposition_leaf_edge_connected_statement_compat.
split=> -[f H]; exists f => T G tr te conn deg dvd.
- apply: (proj1 (x47_tree_decomposition_original_compat G T)); apply: (H T G tr).
  + by rewrite SE.x47_edge_set_compat.
  + exact: (proj2 (x47_edge_connected_original_compat G (f (x48_leaf_count T))) conn).
  + by rewrite SE.x47_edge_set_compat.
  + by rewrite !SE.x47_edge_set_compat.
- rewrite !SE.x47_edge_set_compat in te deg dvd.
  apply: (proj2 (x47_tree_decomposition_original_compat G T)).
  exact: (H T G tr te (proj1 (x47_edge_connected_original_compat G (f (x48_leaf_count T))) conn) deg dvd).
Qed.
