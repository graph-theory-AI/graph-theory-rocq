(** Frozen copy and equal-part decomposition contracts at 423936c66e0df86dff050496e86421193ebb1bcd.
    X47's copy is an injective map whose nested-quantifier image is the part: image edges need not be host
    edges. Its decomposition allows repeated equal parts. The two entire Packing rows keep their quantifier
    order, their positive pattern edge count and that repeated-part convention. The Originals compose this
    family's raw copy with M1's raw edge set, A11's raw minimum degree and the simple-cut family's raw cuts
    (the earlier Originals of Packing.migration.simple_cuts use the live copy predicate). Older certificate
    files remain unchanged. *)
From GTBase Require Import base common.
From GTBase Require edge_copies.
From Packing.conjectures Require Import X47 X48.
From Packing.migration Require simple_edges min_degree_at_least simple_cuts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SE := Packing.migration.simple_edges.
Module MD := Packing.migration.min_degree_at_least.
Module SC := Packing.migration.simple_cuts.

Module Legacy.

Definition x47_copy_edge_set
    (G T : sgraph) (F : {set {set G}}) : Prop :=
  exists f : T -> G,
    injective f /\
    F = [set e : {set G} |
          [exists x : T, [exists y : T, (x -- y) && (e == [set f x; f y])]]].

Definition x47_tree_decomposition_by_copies (G T : sgraph) : Prop :=
  exists parts : seq {set {set G}},
    (forall F : {set {set G}}, F \in parts -> @Legacy.x47_copy_edge_set G T F) /\
    (forall F : {set {set G}}, F \in parts -> F \subset x47_edge_set G) /\
    (forall e : {set G}, e \in x47_edge_set G ->
      exists F : {set {set G}}, F \in parts /\ e \in F) /\
    forall (F1 F2 : {set {set G}}) (e : {set G}),
      F1 \in parts -> F2 \in parts -> e \in F1 -> e \in F2 -> F1 = F2.

End Legacy.

Module X47Legacy.

Definition tree_decomposition_delta_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (Delta T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @Legacy.x47_tree_decomposition_by_copies G T.

End X47Legacy.

Module X48Legacy.

Definition tree_decomposition_leaf_edge_connected_statement : Prop :=
  exists f : nat -> nat,
    forall T G : sgraph,
      is_tree [set: T] ->
      0 < #|@x47_edge_set T| ->
      @x47_edge_connected G (f (x48_leaf_count T)) ->
      @x47_min_degree_at_least G (f #|@x47_edge_set T|) ->
      #|@x47_edge_set T| %| #|@x47_edge_set G| ->
      @Legacy.x47_tree_decomposition_by_copies G T.

End X48Legacy.

Module Original.

Definition x47_tree_decomposition_by_copies (G T : sgraph) : Prop :=
  exists parts : seq {set {set G}},
    (forall F : {set {set G}}, F \in parts -> @Legacy.x47_copy_edge_set G T F) /\
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
      @SC.Original.x47_edge_connected G (f (Delta T)) ->
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
      @SC.Original.x47_edge_connected G (f (x48_leaf_count T)) ->
      @MD.Legacy.x47_min_degree_at_least G (f #|@SE.Legacy.edge_set T|) ->
      #|@SE.Legacy.edge_set T| %| #|@SE.Legacy.edge_set G| ->
      @Original.x47_tree_decomposition_by_copies G T.

End X48Original.

(** ** Certificates *)

(** The nested-quantifier image and the pair image are the same set (not a conversion). *)
Lemma x47_copy_edge_set_compat (G T : sgraph) (F : {set {set G}}) :
  Legacy.x47_copy_edge_set T F <-> x47_copy_edge_set T F.
Proof. exact: iff_sym (GTBase.edge_copies.injective_edge_image_nested T F). Qed.

Lemma x47_tree_decomposition_by_copies_compat (G T : sgraph) :
  Legacy.x47_tree_decomposition_by_copies G T <-> x47_tree_decomposition_by_copies G T.
Proof.
split=> -[parts [Hc H]]; exists parts; split=> // F Fp.
- by apply/x47_copy_edge_set_compat; exact: Hc Fp.
- by apply/x47_copy_edge_set_compat; exact: Hc Fp.
Qed.

Lemma tree_decomposition_delta_edge_connected_statement_compat :
  X47Legacy.tree_decomposition_delta_edge_connected_statement <->
  tree_decomposition_delta_edge_connected_statement.
Proof.
split=> -[f H]; exists f => T G tr te conn deg dvd.
- by apply/x47_tree_decomposition_by_copies_compat; exact: (H T G tr te conn deg dvd).
- by apply/x47_tree_decomposition_by_copies_compat; exact: (H T G tr te conn deg dvd).
Qed.

Lemma tree_decomposition_leaf_edge_connected_statement_compat :
  X48Legacy.tree_decomposition_leaf_edge_connected_statement <->
  tree_decomposition_leaf_edge_connected_statement.
Proof.
split=> -[f H]; exists f => T G tr te conn deg dvd.
- by apply/x47_tree_decomposition_by_copies_compat; exact: (H T G tr te conn deg dvd).
- by apply/x47_tree_decomposition_by_copies_compat; exact: (H T G tr te conn deg dvd).
Qed.

(** The deepest decomposition differs from the simple-cut family's Original only in the frozen copy. *)
Lemma x47_tree_decomposition_by_copies_pre_simple_cuts (G T : sgraph) :
  Original.x47_tree_decomposition_by_copies G T <-> SC.Original.x47_tree_decomposition_by_copies G T.
Proof.
split=> -[parts [Hc H]]; exists parts; split=> // F Fp.
- by apply/x47_copy_edge_set_compat; exact: Hc Fp.
- by apply/x47_copy_edge_set_compat; exact: Hc Fp.
Qed.

Lemma x47_tree_decomposition_by_copies_original_compat (G T : sgraph) :
  Original.x47_tree_decomposition_by_copies G T <-> x47_tree_decomposition_by_copies G T.
Proof.
rewrite x47_tree_decomposition_by_copies_pre_simple_cuts.
exact: (SC.x47_tree_decomposition_original_compat G T).
Qed.

Lemma tree_decomposition_delta_edge_connected_statement_original_compat :
  X47Original.tree_decomposition_delta_edge_connected_statement <->
  tree_decomposition_delta_edge_connected_statement.
Proof.
rewrite -SC.tree_decomposition_delta_edge_connected_statement_original_compat.
split=> -[f H]; exists f => T G tr te conn deg dvd.
- by apply/x47_tree_decomposition_by_copies_pre_simple_cuts; exact: (H T G tr te conn deg dvd).
- by apply/x47_tree_decomposition_by_copies_pre_simple_cuts; exact: (H T G tr te conn deg dvd).
Qed.

Lemma tree_decomposition_leaf_edge_connected_statement_original_compat :
  X48Original.tree_decomposition_leaf_edge_connected_statement <->
  tree_decomposition_leaf_edge_connected_statement.
Proof.
rewrite -SC.tree_decomposition_leaf_edge_connected_statement_original_compat.
split=> -[f H]; exists f => T G tr te conn deg dvd.
- by apply/x47_tree_decomposition_by_copies_pre_simple_cuts; exact: (H T G tr te conn deg dvd).
- by apply/x47_tree_decomposition_by_copies_pre_simple_cuts; exact: (H T G tr te conn deg dvd).
Qed.

Print Assumptions x47_copy_edge_set_compat.
Print Assumptions x47_tree_decomposition_by_copies_compat.
Print Assumptions tree_decomposition_delta_edge_connected_statement_compat.
Print Assumptions tree_decomposition_leaf_edge_connected_statement_compat.
Print Assumptions x47_tree_decomposition_by_copies_pre_simple_cuts.
Print Assumptions x47_tree_decomposition_by_copies_original_compat.
Print Assumptions tree_decomposition_delta_edge_connected_statement_original_compat.
Print Assumptions tree_decomposition_leaf_edge_connected_statement_original_compat.
