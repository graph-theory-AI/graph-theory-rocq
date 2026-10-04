(** A28 disjoint unions (chromatic): X66's disjoint union of two simple graphs -- the three-case relation on
    [G + H], its two constructor proofs and the graph -- with the complete good-trees row, frozen at the A27 pin
    ec5fb25.  Baseline, hashes and exact substitutions are recorded in meta/migration_reports/disjoint_union.spec.json.
    - [X66Legacy]: [x66_disjoint_union_rel] (adjacency inside each summand, none across), [x66_disjoint_union_sym]
      and [x66_disjoint_union_irrefl] with their scripts, [x66_disjoint_union] and the row (both tree guards, both
      goodness premises, goodness of the union).
    The frozen relation is the same three-case match as upstream GraphTheory's [join_rel], so it converts; the frozen
    graph differs from [sjoin] only in its opaque proof fields, so the two are related by pointwise adjacency and the
    identity isomorphism, and the row, whose induced copies are isomorphisms of the underlying relations, converts. *)
From GTBase Require Export base.
From Chromatic.conjectures Require Import U8 X3 X66.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module X66Legacy.

Definition x66_disjoint_union_rel (G H : sgraph) : rel (G + H) :=
  fun x y =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | _, _ => false
    end.

Lemma x66_disjoint_union_sym (G H : sgraph) :
  symmetric (@X66Legacy.x66_disjoint_union_rel G H).
Proof. by move=> [a|a] [b|b] //=; rewrite sgP. Qed.

Lemma x66_disjoint_union_irrefl (G H : sgraph) :
  irreflexive (@X66Legacy.x66_disjoint_union_rel G H).
Proof. by move=> [a|a] //=; rewrite sg_irrefl. Qed.

Definition x66_disjoint_union (G H : sgraph) : sgraph :=
  SGraph (@X66Legacy.x66_disjoint_union_sym G H) (@X66Legacy.x66_disjoint_union_irrefl G H).

Definition good_trees_disjoint_union_good_statement : Prop :=
  forall H1 H2 : sgraph,
    is_tree [set: H1] ->
    is_tree [set: H2] ->
    x66_good H1 ->
    x66_good H2 ->
    x66_good (X66Legacy.x66_disjoint_union H1 H2).

End X66Legacy.

(** The relation is upstream [join_rel] by conversion; the constructor proofs and the graphs are related by the
    identity isomorphism, never by an equation between proof fields. *)
Lemma x66_disjoint_union_rel_compat (G H : sgraph) (x y : G + H) :
  @X66Legacy.x66_disjoint_union_rel G H x y = @Chromatic.conjectures.X66.x66_disjoint_union_rel G H x y.
Proof.
by [].
Qed.

Lemma x66_disjoint_union_proofs_compat (G H : sgraph) :
  SGraph (@X66Legacy.x66_disjoint_union_sym G H) (@X66Legacy.x66_disjoint_union_irrefl G H) ≃
  SGraph (@Chromatic.conjectures.X66.x66_disjoint_union_sym G H) (@Chromatic.conjectures.X66.x66_disjoint_union_irrefl G H).
Proof. by apply: eq_diso => x y. Qed.

Lemma x66_disjoint_union_compat (G H : sgraph) :
  @edge_rel (X66Legacy.x66_disjoint_union G H) =2 @edge_rel (Chromatic.conjectures.X66.x66_disjoint_union G H).
Proof.
by [].
Qed.

Lemma x66_disjoint_union_diso (G H : sgraph) : X66Legacy.x66_disjoint_union G H ≃ Chromatic.conjectures.X66.x66_disjoint_union G H.
Proof. by rewrite /X66Legacy.x66_disjoint_union /Chromatic.conjectures.X66.x66_disjoint_union /sjoin; apply: eq_diso => x y. Qed.

(** The row: goodness reads the union through induced copies, isomorphisms of its vertices and adjacency. *)
Lemma good_trees_disjoint_union_good_statement_compat :
  X66Legacy.good_trees_disjoint_union_good_statement <->
  Chromatic.conjectures.X66.good_trees_disjoint_union_good_statement.
Proof.
rewrite /X66Legacy.good_trees_disjoint_union_good_statement.
reflexivity.
Qed.
