(** A28 disjoint unions (digraph): X2's disjoint union of two finite digraphs -- the whole [Section DisjointUnion] with
    its type alias, its anonymous [Finite]/[HasArc] packaging and its arc relation -- with the complete current row,
    frozen at the A27 pin ec5fb25, and the complete B1+A28 Original at B1's baseline 9e03072.  Baseline, hashes and
    exact substitutions are recorded in meta/migration_reports/disjoint_union.spec.json.
    - [X2Legacy]: the Section verbatim (arbitrary [D1 D2 : diGraphType], the alias [(D1 + D2)%type], [Finite.on],
      the relation with arcs inside each summand and none across, [HasArc.Build]) and the row (both summands
      delta-plus-Maderian, then their disjoint union is), over the live [delta_plus_maderian].
    - [X2Original] (text at 9e03072): the same row over the frozen sum and B1's raw
      [X2MaderianLegacy.delta_plus_maderian] (the nonempty-host minimum-out-degree bound and the complete subdivision
      model with branch vertices, nonempty dipaths, internal disjointness from branches and pairwise); B1's module is
      aliased, not imported.
    [HasArc] carries no proof, so the frozen and live sums are the same finite digraph up to conversion: the alias,
    the relation, every arc and the packaged [diGraphType] convert, and so do both rows. *)
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament.
From Digraph Require Import automorphism domination strong.
From Digraph Require Import classic_core heroes chi_bounded dichromatic.
From GTBase Require Import walks_paths.
From Digraph Require Import digraph_sum.
From Digraph.conjectures Require Import X2.
From Digraph.migration Require path_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** B1's certificate module, aliased without Import: its module names coincide with this file's. *)
Module B1 := Digraph.migration.path_vertices.

Module X2Legacy.

Section DisjointUnion.
Variables D1 D2 : diGraphType.

Definition x2_disjoint_union : Type := (D1 + D2)%type.
HB.instance Definition _ := Finite.on x2_disjoint_union.

Definition x2_disjoint_union_rel (x y : D1 + D2) : bool :=
  match x, y with
  | inl a, inl b => a --> b
  | inr a, inr b => a --> b
  | _, _ => false
  end.

HB.instance Definition _ := HasArc.Build x2_disjoint_union x2_disjoint_union_rel.

End DisjointUnion.

Definition delta_plus_maderian_disjoint_union_statement : Prop :=
  forall F1 F2 : diGraphType,
    delta_plus_maderian F1 -> delta_plus_maderian F2 ->
    delta_plus_maderian (X2Legacy.x2_disjoint_union F1 F2).

End X2Legacy.

(** The frozen [Finite]/[HasArc] packaging is used outside its module. *)
Import X2Legacy.

Module X2Original.

Definition delta_plus_maderian_disjoint_union_statement : Prop :=
  forall F1 F2 : diGraphType,
    B1.X2MaderianLegacy.delta_plus_maderian F1 -> B1.X2MaderianLegacy.delta_plus_maderian F2 ->
    B1.X2MaderianLegacy.delta_plus_maderian (X2Legacy.x2_disjoint_union F1 F2).

End X2Original.

(** The sum: the alias, the relation, the arcs and the packaged finite digraph convert. *)
Lemma x2_disjoint_union_compat (D1 D2 : diGraphType) :
  X2Legacy.x2_disjoint_union D1 D2 = Digraph.conjectures.X2.x2_disjoint_union D1 D2.
Proof.
by [].
Qed.

Lemma x2_disjoint_union_rel_compat (D1 D2 : diGraphType) (x y : D1 + D2) :
  @X2Legacy.x2_disjoint_union_rel D1 D2 x y = @Digraph.conjectures.X2.x2_disjoint_union_rel D1 D2 x y.
Proof.
by [].
Qed.

Lemma x2_disjoint_union_arc_compat (D1 D2 : diGraphType) (x y : X2Legacy.x2_disjoint_union D1 D2) :
  (x : X2Legacy.x2_disjoint_union D1 D2) --> y = ((x : Digraph.conjectures.X2.x2_disjoint_union D1 D2) --> y).
Proof.
by [].
Qed.

Lemma x2_disjoint_union_digraph_compat (D1 D2 : diGraphType) :
  (X2Legacy.x2_disjoint_union D1 D2 : diGraphType) = (Digraph.conjectures.X2.x2_disjoint_union D1 D2 : diGraphType).
Proof.
by [].
Qed.

(** Each packaging resolves its arcs to its own relation: the frozen instance to the frozen relation, the live one to
    the live relation. *)
Lemma x2_disjoint_union_legacy_arcE (D1 D2 : diGraphType) (x y : X2Legacy.x2_disjoint_union D1 D2) :
  (x --> y) = X2Legacy.x2_disjoint_union_rel x y.
Proof.
by [].
Qed.

Lemma x2_disjoint_union_arcE (D1 D2 : diGraphType) (x y : Digraph.conjectures.X2.x2_disjoint_union D1 D2) :
  (x --> y) = Digraph.conjectures.X2.x2_disjoint_union_rel x y.
Proof.
by [].
Qed.

(** The current row. *)
Lemma delta_plus_maderian_disjoint_union_statement_compat :
  X2Legacy.delta_plus_maderian_disjoint_union_statement <->
  Digraph.conjectures.X2.delta_plus_maderian_disjoint_union_statement.
Proof.
rewrite /X2Legacy.delta_plus_maderian_disjoint_union_statement.
reflexivity.
Qed.

(** The complete B1+A28 row: B1's raw Maderian chain converts to the live one (B1's [delta_plus_maderian_compat]), and
    the frozen sum to the live sum. *)
Lemma delta_plus_maderian_disjoint_union_statement_original_compat :
  X2Original.delta_plus_maderian_disjoint_union_statement <->
  Digraph.conjectures.X2.delta_plus_maderian_disjoint_union_statement.
Proof.
rewrite /X2Original.delta_plus_maderian_disjoint_union_statement.
reflexivity.
Qed.
