(** * Chromatic.conjectures.implications_X66 -- dependency-graph EDGES for wave X66.

    Machine-checked implication edges whose TARGET is the X66 row
    [good_trees_disjoint_union_good_statement].  Every SCHEDULED edge is a
    RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving
    either endpoint.  Axiom-free: no [Axiom] / [Parameter] / [Admitted] /
    [Conjecture].

    The [cite="gc:eNNN"] fields point at [meta/corpus_relations.json]. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding poly_forms.
From Chromatic.conjectures Require Import U8 X3 X66 X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The X66 disjoint union of two forests is a forest ******************)

(** [x66_disjoint_union] is the coq-graph-theory disjoint union [sjoin] (same
    vertex sum, same adjacency relation), so the library's forest lemma for
    [sjoin] applies: [GraphTheory.treewidth.join_is_forest] states
    [is_forest [set: T1 ∔ T2]] for forests [T1], [T2] packaged as the record
    type [forest].  (The earlier X218 note claiming coq-graph-theory has no
    disjoint-union forest lemma is stale.) *)
Lemma x66_union_forest (H1 H2 : sgraph) :
  is_forest [set: H1] -> is_forest [set: H2] ->
  is_forest [set: x66_disjoint_union H1 H2].
Proof. by move=> f1 f2; exact: (@join_is_forest (@Forest H1 f1) (@Forest H2 f2)). Qed.

(** ** Every forest is good ==> good trees have a good disjoint union *****)

(*@EDGE from=every_forest_is_good_statement to=good_trees_disjoint_union_good_statement kind=implies status=verified proved=true proof=every_forest_is_good_implies_good_trees_disjoint_union_good cite="gc:e036" note="Corpus relation e036 (confirmed): the disjoint union of two trees is a forest, so the source makes the target's conclusion hold UNCONDITIONALLY -- the target's two goodness hypotheses on H1 and H2 are not needed, exactly as the corpus argument says. Both bridges recorded as missing by the earlier candidate annotation are now available: (a) is_forest [set: x66_disjoint_union H1 H2] is the library lemma GraphTheory.treewidth.join_is_forest, since x66_disjoint_union is sjoin (x66_union_forest, this file); (b) the coefficient-list versus c * omega^d normal-form conversion is foundations/poly_forms.v (poly_chi_bounded_x3W), since X66 states goodness through x3_polynomially_chi_bounded." *)
Theorem every_forest_is_good_implies_good_trees_disjoint_union_good :
  every_forest_is_good_statement -> good_trees_disjoint_union_good_statement.
Proof.
move=> X H1 H2 [f1 _] [f2 _] _ _.
by apply: poly_chi_bounded_x3W; apply: X; exact: x66_union_forest.
Qed.

Print Assumptions x66_union_forest.
Print Assumptions every_forest_is_good_implies_good_trees_disjoint_union_good.
