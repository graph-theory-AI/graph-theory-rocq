(** * GTMisc.migration.complement -- frozen ordinary graph-complement certificates

    Batch A, family A6 (ordinary complement), the X29 row.  [Legacy] freezes each relation
    [(x != y) && ~~ (x -- y)], its symmetry and irreflexivity proof scripts and the [SGraph]
    built from them, verbatim at 49ddc03 except that references to the frozen names are
    [Legacy.]-qualified.  The live helpers now unfold to upstream [compl_rel] and [compl]; the
    relations agree by conversion, and the graphs are related by the identity isomorphism
    ([compl_eq_diso]), which does not equate the opaque proof fields.  Row certificates move
    each statement along that isomorphism: as a pattern of [induced_free], as the host of an
    induced cycle or of an ordinary subgraph, or through the same witness of a class.
    The regeneration spec is meta/migration_reports/complement.spec.json. *)

From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From GTMisc.conjectures Require Import X29.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

Module Legacy.

Definition x29_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma x29_complement_sym (G : sgraph) : symmetric (@Legacy.x29_complement_rel G).
Proof. by move=> x y; rewrite /Legacy.x29_complement_rel eq_sym sg_sym. Qed.

Lemma x29_complement_irrefl (G : sgraph) : irreflexive (@Legacy.x29_complement_rel G).
Proof. by move=> x; rewrite /Legacy.x29_complement_rel eqxx. Qed.

Definition x29_complement (G : sgraph) : sgraph :=
  SGraph (@Legacy.x29_complement_sym G) (@Legacy.x29_complement_irrefl G).

End Legacy.

Module X29Legacy.

Definition no_c5_c7_complement_c7_normal_graph_statement : Prop :=
  forall G : sgraph,
    ~ x29_has_induced_cycle G 5 ->
    ~ x29_has_induced_cycle G 7 ->
    ~ x29_has_induced_cycle (Legacy.x29_complement G) 7 ->
    x29_normal_graph G.

End X29Legacy.

(** ** Helper certificates *)

Lemma x29_complement_rel_compat (G : sgraph) : @Legacy.x29_complement_rel G =2 @x29_complement_rel G.
Proof. by move=> x y. Qed.

Lemma x29_complement_compat (G : sgraph) :
  @edge_rel (Legacy.x29_complement G) =2 @edge_rel (x29_complement G).
Proof. by move=> x y. Qed.

(** The identity is an isomorphism of the frozen and live complements. *)
Lemma x29_complement_diso (G : sgraph) : Legacy.x29_complement G ≃ x29_complement G.
Proof. by rewrite /Legacy.x29_complement; apply: compl_eq_diso => x y. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen proofs is isomorphic,
    through the identity, to the one built from the retained live lemmas (no proof-term claim). *)
Lemma x29_complement_proofs_compat (G : sgraph) :
  SGraph (@Legacy.x29_complement_sym G) (@Legacy.x29_complement_irrefl G) ≃ SGraph (@x29_complement_sym G) (@x29_complement_irrefl G).
Proof. by apply: eq_diso => x y. Qed.


(** ** X29: induced cycles move along a host isomorphism, keeping their size *)

Lemma x29_has_induced_cycle_diso (G G' : sgraph) (n : nat) :
  G ≃ G' -> x29_has_induced_cycle G n -> x29_has_induced_cycle G' n.
Proof.
move=> i [S [Sn [j]]]; have [S' [S'S cyc]] := induced_copy_host_diso i j.
by exists S'; rewrite S'S.
Qed.

Lemma no_c5_c7_complement_c7_normal_graph_statement_compat :
  X29Legacy.no_c5_c7_complement_c7_normal_graph_statement <->
  no_c5_c7_complement_c7_normal_graph_statement.
Proof.
split=> h G n5 n7 nc7; apply: (h G n5 n7) => hc; apply: nc7.
- exact: x29_has_induced_cycle_diso (x29_complement_diso G) hc.
- exact: x29_has_induced_cycle_diso (diso_sym (x29_complement_diso G)) hc.
Qed.

Print Assumptions x29_complement_rel_compat.
Print Assumptions x29_complement_compat.
Print Assumptions x29_complement_diso.
Print Assumptions x29_complement_proofs_compat.
Print Assumptions x29_has_induced_cycle_diso.
Print Assumptions no_c5_c7_complement_c7_normal_graph_statement_compat.
