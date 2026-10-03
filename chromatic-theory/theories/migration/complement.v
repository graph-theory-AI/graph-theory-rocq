(** * Chromatic.migration.complement -- frozen ordinary graph-complement certificates

    Batch A, family A6 (ordinary complement), X3 and the chromatic XE2 row.  [Legacy] freezes each relation
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
From Chromatic.conjectures Require Import U8 X3 XE2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

Module Legacy.

Definition x3_complement_rel (G : sgraph) : rel G :=
  fun u v => (u != v) && ~~ (u -- v).

Lemma x3_complement_sym (G : sgraph) : symmetric (@Legacy.x3_complement_rel G).
Proof. by move=> u v; rewrite /Legacy.x3_complement_rel eq_sym sgP. Qed.

Lemma x3_complement_irrefl (G : sgraph) : irreflexive (@Legacy.x3_complement_rel G).
Proof. by move=> u; rewrite /Legacy.x3_complement_rel eqxx. Qed.

Definition x3_complement_graph (G : sgraph) : sgraph :=
  SGraph (@Legacy.x3_complement_sym G) (@Legacy.x3_complement_irrefl G).

Definition xe2_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma xe2_complement_sym (G : sgraph) : symmetric (@Legacy.xe2_complement_rel G).
Proof. by move=> x y; rewrite /Legacy.xe2_complement_rel eq_sym sgP. Qed.

Lemma xe2_complement_irrefl (G : sgraph) : irreflexive (@Legacy.xe2_complement_rel G).
Proof. by move=> x; rewrite /Legacy.xe2_complement_rel eqxx. Qed.

Definition xe2_complement_graph (G : sgraph) : sgraph :=
  SGraph (@Legacy.xe2_complement_sym G) (@Legacy.xe2_complement_irrefl G).

End Legacy.

Module X3Legacy.

Definition complement_image (C : sgraph -> Prop) (G : sgraph) : Prop :=
  exists H : sgraph, C H /\ x3_iso G (Legacy.x3_complement_graph H).

Definition gyarfas_complementation_chi_bounded_statement : Prop :=
  forall (c : nat) (C : sgraph -> Prop),
    x3_chi_omega_plus_bound C c ->
    chi_bounded (complement_image C).

End X3Legacy.

Module XE2Legacy.

Definition erdos_753_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (G : sgraph) (n chG chGc : nat),
      #|G| = n ->
      0 < n ->
      is_choice_number G chG ->
      is_choice_number (Legacy.xe2_complement_graph G) chGc ->
      xe2_above_half_plus_rational_power n cnum cden (chG + chGc).

End XE2Legacy.

(** ** Helper certificates *)

Lemma x3_complement_rel_compat (G : sgraph) : @Legacy.x3_complement_rel G =2 @x3_complement_rel G.
Proof. by move=> x y. Qed.

Lemma x3_complement_graph_compat (G : sgraph) :
  @edge_rel (Legacy.x3_complement_graph G) =2 @edge_rel (x3_complement_graph G).
Proof. by move=> x y. Qed.

(** The identity is an isomorphism of the frozen and live complements. *)
Lemma x3_complement_diso (G : sgraph) : Legacy.x3_complement_graph G ≃ x3_complement_graph G.
Proof. by rewrite /Legacy.x3_complement_graph; apply: compl_eq_diso => x y. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen proofs is isomorphic,
    through the identity, to the one built from the retained live lemmas (no proof-term claim). *)
Lemma x3_complement_proofs_compat (G : sgraph) :
  SGraph (@Legacy.x3_complement_sym G) (@Legacy.x3_complement_irrefl G) ≃ SGraph (@x3_complement_sym G) (@x3_complement_irrefl G).
Proof. by apply: eq_diso => x y. Qed.

Lemma xe2_complement_rel_compat (G : sgraph) : @Legacy.xe2_complement_rel G =2 @xe2_complement_rel G.
Proof. by move=> x y. Qed.

Lemma xe2_complement_graph_compat (G : sgraph) :
  @edge_rel (Legacy.xe2_complement_graph G) =2 @edge_rel (xe2_complement_graph G).
Proof. by move=> x y. Qed.

(** The identity is an isomorphism of the frozen and live complements. *)
Lemma xe2_complement_diso (G : sgraph) : Legacy.xe2_complement_graph G ≃ xe2_complement_graph G.
Proof. by rewrite /Legacy.xe2_complement_graph; apply: compl_eq_diso => x y. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen proofs is isomorphic,
    through the identity, to the one built from the retained live lemmas (no proof-term claim). *)
Lemma xe2_complement_proofs_compat (G : sgraph) :
  SGraph (@Legacy.xe2_complement_sym G) (@Legacy.xe2_complement_irrefl G) ≃ SGraph (@xe2_complement_sym G) (@xe2_complement_irrefl G).
Proof. by apply: eq_diso => x y. Qed.


(** ** X3: complements of a class, same witness *)

Lemma x3_complement_image_compat (C : sgraph -> Prop) (G : sgraph) :
  X3Legacy.complement_image C G <-> x3_complement_image C G.
Proof.
split=> -[H [CH [i]]]; exists H; (split; [exact: CH | constructor]).
- exact: diso_comp i (x3_complement_diso H).
- exact: diso_comp i (diso_sym (x3_complement_diso H)).
Qed.

Lemma gyarfas_complementation_chi_bounded_statement_compat :
  X3Legacy.gyarfas_complementation_chi_bounded_statement <->
  gyarfas_complementation_chi_bounded_statement.
Proof.
rewrite /X3Legacy.gyarfas_complementation_chi_bounded_statement /gyarfas_complementation_chi_bounded_statement /chi_bounded.
setoid_rewrite x3_complement_image_compat; reflexivity.
Qed.

(** ** XE2: the choice number of the complement depends only on vertices and adjacency *)

Lemma erdos_753_statement_compat : XE2Legacy.erdos_753_statement <-> erdos_753_statement.
Proof. by rewrite /XE2Legacy.erdos_753_statement /erdos_753_statement. Qed.

Print Assumptions x3_complement_rel_compat.
Print Assumptions x3_complement_graph_compat.
Print Assumptions x3_complement_diso.
Print Assumptions x3_complement_proofs_compat.
Print Assumptions xe2_complement_rel_compat.
Print Assumptions xe2_complement_graph_compat.
Print Assumptions xe2_complement_diso.
Print Assumptions xe2_complement_proofs_compat.
Print Assumptions x3_complement_image_compat.
Print Assumptions gyarfas_complementation_chi_bounded_statement_compat.
Print Assumptions erdos_753_statement_compat.
