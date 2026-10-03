(** * Chromatic.migration.delete_edges -- frozen set-of-edges deletion certificates

    Batch A, family A2 ([delete_edges], [delete_edges_rel]).  [Legacy] freezes
    the conjecture-local helpers verbatim as they stood at 03742d1, before the
    migration, together with their opaque proof dependencies: the relation,
    its symmetry and irreflexivity lemmas, and the [SGraph] built from them.
    [X7Legacy] and [XE1Legacy] freeze the affected chain of every statement,
    the statements included, with every reference to a helper of this family
    replaced by its frozen copy.

    The live helpers now unfold to [GTBase.common.del_es_rel] and
    [GTBase.common.del_edge_set].  A frozen graph and its live counterpart have
    the same vertex type and the same adjacency ([*_delete_edges_compat]), so
    the identity is an isomorphism between them ([*_delete_edges_diso]); the
    chromatic numbers in the statements move along it by [chi_diso].  The
    regeneration spec is meta/migration_reports/delete_edges.spec.json. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import XE1 X7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x7_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma x7_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@Legacy.x7_delete_edges_rel G F).
Proof.
move=> x y; rewrite /Legacy.x7_delete_edges_rel.
rewrite sgP.
by rewrite setUC.
Qed.

Lemma x7_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@Legacy.x7_delete_edges_rel G F).
Proof. by move=> x; rewrite /Legacy.x7_delete_edges_rel sg_irrefl. Qed.

Definition x7_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@Legacy.x7_delete_edges_sym G F) (@Legacy.x7_delete_edges_irrefl G F).

Definition xe1_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma xe1_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@Legacy.xe1_delete_edges_rel G F).
Proof.
move=> x y; rewrite /Legacy.xe1_delete_edges_rel.
rewrite sgP.
by rewrite setUC.
Qed.

Lemma xe1_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@Legacy.xe1_delete_edges_rel G F).
Proof. by move=> x; rewrite /Legacy.xe1_delete_edges_rel sg_irrefl. Qed.

Definition xe1_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@Legacy.xe1_delete_edges_sym G F) (@Legacy.xe1_delete_edges_irrefl G F).

End Legacy.

(** ** Helper certificates *)

Lemma x7_delete_edges_rel_compat (G : sgraph) (F : {set {set G}}) :
  @Legacy.x7_delete_edges_rel G F = @x7_delete_edges_rel G F.
Proof. by []. Qed.

Lemma x7_delete_edges_compat (G : sgraph) (F : {set {set G}}) :
  @edge_rel (@Legacy.x7_delete_edges G F) =2 @edge_rel (@x7_delete_edges G F).
Proof. by []. Qed.

Lemma x7_delete_edges_diso (G : sgraph) (F : {set {set G}}) :
  @Legacy.x7_delete_edges G F ≃ @x7_delete_edges G F.
Proof. by rewrite /Legacy.x7_delete_edges; apply: del_edge_set_eq_diso. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the two constructions; it does not equate
    the opaque proof terms. *)
Lemma x7_delete_edges_proofs_compat (G : sgraph) (F : {set {set G}}) :
  SGraph (@Legacy.x7_delete_edges_sym G F) (@Legacy.x7_delete_edges_irrefl G F) ≃
  SGraph (@x7_delete_edges_sym G F) (@x7_delete_edges_irrefl G F).
Proof. by apply: eq_diso => x y. Qed.

Lemma xe1_delete_edges_rel_compat (G : sgraph) (F : {set {set G}}) :
  @Legacy.xe1_delete_edges_rel G F = @xe1_delete_edges_rel G F.
Proof. by []. Qed.

Lemma xe1_delete_edges_compat (G : sgraph) (F : {set {set G}}) :
  @edge_rel (@Legacy.xe1_delete_edges G F) =2 @edge_rel (@xe1_delete_edges G F).
Proof. by []. Qed.

Lemma xe1_delete_edges_diso (G : sgraph) (F : {set {set G}}) :
  @Legacy.xe1_delete_edges G F ≃ @xe1_delete_edges G F.
Proof. by rewrite /Legacy.xe1_delete_edges; apply: del_edge_set_eq_diso. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the two constructions; it does not equate
    the opaque proof terms. *)
Lemma xe1_delete_edges_proofs_compat (G : sgraph) (F : {set {set G}}) :
  SGraph (@Legacy.xe1_delete_edges_sym G F) (@Legacy.xe1_delete_edges_irrefl G F) ≃
  SGraph (@xe1_delete_edges_sym G F) (@xe1_delete_edges_irrefl G F).
Proof. by apply: eq_diso => x y. Qed.

(** ** X7 *)

Module X7Legacy.

Definition no_critical_edge (G : sgraph) (k : nat) : Prop :=
  forall F : {set G},
    F \in @xe1_edge_set G ->
    χ([set: @Legacy.x7_delete_edges G [set F]]) = k.

Definition edge_deletion_preserves_chromatic
    (G : sgraph) (k r : nat) : Prop :=
  forall R : {set {set G}},
    R \subset @xe1_edge_set G ->
    #|R| <= r ->
    χ([set: @Legacy.x7_delete_edges G R]) = k.

Definition four_one_graph (G : sgraph) : Prop :=
  χ([set: G]) = 4 /\
  xe1_vertex_critical G 4 /\
  no_critical_edge G 4.

Definition fixed_k_vertex_critical_edge_robust_statement : Prop :=
  forall k r : nat, 4 <= k ->
    exists G : sgraph,
      χ([set: G]) = k /\
      xe1_vertex_critical G k /\
      edge_deletion_preserves_chromatic G k r.

Definition six_regular_four_one_graph_statement : Prop :=
  exists G : sgraph,
    regular G 6 /\ four_one_graph G.

End X7Legacy.

Lemma x7_no_critical_edge_compat (G : sgraph) (k : nat) :
  X7Legacy.no_critical_edge G k <-> x7_no_critical_edge G k.
Proof.
split=> crit F FE; rewrite -(crit F FE).
all: by rewrite (chi_diso (@x7_delete_edges_diso G [set F])).
Qed.

Lemma x7_edge_deletion_preserves_chromatic_compat (G : sgraph) (k r : nat) :
  X7Legacy.edge_deletion_preserves_chromatic G k r <->
  x7_edge_deletion_preserves_chromatic G k r.
Proof.
split=> keep R RE Rr; rewrite -(keep R RE Rr).
all: by rewrite (chi_diso (@x7_delete_edges_diso G R)).
Qed.

Lemma x7_four_one_graph_compat (G : sgraph) :
  X7Legacy.four_one_graph G <-> x7_four_one_graph G.
Proof.
split=> -[chiG [crit nocrit]]; (split; [exact: chiG | split; [exact: crit | ]]).
- exact/x7_no_critical_edge_compat.
- exact/x7_no_critical_edge_compat.
Qed.

Lemma fixed_k_vertex_critical_edge_robust_statement_compat :
  X7Legacy.fixed_k_vertex_critical_edge_robust_statement <->
  fixed_k_vertex_critical_edge_robust_statement.
Proof.
split=> st k r k4; have [G [chiG [crit keep]]] := st k r k4; exists G.
all: (split; [exact: chiG | split; [exact: crit | ]]).
- exact/x7_edge_deletion_preserves_chromatic_compat.
- exact/x7_edge_deletion_preserves_chromatic_compat.
Qed.

Lemma six_regular_four_one_graph_statement_compat :
  X7Legacy.six_regular_four_one_graph_statement <->
  six_regular_four_one_graph_statement.
Proof.
split=> -[G [reg four]]; exists G; (split; [exact: reg | ]).
- exact/x7_four_one_graph_compat.
- exact/x7_four_one_graph_compat.
Qed.

(** ** XE1 *)

Module XE1Legacy.

Definition edge_critical_set (G : sgraph) (F : {set {set G}}) (k : nat) : Prop :=
  F \subset @xe1_edge_set G /\ χ([set: @Legacy.xe1_delete_edges G F]) < k.

Definition all_edge_critical_sets_large (G : sgraph) (r k : nat) : Prop :=
  forall F : {set {set G}}, edge_critical_set F k -> r < #|F|.

Definition erdos_944_statement : Prop :=
  forall k r : nat, 4 <= k -> 1 <= r ->
    exists G : sgraph,
      χ([set: G]) = k /\
      xe1_vertex_critical G k /\
      all_edge_critical_sets_large G r k.

End XE1Legacy.

Lemma xe1_edge_critical_set_compat (G : sgraph) (F : {set {set G}}) (k : nat) :
  XE1Legacy.edge_critical_set F k <-> xe1_edge_critical_set F k.
Proof.
by rewrite /XE1Legacy.edge_critical_set /xe1_edge_critical_set
  (chi_diso (@xe1_delete_edges_diso G F)).
Qed.

Lemma xe1_all_edge_critical_sets_large_compat (G : sgraph) (r k : nat) :
  XE1Legacy.all_edge_critical_sets_large G r k <-> xe1_all_edge_critical_sets_large G r k.
Proof.
split=> large F crit; apply: large.
- exact/xe1_edge_critical_set_compat.
- exact/xe1_edge_critical_set_compat.
Qed.

Lemma erdos_944_statement_compat :
  XE1Legacy.erdos_944_statement <-> erdos_944_statement.
Proof.
split=> st k r k4 r1; have [G [chiG [crit large]]] := st k r k4 r1; exists G.
all: (split; [exact: chiG | split; [exact: crit | ]]).
all: exact/xe1_all_edge_critical_sets_large_compat.
Qed.
