(** * Chromatic.migration.delete_edge -- frozen single-edge deletion certificates

    Batch A, family A3 ([delete_edge_rel], [delete_edge_graph]), X64 row.
    [Legacy] freezes the helpers verbatim as they stood at dbee364, before the
    migration: the relation [(x -- y) && ([set x; y] != e)], its symmetry and
    irreflexivity lemmas, and the [SGraph] built from them.  [X64Legacy] freezes
    the affected chain ([x64_bridgeless]) and the statement; [X64Original] also
    freezes M1's edge set, so it is the row as it stood before both migrations.

    The live helpers now unfold to [del_es_rel G [set e]] and
    [del_edge_set G [set e]].  For every vertex set [e], valid edge or not, the
    frozen and live adjacencies agree pointwise ([x64_delete_edge_rel_compat],
    from [GTBase.common.del_edge_set1]); the identity is then an isomorphism of the
    deleted graphs, and connectivity moves along it by [iso_connected].

    Historical snapshot: M1's [Chromatic.migration.simple_edges.X64Legacy.bridgeless]
    froze only the edge set and still calls the live [x64_delete_edge_graph]; it
    is kept unchanged, and [X64Original] is the fully frozen replacement.  The
    regeneration spec is meta/migration_reports/delete_edge.spec.json. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X63 X64.
From Chromatic.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x64_delete_edge_rel (G : sgraph) (e : {set G}) : rel G :=
  fun x y => (x -- y) && ([set x; y] != e).

Lemma x64_delete_edge_sym (G : sgraph) (e : {set G}) :
  symmetric (@Legacy.x64_delete_edge_rel G e).
Proof. by move=> x y; rewrite /Legacy.x64_delete_edge_rel sgP setUC. Qed.

Lemma x64_delete_edge_irrefl (G : sgraph) (e : {set G}) :
  irreflexive (@Legacy.x64_delete_edge_rel G e).
Proof. by move=> x; rewrite /Legacy.x64_delete_edge_rel sg_irrefl. Qed.

Definition x64_delete_edge_graph (G : sgraph) (e : {set G}) : sgraph :=
  SGraph (@Legacy.x64_delete_edge_sym G e) (@Legacy.x64_delete_edge_irrefl G e).

End Legacy.

(** ** Helper certificates *)

(** Unconditional: [e] need not be an edge, nor a two-element set. *)
Lemma x64_delete_edge_rel_compat (G : sgraph) (e : {set G}) :
  @Legacy.x64_delete_edge_rel G e =2 @x64_delete_edge_rel G e.
Proof.
by move=> x y; rewrite /Legacy.x64_delete_edge_rel /x64_delete_edge_rel /del_es_rel /= inE.
Qed.

Lemma x64_delete_edge_graph_compat (G : sgraph) (e : {set G}) :
  @edge_rel (@Legacy.x64_delete_edge_graph G e) =2 @edge_rel (@x64_delete_edge_graph G e).
Proof. by move=> x y; exact: (@x64_delete_edge_rel_compat G e x y). Qed.

Lemma x64_delete_edge_diso (G : sgraph) (e : {set G}) :
  @Legacy.x64_delete_edge_graph G e ≃ @x64_delete_edge_graph G e.
Proof.
rewrite /Legacy.x64_delete_edge_graph; apply: del_edge_set_eq_diso => x y.
exact: (@x64_delete_edge_rel_compat G e x y).
Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the two constructions; it does not equate
    the opaque proof terms. *)
Lemma x64_delete_edge_proofs_compat (G : sgraph) (e : {set G}) :
  SGraph (@Legacy.x64_delete_edge_sym G e) (@Legacy.x64_delete_edge_irrefl G e) ≃
  SGraph (@x64_delete_edge_sym G e) (@x64_delete_edge_irrefl G e).
Proof. by apply: eq_diso => x y; exact: (@x64_delete_edge_rel_compat G e x y). Qed.

(** ** X64 *)

Module X64Legacy.

Definition bridgeless (G : sgraph) : Prop :=
  forall e : {set G},
    e \in x64_edge_set G ->
    connected [set: @Legacy.x64_delete_edge_graph G e].

Definition finite_bridgeless_cubic_two_homogeneous_exceptions_statement : Prop :=
  exists N : nat,
    forall G : sgraph,
      connected [set: G] ->
      regular G 3 ->
      bridgeless G ->
      N <= #|G| ->
      x63_k_homogeneous_colouring G 2.

End X64Legacy.

Lemma x64_bridgeless_compat (G : sgraph) :
  X64Legacy.bridgeless G <-> x64_bridgeless G.
Proof.
split=> bl e eE; move: (bl e eE); apply: iso_connected.
- exact: diso_sym (@x64_delete_edge_diso G e).
- exact: @x64_delete_edge_diso G e.
Qed.

Lemma finite_bridgeless_cubic_two_homogeneous_exceptions_statement_compat :
  X64Legacy.finite_bridgeless_cubic_two_homogeneous_exceptions_statement <->
  finite_bridgeless_cubic_two_homogeneous_exceptions_statement.
Proof.
split=> -[N bound]; exists N => G conn reg bl size; apply: bound conn reg _ size.
- exact/x64_bridgeless_compat.
- exact/x64_bridgeless_compat.
Qed.

(** ** X64 before M1 and A3 *)

Module X64Original.

Definition bridgeless (G : sgraph) : Prop :=
  forall e : {set G},
    e \in simple_edges.Legacy.exists_edge_set G ->
    connected [set: @Legacy.x64_delete_edge_graph G e].

Definition finite_bridgeless_cubic_two_homogeneous_exceptions_statement : Prop :=
  exists N : nat,
    forall G : sgraph,
      connected [set: G] ->
      regular G 3 ->
      bridgeless G ->
      N <= #|G| ->
      x63_k_homogeneous_colouring G 2.

End X64Original.

Lemma x64_bridgeless_original_compat (G : sgraph) :
  X64Original.bridgeless G <-> x64_bridgeless G.
Proof.
rewrite -x64_bridgeless_compat /X64Original.bridgeless /X64Legacy.bridgeless.
by rewrite simple_edges.x64_edge_set_compat.
Qed.

Lemma finite_bridgeless_cubic_two_homogeneous_exceptions_statement_original_compat :
  X64Original.finite_bridgeless_cubic_two_homogeneous_exceptions_statement <->
  finite_bridgeless_cubic_two_homogeneous_exceptions_statement.
Proof.
split=> -[N bound]; exists N => G conn reg bl size; apply: bound conn reg _ size.
- exact/x64_bridgeless_original_compat.
- exact/x64_bridgeless_original_compat.
Qed.
