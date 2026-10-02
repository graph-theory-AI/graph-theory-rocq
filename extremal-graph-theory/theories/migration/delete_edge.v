(** * Extremal.migration.delete_edge -- frozen single-edge deletion certificates

    Batch A, family A3 ([delete_edge_rel], [delete_edge_graph]): X60, and X61
    across modules.  [Legacy] freezes X60's helpers verbatim as they stood at
    dbee364, before the migration: the relation [(x -- y) && ([set x; y] != e)],
    its symmetry and irreflexivity lemmas, and the [SGraph] built from them.
    [X60Legacy] and [X61Legacy] freeze the affected chains (X61's
    [x61_induced_saturated]) and the statements.  [X60Original] also freezes M1's
    edge set; [X61Original] freezes M1's edge set and A1's induced-free helper
    too, so both are the rows as they stood before every migration that touched
    them.

    The live helpers now unfold to [del_es_rel G [set e]] and
    [del_edge_set G [set e]].  For every vertex set [e], valid edge or not, the
    frozen and live adjacencies agree pointwise ([x60_delete_edge_rel_compat]),
    so the identity is an isomorphism of the deleted graphs.  X60's induced
    cycles move along it by [induced_copy_host_diso]; X61's [x61_induced_free] of
    the deleted graph, the HOST argument, by [induced_free_host_diso].

    Historical snapshots: A1's [Extremal.migration.induced_free.X61Legacy] and
    [X61Original] froze the induced-free chain and still call the live
    [x60_delete_edge_graph]; they are kept unchanged, and [X61Original] here is the
    fully frozen replacement.  The regeneration spec is
    meta/migration_reports/delete_edge.spec.json. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X49 X60 X61.
From Extremal.migration Require simple_edges induced_free.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x60_delete_edge_rel (G : sgraph) (e : {set G}) : rel G :=
  fun x y => (x -- y) && ([set x; y] != e).

Lemma x60_delete_edge_sym (G : sgraph) (e : {set G}) :
  symmetric (@Legacy.x60_delete_edge_rel G e).
Proof. by move=> x y; rewrite /Legacy.x60_delete_edge_rel sgP setUC. Qed.

Lemma x60_delete_edge_irrefl (G : sgraph) (e : {set G}) :
  irreflexive (@Legacy.x60_delete_edge_rel G e).
Proof. by move=> x; rewrite /Legacy.x60_delete_edge_rel sg_irrefl. Qed.

Definition x60_delete_edge_graph (G : sgraph) (e : {set G}) : sgraph :=
  SGraph (@Legacy.x60_delete_edge_sym G e) (@Legacy.x60_delete_edge_irrefl G e).

End Legacy.

(** ** Helper certificates *)

(** Unconditional: [e] need not be an edge, nor a two-element set. *)
Lemma x60_delete_edge_rel_compat (G : sgraph) (e : {set G}) :
  @Legacy.x60_delete_edge_rel G e =2 @x60_delete_edge_rel G e.
Proof.
by move=> x y; rewrite /Legacy.x60_delete_edge_rel /x60_delete_edge_rel /del_es_rel /= inE.
Qed.

Lemma x60_delete_edge_graph_compat (G : sgraph) (e : {set G}) :
  @edge_rel (@Legacy.x60_delete_edge_graph G e) =2 @edge_rel (@x60_delete_edge_graph G e).
Proof. by move=> x y; exact: (@x60_delete_edge_rel_compat G e x y). Qed.

Lemma x60_delete_edge_diso (G : sgraph) (e : {set G}) :
  @Legacy.x60_delete_edge_graph G e ≃ @x60_delete_edge_graph G e.
Proof.
rewrite /Legacy.x60_delete_edge_graph; apply: del_edge_set_eq_diso => x y.
exact: (@x60_delete_edge_rel_compat G e x y).
Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen symmetry and
    irreflexivity proofs is isomorphic, through the identity, to the one built from
    the retained live lemmas.  It relates the two constructions; it does not equate
    the opaque proof terms. *)
Lemma x60_delete_edge_proofs_compat (G : sgraph) (e : {set G}) :
  SGraph (@Legacy.x60_delete_edge_sym G e) (@Legacy.x60_delete_edge_irrefl G e) ≃
  SGraph (@x60_delete_edge_sym G e) (@x60_delete_edge_irrefl G e).
Proof. by apply: eq_diso => x y; exact: (@x60_delete_edge_rel_compat G e x y). Qed.

(** ** Transport of the statements' graph properties *)

Lemma x60_has_induced_cycle_diso (G G' : sgraph) (n : nat) :
  G ≃ G' -> x60_has_induced_cycle G n -> x60_has_induced_cycle G' n.
Proof.
move=> i [S [Sn [j]]]; have [S' [S'S cyc]] := induced_copy_host_diso i j.
by exists S'; rewrite S'S.
Qed.

(** ** X60 *)

Module X60Legacy.

Definition induced_saturation_even_cycle_polynomial_size_statement : Prop :=
  exists p : seq nat,
    forall t : nat,
      3 <= t ->
      exists G : sgraph,
        #|G| <= x60_poly_eval p t /\
        0 < #|x60_edge_set G| /\
        ~ x60_has_induced_cycle G (2 * t - 2) /\
        forall e : {set G},
          e \in x60_edge_set G ->
          x60_has_induced_cycle (@Legacy.x60_delete_edge_graph G e) (2 * t - 2).

End X60Legacy.

Lemma induced_saturation_even_cycle_polynomial_size_statement_compat :
  X60Legacy.induced_saturation_even_cycle_polynomial_size_statement <->
  induced_saturation_even_cycle_polynomial_size_statement.
Proof.
split=> -[p sat]; exists p => t t3; have [G [size [edges [nocyc del]]]] := sat t t3.
all: exists G; (split; [exact: size | split; [exact: edges | split; [exact: nocyc | ]]]).
- move=> e eE; apply: x60_has_induced_cycle_diso (del e eE).
  exact: @x60_delete_edge_diso G e.
- move=> e eE; apply: x60_has_induced_cycle_diso (del e eE).
  exact: diso_sym (@x60_delete_edge_diso G e).
Qed.

(** ** X60 before M1 and A3 *)

Module X60Original.

Definition induced_saturation_even_cycle_polynomial_size_statement : Prop :=
  exists p : seq nat,
    forall t : nat,
      3 <= t ->
      exists G : sgraph,
        #|G| <= x60_poly_eval p t /\
        0 < #|simple_edges.Legacy.edge_set G| /\
        ~ x60_has_induced_cycle G (2 * t - 2) /\
        forall e : {set G},
          e \in simple_edges.Legacy.edge_set G ->
          x60_has_induced_cycle (@Legacy.x60_delete_edge_graph G e) (2 * t - 2).

End X60Original.

Lemma induced_saturation_even_cycle_polynomial_size_statement_original_compat :
  X60Original.induced_saturation_even_cycle_polynomial_size_statement <->
  induced_saturation_even_cycle_polynomial_size_statement.
Proof.
rewrite -induced_saturation_even_cycle_polynomial_size_statement_compat.
split=> -[p sat]; exists p => t t3; have [G [size [edges [nocyc del]]]] := sat t t3.
- by exists G; rewrite -simple_edges.x60_edge_set_compat.
- by exists G; rewrite simple_edges.x60_edge_set_compat.
Qed.

(** ** X61 (reaches the family through [x61_induced_saturated], across modules) *)

Module X61Legacy.

Definition induced_saturated (H G : sgraph) : Prop :=
  x61_induced_free G H /\
  (forall a b : G,
    a != b ->
    ~~ (a -- b) ->
    x61_induced_free (@x49_add_edge_graph G a b) H -> False) /\
  forall e : {set G},
    e \in x60_edge_set G ->
    x61_induced_free (@Legacy.x60_delete_edge_graph G e) H -> False.

Definition infinite_family_without_finite_induced_saturation_statement : Prop :=
  exists F : sgraph -> Prop,
    x61_infinite_family F /\
    forall H : sgraph,
      F H ->
      x61_neither_clique_nor_stable H /\
      forall G : sgraph, ~ induced_saturated H G.

End X61Legacy.

(** [x61_induced_free] of a deleted graph: the deleted graph is the HOST. *)
Lemma x61_induced_free_delete_edge_compat (G H : sgraph) (e : {set G}) :
  x61_induced_free (@Legacy.x60_delete_edge_graph G e) H <->
  x61_induced_free (@x60_delete_edge_graph G e) H.
Proof.
split; apply: induced_free_host_diso.
- exact: @x60_delete_edge_diso G e.
- exact: diso_sym (@x60_delete_edge_diso G e).
Qed.

Lemma x61_induced_saturated_compat (H G : sgraph) :
  X61Legacy.induced_saturated H G <-> x61_induced_saturated H G.
Proof.
split=> -[free [add del]]; (split; [exact: free | split; [exact: add | ]]).
- move=> e eE h; apply: (del e eE).
  exact: proj2 (@x61_induced_free_delete_edge_compat G H e) h.
- move=> e eE h; apply: (del e eE).
  exact: proj1 (@x61_induced_free_delete_edge_compat G H e) h.
Qed.

Lemma infinite_family_without_finite_induced_saturation_statement_compat :
  X61Legacy.infinite_family_without_finite_induced_saturation_statement <->
  infinite_family_without_finite_induced_saturation_statement.
Proof.
split=> -[F [inf members]]; exists F; split=> // H FH;
  have [neither nosat] := members H FH; split=> // G /x61_induced_saturated_compat;
  exact: nosat.
Qed.

(** ** X61 before M1, A1 and A3 *)

Module X61Original.

Definition induced_saturated (H G : sgraph) : Prop :=
  Extremal.migration.induced_free.Legacy.x61_induced_free G H /\
  (forall a b : G,
    a != b ->
    ~~ (a -- b) ->
    Extremal.migration.induced_free.Legacy.x61_induced_free (@x49_add_edge_graph G a b) H -> False) /\
  forall e : {set G},
    e \in simple_edges.Legacy.edge_set G ->
    Extremal.migration.induced_free.Legacy.x61_induced_free (@Legacy.x60_delete_edge_graph G e) H -> False.

Definition infinite_family_without_finite_induced_saturation_statement : Prop :=
  exists F : sgraph -> Prop,
    x61_infinite_family F /\
    forall H : sgraph,
      F H ->
      x61_neither_clique_nor_stable H /\
      forall G : sgraph, ~ induced_saturated H G.

End X61Original.

Lemma x61_induced_saturated_original_compat (H G : sgraph) :
  X61Original.induced_saturated H G <-> x61_induced_saturated H G.
Proof.
rewrite -x61_induced_saturated_compat /X61Original.induced_saturated.
rewrite /X61Legacy.induced_saturated simple_edges.x60_edge_set_compat.
split=> -[free [add del]]; (split; [ | split]).
- exact/Extremal.migration.induced_free.x61_induced_free_compat.
- by move=> a b ab nab /Extremal.migration.induced_free.x61_induced_free_compat; exact: add.
- by move=> e eE /Extremal.migration.induced_free.x61_induced_free_compat; exact: del.
- exact/Extremal.migration.induced_free.x61_induced_free_compat.
- by move=> a b ab nab /Extremal.migration.induced_free.x61_induced_free_compat; exact: add.
- by move=> e eE /Extremal.migration.induced_free.x61_induced_free_compat; exact: del.
Qed.

Lemma infinite_family_without_finite_induced_saturation_statement_original_compat :
  X61Original.infinite_family_without_finite_induced_saturation_statement <->
  infinite_family_without_finite_induced_saturation_statement.
Proof.
split=> -[F [inf members]]; exists F; split=> // H FH;
  have [neither nosat] := members H FH; split=> // G /x61_induced_saturated_original_compat;
  exact: nosat.
Qed.
