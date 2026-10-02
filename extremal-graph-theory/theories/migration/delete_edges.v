(** * Extremal.migration.delete_edges -- frozen set-of-edges deletion certificates

    Batch A, family A2 ([delete_edges], [delete_edges_rel]).  [Legacy] freezes
    the conjecture-local helpers verbatim as they stood at 03742d1, before the
    migration, together with their opaque proof dependencies: XE1's relation,
    its symmetry and irreflexivity lemmas and the [SGraph] built from them, and
    X191's [fg_mk_sgraph] graph.  [XE1Legacy], [XE2Legacy] and [X191Legacy]
    freeze the affected chain of every statement, the statements included, with
    every reference to a helper of this family replaced by its frozen copy.
    XE2 reaches the family through the extremal XE1 helper, across modules.

    The live helpers now unfold to [GTBase.common.del_es_rel] and
    [GTBase.common.del_edge_set].  Each frozen graph has the vertex type and
    adjacency of its live counterpart ([*_delete_edges_compat]; for X191 the
    symmetric closure of [fg_mk_sgraph] is undone by symmetry and
    irreflexivity), so the identity is an isomorphism ([*_delete_edges_diso]).
    The statements' graph properties move along it: chromatic number by
    [chi_diso], bipartiteness by [bipartite_diso], balls and bounded diameter
    by [ball_diso] and [xe1_diameter_at_most_diso].  The regeneration spec is
    meta/migration_reports/delete_edges.spec.json. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X4 XE1 XE2 X191.
(* [bij] supplies the inverse notation [i^-1] and [bijK'] used by the transports. *)
From GraphTheory Require Import bij.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe1_delete_edges_rel (G : sgraph) (F : {set {set G}}) : rel G :=
  fun x y => (x -- y) && ([set x; y] \notin F).

Lemma xe1_delete_edges_sym (G : sgraph) (F : {set {set G}}) :
  symmetric (@Legacy.xe1_delete_edges_rel G F).
Proof. by move=> x y; rewrite /Legacy.xe1_delete_edges_rel sgP setUC. Qed.

Lemma xe1_delete_edges_irrefl (G : sgraph) (F : {set {set G}}) :
  irreflexive (@Legacy.xe1_delete_edges_rel G F).
Proof. by move=> x; rewrite /Legacy.xe1_delete_edges_rel sg_irrefl. Qed.

Definition xe1_delete_edges (G : sgraph) (F : {set {set G}}) : sgraph :=
  SGraph (@Legacy.xe1_delete_edges_sym G F) (@Legacy.xe1_delete_edges_irrefl G F).

Definition x191_delete_edges (F : sgraph) (X : {set {set F}}) : sgraph :=
  @fg_mk_sgraph F (fun x y => (x -- y) && ([set x; y] \notin X)).

End Legacy.

(** ** Isomorphism transport for the statements' graph properties *)

Lemma bipartite_diso (G H : sgraph) : G ≃ H -> bipartite G <-> bipartite H.
Proof.
move=> i; split=> -[f fP].
- by exists (f \o i^-1) => x y xy /=; apply: fP; rewrite edge_diso'.
- by exists (f \o i) => x y xy /=; apply: fP; rewrite edge_diso.
Qed.

Lemma ball_diso (G H : sgraph) (i : G ≃ H) (k : nat) (x y : G) :
  (i y \in ball k (i x)) = (y \in ball k x).
Proof.
elim: k y => [|k IH] y /=; first by rewrite !inE (inj_eq (@bij_injective _ _ i)).
rewrite !inE IH; congr (_ || _); apply/bigcupP/bigcupP.
- case=> z zB; rewrite inE => zy; exists (i^-1 z).
  + by rewrite -IH bijK'.
  + by rewrite inE -(edge_diso i) bijK'.
- case=> z zB; rewrite inE => zy; exists (i z); first by rewrite IH.
  by rewrite inE edge_diso.
Qed.

Lemma xe1_diameter_at_most_diso (G H : sgraph) (r : nat) :
  G ≃ H -> xe1_diameter_at_most G r <-> xe1_diameter_at_most H r.
Proof.
move=> i; split=> diam x y.
- by rewrite -[x](bijK' i) -[y](bijK' i) ball_diso; apply: diam.
- by rewrite -(ball_diso i); apply: diam.
Qed.

(** ** Helper certificates *)

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

Lemma x191_delete_edges_compat (F : sgraph) (X : {set {set F}}) :
  @edge_rel (@Legacy.x191_delete_edges F X) =2 @edge_rel (@x191_delete_edges F X).
Proof.
move=> x y; rewrite /Legacy.x191_delete_edges /edge_rel /= /fg_srel /del_es_rel /=.
have [<-|xy] := eqVneq x y; first by rewrite /= sg_irrefl.
by rewrite /= (@sg_sym F y x) setUC orbb.
Qed.

Lemma x191_delete_edges_diso (F : sgraph) (X : {set {set F}}) :
  @Legacy.x191_delete_edges F X ≃ @x191_delete_edges F X.
Proof.
rewrite /Legacy.x191_delete_edges /fg_mk_sgraph; apply: del_edge_set_eq_diso.
exact: x191_delete_edges_compat.
Qed.

(** ** XE1 *)

Module XE1Legacy.

Definition erdos_23_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = 5 * n ->
    triangle_free G ->
    exists F : {set {set G}},
      F \subset x4_edge_set G /\
      #|F| <= n ^ 2 /\
      bipartite (@Legacy.xe1_delete_edges G F).

End XE1Legacy.

Lemma erdos_23_statement_compat :
  XE1Legacy.erdos_23_statement <-> erdos_23_statement.
Proof.
split=> st n G Gn tri; have [F [sub [size bip]]] := st n G Gn tri; exists F.
all: (split; [exact: sub | split; [exact: size | ]]).
all: exact/(bipartite_diso (@xe1_delete_edges_diso G F)).
Qed.

(** ** XE2 (reaches the family through the extremal XE1 helper) *)

Module XE2Legacy.

Definition bipartite_plus_bounded_degree (G : sgraph) (d : nat) : Prop :=
  exists F : {set {set G}},
    F \subset x4_edge_set G /\
    bipartite (@Legacy.xe1_delete_edges G F) /\
    forall v : G, #|[set e in F | v \in e]| < d.

Definition diameter_critical_two (G : sgraph) : Prop :=
  xe1_diameter_at_most G 2 /\
  ~ xe1_diameter_at_most G 1 /\
  forall e : {set G}, e \in x4_edge_set G ->
    ~ xe1_diameter_at_most (@Legacy.xe1_delete_edges G [set e]) 2.

Definition erdos_613_statement : Prop :=
  forall (n : nat) (G : sgraph),
    3 <= n ->
    x4_edge_count G = 'C(2 * n + 1, 2) - 'C(n, 2) - 1 ->
    bipartite_plus_bounded_degree G n.

Definition erdos_742_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    diameter_critical_two G ->
    4 * x4_edge_count G <= n ^ 2.

End XE2Legacy.

Lemma xe2_bipartite_plus_bounded_degree_compat (G : sgraph) (d : nat) :
  XE2Legacy.bipartite_plus_bounded_degree G d <-> xe2_bipartite_plus_bounded_degree G d.
Proof.
split=> -[F [sub [bip deg]]]; exists F.
all: (split; [exact: sub | split; [ | exact: deg]]).
all: exact/(bipartite_diso (@xe1_delete_edges_diso G F)).
Qed.

Lemma xe2_diameter_critical_two_compat (G : sgraph) :
  XE2Legacy.diameter_critical_two G <-> xe2_diameter_critical_two G.
Proof.
split=> -[diam2 [ndiam1 crit]]; (split; [exact: diam2 | split; [exact: ndiam1 | ]]).
all: move=> e eE diam; apply: (crit e eE).
- exact/(xe1_diameter_at_most_diso _ (@xe1_delete_edges_diso G [set e])).
- exact/(xe1_diameter_at_most_diso _ (@xe1_delete_edges_diso G [set e])).
Qed.

Lemma erdos_613_statement_compat :
  XE2Legacy.erdos_613_statement <-> erdos_613_statement.
Proof.
split=> st n G n3 count; apply/xe2_bipartite_plus_bounded_degree_compat.
all: exact: st n G n3 count.
Qed.

Lemma erdos_742_statement_compat :
  XE2Legacy.erdos_742_statement <-> erdos_742_statement.
Proof.
split=> st n G Gn crit; apply: (st n G Gn).
all: exact/xe2_diameter_critical_two_compat.
Qed.

(** ** X191 (row BLOCKED; the encoding is preserved, not repaired) *)

Module X191Legacy.

Definition subquadratic_deletion_to_partite
    (F : sgraph) (parts delta_num delta_den : nat) : Prop :=
  exists C : nat,
    forall n : nat,
      #|F| = n ->
      exists X : {set {set F}},
        #|X| ^ delta_den <= C * n ^ (2 * delta_den - delta_num) + C /\
        χ([set: Legacy.x191_delete_edges X]) <= parts.

Definition dense_H_free_clique_blowup_subquadratic_error_statement : Prop :=
  forall H : sgraph,
    exists delta_num delta_den C N : nat,
      [/\ 0 < delta_num, delta_num <= delta_den &
        forall (G F : sgraph) (m t : nat),
          N <= #|G| ->
          x191_dense_H_free_clique_blowup_extremal H G F m t ->
          subquadratic_deletion_to_partite F (χ([set: H]) - 1) delta_num delta_den].

End X191Legacy.

Lemma x191_subquadratic_deletion_to_partite_compat
    (F : sgraph) (parts delta_num delta_den : nat) :
  X191Legacy.subquadratic_deletion_to_partite F parts delta_num delta_den <->
  x191_subquadratic_deletion_to_partite F parts delta_num delta_den.
Proof.
split=> -[C small]; exists C => n Fn; have [X [sizeX chiX]] := small n Fn.
all: exists X; (split; [exact: sizeX | ]).
- by rewrite -(chi_diso (x191_delete_edges_diso X)).
- by rewrite (chi_diso (x191_delete_edges_diso X)).
Qed.

Lemma dense_H_free_clique_blowup_subquadratic_error_statement_compat :
  X191Legacy.dense_H_free_clique_blowup_subquadratic_error_statement <->
  dense_H_free_clique_blowup_subquadratic_error_statement.
Proof.
split=> st H; have [dn [dd [C [N [dn0 dnd deletion]]]]] := st H.
all: exists dn, dd, C, N; split; [exact: dn0 | exact: dnd | move=> G F m t GN ext].
all: apply/x191_subquadratic_deletion_to_partite_compat; exact: deletion G F m t GN ext.
Qed.
