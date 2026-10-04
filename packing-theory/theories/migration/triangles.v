(** A19 triangles (packing): the frozen U9/X5 clique-first triangles and raw pairs, the U9 row (unrestricted
    transversal S), X5's packing and genuine-edge transversal chains and #167 row, and X5's complete row.  Baseline,
    hashes and exact substitutions are recorded in meta/migration_reports/triangles.spec.json.
    - [Legacy]: U9's and X5's [clique T /\ #|T| = 3] convert to [GTBase.triangles.triangle T]; their raw two-subsets
      convert to [raw_pairs T].
    - [U9Legacy], [X5Legacy]: the rows and X5's chains over the frozen helpers.  U9's S is any set of vertex subsets
      (no edge or two-element restriction); X5's F must consist of graph edges ([x5_edge_set], M1's, stays live here).
    - [X5Original] (texts at the pre-M1 061154c): the transversal over M1's frozen edge set and the whole #167 row,
      reusing the frozen packing chain.  M1's module is aliased, not imported; the bridge reuses M1's certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base triangles.
From Packing.conjectures Require Import U9 X5.
From Packing.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** M1's certificate module, aliased without Import: its module names coincide with this file's. *)
Module M1P := Packing.migration.simple_edges.

Module Legacy.

Definition is_triangle (G : sgraph) (T : {set G}) : Prop :=
  clique T /\ #|T| = 3.

Definition tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

Definition x5_is_triangle (G : sgraph) (T : {set G}) : Prop :=
  clique T /\ #|T| = 3.

Definition x5_tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

End Legacy.

Module U9Legacy.

Definition triangle_packing_vs_triangle_edge_transversal_statement : Prop :=
  forall (k : nat) (G : sgraph),
    (forall P : {set {set G}},
       (forall T : {set G}, T \in P -> Legacy.is_triangle T) ->
       {in P &, forall T1 T2 : {set G},
          T1 != T2 -> [disjoint Legacy.tri_edges T1 & Legacy.tri_edges T2]} ->
       #|P| <= k) ->
    exists S : {set {set G}},
      #|S| <= 2 * k /\
      (forall T : {set G}, Legacy.is_triangle T ->
         exists2 e : {set G}, e \in Legacy.tri_edges T & e \in S).

End U9Legacy.

Module X5Legacy.

Definition x5_edge_disjoint_triangles (G : sgraph) (ts : seq {set G}) : Prop :=
  uniq ts /\
  (forall T : {set G}, T \in ts -> Legacy.x5_is_triangle T) /\
  forall T U : {set G}, T \in ts -> U \in ts -> T != U ->
    [disjoint Legacy.x5_tri_edges T & Legacy.x5_tri_edges U].

Definition x5_triangle_edge_transversal
    (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x5_edge_set G /\
  forall T : {set G}, Legacy.x5_is_triangle T ->
    exists e : {set G}, e \in F /\ e \in Legacy.x5_tri_edges T.

Definition triangle_packing_transversal_statement : Prop :=
  forall (G : sgraph) (k : nat),
    (forall ts : seq {set G}, X5Legacy.x5_edge_disjoint_triangles ts -> size ts <= k) ->
    exists F : {set {set G}},
      X5Legacy.x5_triangle_edge_transversal F /\ #|F| <= 2 * k.

End X5Legacy.

Module X5Original.

Definition x5_triangle_edge_transversal
    (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset M1P.Legacy.edge_set G /\
  forall T : {set G}, Legacy.x5_is_triangle T ->
    exists e : {set G}, e \in F /\ e \in Legacy.x5_tri_edges T.

Definition triangle_packing_transversal_statement : Prop :=
  forall (G : sgraph) (k : nat),
    (forall ts : seq {set G}, X5Legacy.x5_edge_disjoint_triangles ts -> size ts <= k) ->
    exists F : {set {set G}},
      X5Original.x5_triangle_edge_transversal F /\ #|F| <= 2 * k.

End X5Original.

Lemma is_triangle_compat (G : sgraph) (T : {set G}) :
  Legacy.is_triangle T <-> is_triangle T.
Proof.
exact: iff_refl.
Qed.

Lemma tri_edges_compat (G : sgraph) (T : {set G}) :
  Legacy.tri_edges T = tri_edges T.
Proof.
by [].
Qed.

Lemma x5_is_triangle_compat (G : sgraph) (T : {set G}) :
  Legacy.x5_is_triangle T <-> x5_is_triangle T.
Proof.
exact: iff_refl.
Qed.

Lemma x5_tri_edges_compat (G : sgraph) (T : {set G}) :
  Legacy.x5_tri_edges T = x5_tri_edges T.
Proof.
by [].
Qed.

Lemma triangle_packing_vs_triangle_edge_transversal_statement_compat :
  U9Legacy.triangle_packing_vs_triangle_edge_transversal_statement <->
  triangle_packing_vs_triangle_edge_transversal_statement.
Proof.
exact: iff_refl.
Qed.

Lemma x5_edge_disjoint_triangles_compat (G : sgraph) (ts : seq {set G}) :
  X5Legacy.x5_edge_disjoint_triangles ts <-> x5_edge_disjoint_triangles ts.
Proof.
exact: iff_refl.
Qed.

Lemma x5_triangle_edge_transversal_compat (G : sgraph) (F : {set {set G}}) :
  X5Legacy.x5_triangle_edge_transversal F <-> x5_triangle_edge_transversal F.
Proof.
exact: iff_refl.
Qed.

Lemma triangle_packing_transversal_statement_compat :
  X5Legacy.triangle_packing_transversal_statement <-> triangle_packing_transversal_statement.
Proof.
exact: iff_refl.
Qed.

(** Complete X5 #167: M1's frozen edge set is rewritten by M1's certificate; the triangle helpers convert. *)
Lemma x5_triangle_edge_transversal_original_compat (G : sgraph) (F : {set {set G}}) :
  X5Original.x5_triangle_edge_transversal F <-> x5_triangle_edge_transversal F.
Proof.
rewrite /X5Original.x5_triangle_edge_transversal /x5_triangle_edge_transversal M1P.x5_edge_set_compat.
exact: iff_refl.
Qed.

Lemma triangle_packing_transversal_statement_original_compat :
  X5Original.triangle_packing_transversal_statement <-> triangle_packing_transversal_statement.
Proof.
rewrite /X5Original.triangle_packing_transversal_statement /triangle_packing_transversal_statement.
setoid_rewrite x5_triangle_edge_transversal_original_compat.
reflexivity.
Qed.
