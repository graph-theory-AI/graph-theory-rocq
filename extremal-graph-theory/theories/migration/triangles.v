(** A19 triangles (extremal): the frozen X4 Boolean triangle set and XE2 raw pairs, the X4 #621, XE1 #128/#813 and
    XE2 #1009 chains and rows, and the three complete rows.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/triangles.spec.json.
    - [Legacy]: X4's [(#|T| == 3) && cliqueb T] converts to [GTBase.triangles.triangle_set T] (same order, so A17's
      [x4_triangle_set_compat] stays a conversion); XE2's raw two-subsets convert to [raw_pairs T], which ignores
      adjacency.
    - [X4Legacy], [XE1Legacy], [XE2Legacy]: the chains and rows over the frozen helpers; M1's [x4_edge_set] and A7's
      [x4_edge_count] stay live there.  All bounds, attained extrema, quantifier orders, the seven-set condition and
      small-order vacuity are verbatim.
    - [X4Original] (texts at the pre-M1 061154c): both F-restriction chains over M1's frozen edge set, both attained
      extrema and the whole #621 row.  [XE1Original], [XE2Original] (texts at A7's baseline ae0e605): #128 and #1009 over
      A7's frozen edge count; #1009 reuses the frozen packing chain.  M1's and A7's modules are aliased, not imported;
      the bridges reuse their certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base triangles.
From Extremal.conjectures Require Import X4 XE1 XE2.
From Extremal.migration Require simple_edges edge_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** M1's and A7's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module M1E := Extremal.migration.simple_edges.
Module A7 := Extremal.migration.edge_count.

Module Legacy.

Definition x4_triangle_set (G : sgraph) (T : {set G}) : bool :=
  (#|T| == 3) && cliqueb T.

Definition xe2_tri_edges (G : sgraph) (T : {set G}) : {set {set G}} :=
  [set e : {set G} | (e \subset T) && (#|e| == 2)].

End Legacy.

Module X4Legacy.

Definition x4_at_most_one_triangle_edge (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x4_edge_set G /\
  forall T : {set G},
    Legacy.x4_triangle_set T -> #|[set e in F | e \subset T]| <= 1.

Definition x4_hits_every_triangle (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset x4_edge_set G /\
  forall T : {set G},
    Legacy.x4_triangle_set T -> exists e : {set G}, e \in F /\ e \subset T.

Definition x4_alpha1 (G : sgraph) (a : nat) : Prop :=
  (exists F : {set {set G}}, X4Legacy.x4_at_most_one_triangle_edge F /\ #|F| = a) /\
  forall b : nat,
    (exists F : {set {set G}}, X4Legacy.x4_at_most_one_triangle_edge F /\ #|F| = b) ->
    b <= a.

Definition x4_tau1 (G : sgraph) (t : nat) : Prop :=
  (exists F : {set {set G}}, X4Legacy.x4_hits_every_triangle F /\ #|F| = t) /\
  forall b : nat,
    (exists F : {set {set G}}, X4Legacy.x4_hits_every_triangle F /\ #|F| = b) ->
    t <= b.

Definition triangle_alpha_tau_bound_statement : Prop :=
  forall G : sgraph, forall n a t : nat,
    #|G| = n -> X4Legacy.x4_alpha1 G a -> X4Legacy.x4_tau1 G t ->
    4 * (a + t) <= n * n.

End X4Legacy.

Module XE1Legacy.

Definition xe1_every_7_set_has_triangle (G : sgraph) : Prop :=
  forall S : {set G}, #|S| = 7 ->
    exists T : {set G}, T \subset S /\ Legacy.x4_triangle_set T.

Definition xe1_seven_triangle_clique_property (n h : nat) : Prop :=
  forall G : sgraph,
    #|G| = n ->
    XE1Legacy.xe1_every_7_set_has_triangle G ->
    exists K : {set G}, clique K /\ h <= #|K|.

Definition xe1_seven_triangle_clique_guarantee (n h : nat) : Prop :=
  XE1Legacy.xe1_seven_triangle_clique_property n h /\
  forall h' : nat, XE1Legacy.xe1_seven_triangle_clique_property n h' -> h' <= h.

Definition erdos_128_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    (forall S : {set G}, n %/ 2 <= #|S| -> n ^ 2 < 50 * x4_edge_count (induced S)) ->
    exists T : {set G}, Legacy.x4_triangle_set T.

Definition erdos_813_statement : Prop :=
  exists a1 b1 a2 b2 C1 C2 N : nat,
    0 < a1 /\ 0 < b1 /\ 0 < a2 /\ 0 < b2 /\
    0 < C1 /\ 0 < C2 /\ 2 * a2 < b2 /\
    forall (n h : nat),
      N <= n ->
      XE1Legacy.xe1_seven_triangle_clique_guarantee n h ->
      xe1_between_rational_power_bounds n h a1 b1 a2 b2 C1 C2.

End XE1Legacy.

Module XE2Legacy.

Definition xe2_edge_disjoint_triangles (G : sgraph) (ts : seq {set G}) : Prop :=
  uniq ts /\
  (forall T : {set G}, T \in ts -> Legacy.x4_triangle_set T) /\
  forall T U : {set G}, T \in ts -> U \in ts -> T != U ->
    [disjoint Legacy.xe2_tri_edges T & Legacy.xe2_tri_edges U].

Definition erdos_1009_statement : Prop :=
  forall cnum cden : nat, 0 < cnum -> 0 < cden -> exists f : nat,
    forall (n k : nat) (G : sgraph),
      #|G| = n ->
      x4_edge_count G >= (n ^ 2) %/ 4 + k ->
      cden * k < cnum * n ->
      exists ts : seq {set G},
        XE2Legacy.xe2_edge_disjoint_triangles ts /\ k <= size ts + f.

End XE2Legacy.

Module X4Original.

Definition x4_at_most_one_triangle_edge (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset M1E.Legacy.edge_set G /\
  forall T : {set G},
    Legacy.x4_triangle_set T -> #|[set e in F | e \subset T]| <= 1.

Definition x4_hits_every_triangle (G : sgraph) (F : {set {set G}}) : Prop :=
  F \subset M1E.Legacy.edge_set G /\
  forall T : {set G},
    Legacy.x4_triangle_set T -> exists e : {set G}, e \in F /\ e \subset T.

Definition x4_alpha1 (G : sgraph) (a : nat) : Prop :=
  (exists F : {set {set G}}, X4Original.x4_at_most_one_triangle_edge F /\ #|F| = a) /\
  forall b : nat,
    (exists F : {set {set G}}, X4Original.x4_at_most_one_triangle_edge F /\ #|F| = b) ->
    b <= a.

Definition x4_tau1 (G : sgraph) (t : nat) : Prop :=
  (exists F : {set {set G}}, X4Original.x4_hits_every_triangle F /\ #|F| = t) /\
  forall b : nat,
    (exists F : {set {set G}}, X4Original.x4_hits_every_triangle F /\ #|F| = b) ->
    t <= b.

Definition triangle_alpha_tau_bound_statement : Prop :=
  forall G : sgraph, forall n a t : nat,
    #|G| = n -> X4Original.x4_alpha1 G a -> X4Original.x4_tau1 G t ->
    4 * (a + t) <= n * n.

End X4Original.

Module XE1Original.

Definition erdos_128_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    (forall S : {set G}, n %/ 2 <= #|S| -> n ^ 2 < 50 * A7.Legacy.x4_edge_count (induced S)) ->
    exists T : {set G}, Legacy.x4_triangle_set T.

End XE1Original.

Module XE2Original.

Definition erdos_1009_statement : Prop :=
  forall cnum cden : nat, 0 < cnum -> 0 < cden -> exists f : nat,
    forall (n k : nat) (G : sgraph),
      #|G| = n ->
      A7.Legacy.x4_edge_count G >= (n ^ 2) %/ 4 + k ->
      cden * k < cnum * n ->
      exists ts : seq {set G},
        XE2Legacy.xe2_edge_disjoint_triangles ts /\ k <= size ts + f.

End XE2Original.

Lemma x4_triangle_set_compat (G : sgraph) (T : {set G}) :
  Legacy.x4_triangle_set T = x4_triangle_set T.
Proof.
by [].
Qed.

Lemma xe2_tri_edges_compat (G : sgraph) (T : {set G}) :
  Legacy.xe2_tri_edges T = xe2_tri_edges T.
Proof.
by [].
Qed.

Lemma x4_at_most_one_triangle_edge_compat (G : sgraph) (F : {set {set G}}) :
  X4Legacy.x4_at_most_one_triangle_edge F <-> x4_at_most_one_triangle_edge F.
Proof.
exact: iff_refl.
Qed.

Lemma x4_hits_every_triangle_compat (G : sgraph) (F : {set {set G}}) :
  X4Legacy.x4_hits_every_triangle F <-> x4_hits_every_triangle F.
Proof.
exact: iff_refl.
Qed.

Lemma x4_alpha1_compat (G : sgraph) (a : nat) :
  X4Legacy.x4_alpha1 G a <-> x4_alpha1 G a.
Proof.
exact: iff_refl.
Qed.

Lemma x4_tau1_compat (G : sgraph) (t : nat) :
  X4Legacy.x4_tau1 G t <-> x4_tau1 G t.
Proof.
exact: iff_refl.
Qed.

Lemma triangle_alpha_tau_bound_statement_compat :
  X4Legacy.triangle_alpha_tau_bound_statement <-> triangle_alpha_tau_bound_statement.
Proof.
exact: iff_refl.
Qed.

Lemma xe1_every_7_set_has_triangle_compat (G : sgraph) :
  XE1Legacy.xe1_every_7_set_has_triangle G <-> xe1_every_7_set_has_triangle G.
Proof.
exact: iff_refl.
Qed.

Lemma xe1_seven_triangle_clique_property_compat (n h : nat) :
  XE1Legacy.xe1_seven_triangle_clique_property n h <-> xe1_seven_triangle_clique_property n h.
Proof.
exact: iff_refl.
Qed.

Lemma xe1_seven_triangle_clique_guarantee_compat (n h : nat) :
  XE1Legacy.xe1_seven_triangle_clique_guarantee n h <-> xe1_seven_triangle_clique_guarantee n h.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_128_statement_compat :
  XE1Legacy.erdos_128_statement <-> erdos_128_statement.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_813_statement_compat :
  XE1Legacy.erdos_813_statement <-> erdos_813_statement.
Proof.
exact: iff_refl.
Qed.

Lemma xe2_edge_disjoint_triangles_compat (G : sgraph) (ts : seq {set G}) :
  XE2Legacy.xe2_edge_disjoint_triangles ts <-> xe2_edge_disjoint_triangles ts.
Proof.
exact: iff_refl.
Qed.

Lemma erdos_1009_statement_compat :
  XE2Legacy.erdos_1009_statement <-> erdos_1009_statement.
Proof.
exact: iff_refl.
Qed.

(** Complete X4 #621: M1's frozen edge set is rewritten by M1's certificate; the triangle set converts. *)
Lemma x4_at_most_one_triangle_edge_original_compat (G : sgraph) (F : {set {set G}}) :
  X4Original.x4_at_most_one_triangle_edge F <-> x4_at_most_one_triangle_edge F.
Proof.
rewrite /X4Original.x4_at_most_one_triangle_edge /x4_at_most_one_triangle_edge M1E.x4_edge_set_compat.
exact: iff_refl.
Qed.

Lemma x4_hits_every_triangle_original_compat (G : sgraph) (F : {set {set G}}) :
  X4Original.x4_hits_every_triangle F <-> x4_hits_every_triangle F.
Proof.
rewrite /X4Original.x4_hits_every_triangle /x4_hits_every_triangle M1E.x4_edge_set_compat.
exact: iff_refl.
Qed.

Lemma x4_alpha1_original_compat (G : sgraph) (a : nat) :
  X4Original.x4_alpha1 G a <-> x4_alpha1 G a.
Proof.
rewrite /X4Original.x4_alpha1 /x4_alpha1.
setoid_rewrite x4_at_most_one_triangle_edge_original_compat.
reflexivity.
Qed.

Lemma x4_tau1_original_compat (G : sgraph) (t : nat) :
  X4Original.x4_tau1 G t <-> x4_tau1 G t.
Proof.
rewrite /X4Original.x4_tau1 /x4_tau1.
setoid_rewrite x4_hits_every_triangle_original_compat.
reflexivity.
Qed.

Lemma triangle_alpha_tau_bound_statement_original_compat :
  X4Original.triangle_alpha_tau_bound_statement <-> triangle_alpha_tau_bound_statement.
Proof.
rewrite /X4Original.triangle_alpha_tau_bound_statement /triangle_alpha_tau_bound_statement.
setoid_rewrite x4_alpha1_original_compat.
setoid_rewrite x4_tau1_original_compat.
reflexivity.
Qed.

(** Complete XE1 #128 and XE2 #1009: conversions to A7's frozen rows, then A7's certificates. *)
Lemma erdos_128_statement_original_compat :
  XE1Original.erdos_128_statement <-> erdos_128_statement.
Proof.
exact: A7.erdos_128_statement_compat.
Qed.

Lemma erdos_1009_statement_original_compat :
  XE2Original.erdos_1009_statement <-> erdos_1009_statement.
Proof.
exact: A7.erdos_1009_statement_compat.
Qed.
