(** A27 complete multipartite graphs (chromatic): U4's and X218's complete multipartite graphs with equal parts --
    the relation, its two constructor proofs and the graph -- with X218's [x218_multibounding] and the two complete rows,
    frozen at the A26 pin 9e3f1ef.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/complete_multipartite_graphs.spec.json.
    - [U4Legacy]: [cmp_rel] on ['I_k * 'I_m] (parts first, adjacent iff the parts differ), [cmp_rel_sym] and
      [cmp_rel_irrefl] with their scripts, [complete_multipartite] and the choice-number row (chi(G) = k, at most m * k
      vertices, BOTH relational choice-number assumptions, then chG <= chK; zero k and m allowed).
    - [X218Legacy]: [x218_multipartite_rel], its two proofs, [x218_complete_multipartite], [x218_multibounding] (whole
      functions c, e : nat -> nat chosen before d >= 1, t >= 1 and G; induced-H exclusion and ordinary-subgraph
      exclusion of K_d(t); chi <= c d * t ^ e d) and the forest row.
    The frozen relations are convertible to GTBase.complete_multipartite_graphs's; the frozen graphs differ from
    [complete_multipartite_graph] only in their opaque proof fields, so the constructions are related by pointwise
    adjacency and the identity isomorphism, and the chain and rows, which read the graphs only through vertices and
    adjacency, convert. *)
From GraphTheory Require Import minor mgraph.
From GTBase Require Import base complete_multipartite_graphs.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U4 U8 X130 X194 X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module U4Legacy.

Definition cmp_rel (k m : nat) : rel ('I_k * 'I_m) :=
  fun x y => x.1 != y.1.

Lemma cmp_rel_sym (k m : nat) : symmetric (@U4Legacy.cmp_rel k m).
Proof. by move=> x y; rewrite /U4Legacy.cmp_rel eq_sym. Qed.

Lemma cmp_rel_irrefl (k m : nat) : irreflexive (@U4Legacy.cmp_rel k m).
Proof. by move=> x; rewrite /U4Legacy.cmp_rel eqxx. Qed.

Definition complete_multipartite (k m : nat) : sgraph :=
  SGraph (@U4Legacy.cmp_rel_sym k m) (@U4Legacy.cmp_rel_irrefl k m).

Definition choice_number_of_k_chromatic_graphs_of_bounded_order_statement : Prop :=
  forall (G : sgraph) (k m chG chK : nat),
    χ([set: G]) = k -> #|G| <= m * k ->
    is_choice_number G chG ->
    is_choice_number (U4Legacy.complete_multipartite k m) chK ->
    chG <= chK.

End U4Legacy.

Module X218Legacy.

Definition x218_multipartite_rel (d t : nat) : rel ('I_d * 'I_t) :=
  fun x y => x.1 != y.1.

Lemma x218_multipartite_sym d t : symmetric (@X218Legacy.x218_multipartite_rel d t).
Proof. by move=> x y; rewrite /X218Legacy.x218_multipartite_rel eq_sym. Qed.

Lemma x218_multipartite_irrefl d t : irreflexive (@X218Legacy.x218_multipartite_rel d t).
Proof. by move=> x; rewrite /X218Legacy.x218_multipartite_rel eqxx. Qed.

Definition x218_complete_multipartite (d t : nat) : sgraph :=
  SGraph (@X218Legacy.x218_multipartite_sym d t) (@X218Legacy.x218_multipartite_irrefl d t).

Definition x218_multibounding (H : sgraph) : Prop :=
  exists c e : nat -> nat,
    forall d : nat, 1 <= d ->
      forall (t : nat) (G : sgraph),
        1 <= t ->
        ~ has_induced H G ->
        ~ has_subgraph G (X218Legacy.x218_complete_multipartite d t) ->
        χ([set: G]) <= c d * t ^ e d.

Definition every_forest_is_multibounding_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    X218Legacy.x218_multibounding H.

End X218Legacy.

(** U4: the relation is the public one by conversion; the constructor proofs and the graphs are related by the identity
    isomorphism, never by an equation between proof fields. *)
Lemma cmp_rel_compat (k m : nat) (x y : 'I_k * 'I_m) :
  @U4Legacy.cmp_rel k m x y = @Chromatic.conjectures.U4.cmp_rel k m x y.
Proof.
by [].
Qed.

Lemma cmp_rel_proofs_compat (k m : nat) :
  SGraph (@U4Legacy.cmp_rel_sym k m) (@U4Legacy.cmp_rel_irrefl k m) ≃
  SGraph (@Chromatic.conjectures.U4.cmp_rel_sym k m) (@Chromatic.conjectures.U4.cmp_rel_irrefl k m).
Proof. by apply: eq_diso => x y. Qed.

Lemma complete_multipartite_compat (k m : nat) :
  @edge_rel (U4Legacy.complete_multipartite k m) =2 @edge_rel (Chromatic.conjectures.U4.complete_multipartite k m).
Proof.
by [].
Qed.

Lemma complete_multipartite_diso (k m : nat) : U4Legacy.complete_multipartite k m ≃ Chromatic.conjectures.U4.complete_multipartite k m.
Proof.
by rewrite /U4Legacy.complete_multipartite /Chromatic.conjectures.U4.complete_multipartite /complete_multipartite_graph; apply: eq_diso => x y.
Qed.

(** The choice-number row: choice numbers read the graph only through its vertices and adjacency. *)
Lemma choice_number_of_k_chromatic_graphs_of_bounded_order_statement_compat :
  U4Legacy.choice_number_of_k_chromatic_graphs_of_bounded_order_statement <->
  Chromatic.conjectures.U4.choice_number_of_k_chromatic_graphs_of_bounded_order_statement.
Proof.
rewrite /U4Legacy.choice_number_of_k_chromatic_graphs_of_bounded_order_statement.
reflexivity.
Qed.

(** X218: the same pattern. *)
Lemma x218_multipartite_rel_compat (d t : nat) (x y : 'I_d * 'I_t) :
  @X218Legacy.x218_multipartite_rel d t x y = @Chromatic.conjectures.X218.x218_multipartite_rel d t x y.
Proof.
by [].
Qed.

Lemma x218_multipartite_proofs_compat (d t : nat) :
  SGraph (@X218Legacy.x218_multipartite_sym d t) (@X218Legacy.x218_multipartite_irrefl d t) ≃
  SGraph (@Chromatic.conjectures.X218.x218_multipartite_sym d t) (@Chromatic.conjectures.X218.x218_multipartite_irrefl d t).
Proof. by apply: eq_diso => x y. Qed.

Lemma x218_complete_multipartite_compat (d t : nat) :
  @edge_rel (X218Legacy.x218_complete_multipartite d t) =2 @edge_rel (Chromatic.conjectures.X218.x218_complete_multipartite d t).
Proof.
by [].
Qed.

Lemma x218_complete_multipartite_diso (d t : nat) :
  X218Legacy.x218_complete_multipartite d t ≃ Chromatic.conjectures.X218.x218_complete_multipartite d t.
Proof.
rewrite /X218Legacy.x218_complete_multipartite /Chromatic.conjectures.X218.x218_complete_multipartite /complete_multipartite_graph.
by apply: eq_diso => x y.
Qed.

(** The multibounding chain and the forest row: subgraph containment and chromatic number read the graphs only through
    their vertices and adjacency; the coefficient functions are untouched. *)
Lemma x218_multibounding_compat (H : sgraph) :
  X218Legacy.x218_multibounding H <-> Chromatic.conjectures.X218.x218_multibounding H.
Proof.
rewrite /X218Legacy.x218_multibounding.
reflexivity.
Qed.

Lemma every_forest_is_multibounding_statement_compat :
  X218Legacy.every_forest_is_multibounding_statement <->
  Chromatic.conjectures.X218.every_forest_is_multibounding_statement.
Proof.
rewrite /X218Legacy.every_forest_is_multibounding_statement.
reflexivity.
Qed.
