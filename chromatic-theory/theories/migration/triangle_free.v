(** A15 triangle-free (chromatic): the frozen X132/X187/X192 girth-at-least-four helpers, X192's polynomial-time
    approximation chain, the three rows and the two complete rows.  Baseline, hashes and exact substitutions are
    recorded in meta/migration_reports/triangle_free.spec.json.
    - [Legacy]: each [girth_geq G 4] equals [GTBase.base.triangle_free G] by the unconditional bridge
      [girth_geq4_equiv_triangle_free] (not a conversion).
    - [X132Legacy], [X187Legacy], [X192Legacy]: the rows and X192's chain over the frozen helpers; every other helper
      stays live there.
    - [X187Original], [X192Original]: the complete rows.  X187 composes C5's frozen proper 3-colouring; X192 composes
      C11's frozen excluded-minor class with the frozen chain.  Earlier families' modules are aliased, not imported;
      each bridge reuses the earlier certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Chromatic.conjectures Require Import X132 X187 X192.
From Chromatic.migration Require proper_colouring minor_classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their module names coincide
    with this file's. *)
Module C5 := Chromatic.migration.proper_colouring.
Module C11 := Chromatic.migration.minor_classes.

Module Legacy.

Definition x132_triangle_free (G : sgraph) : Prop := girth_geq G 4.

Definition x187_triangle_free (G : sgraph) : Prop := girth_geq G 4.

Definition x192_triangle_free (G : sgraph) : Prop := girth_geq G 4.

End Legacy.

Module X132Legacy.

Definition dvorak_norin_postle_planar_list_flexibility_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall G : sgraph,
        wagner_planar G ->
        weighted_epsilon_flexible G 5 p q /\
        (Legacy.x132_triangle_free G -> weighted_epsilon_flexible G 4 p q) /\
        (girth_geq G 5 -> weighted_epsilon_flexible G 3 p q)].

End X132Legacy.

Module X187Legacy.

Definition planar_triangle_free_request_graph_fraction_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat),
        wagner_planar G ->
        Legacy.x187_triangle_free G ->
        x187_request_graph ReqEq ReqNeq w ->
        exists col : G -> 'I_3,
          x187_proper_3_colouring col /\
          x187_satisfies_fraction ReqEq ReqNeq w p q col].

End X187Legacy.

Module X192Legacy.

Definition x192_polytime_additive_chromatic_approx
    (C : sgraph -> Prop) (alpha : nat) : Prop :=
  polytime_outputs_graph_on
    (fun G : sgraph => C G /\ Legacy.x192_triangle_free G)
    (x192_additive_chromatic_output alpha).

Definition triangle_free_minor_closed_chromatic_additive_approx_statement : Prop :=
  exists alpha : nat,
    forall C : sgraph -> Prop,
      x192_proper_minor_closed_class C ->
      X192Legacy.x192_polytime_additive_chromatic_approx C alpha.

End X192Legacy.

Module X187Original.

Definition planar_triangle_free_request_graph_fraction_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat),
        wagner_planar G ->
        Legacy.x187_triangle_free G ->
        x187_request_graph ReqEq ReqNeq w ->
        exists col : G -> 'I_3,
          C5.Legacy.x187_proper_3_colouring col /\
          x187_satisfies_fraction ReqEq ReqNeq w p q col].

End X187Original.

Module X192Original.

Definition triangle_free_minor_closed_chromatic_additive_approx_statement : Prop :=
  exists alpha : nat,
    forall C : sgraph -> Prop,
      C11.Legacy.x192_proper_minor_closed_class C ->
      X192Legacy.x192_polytime_additive_chromatic_approx C alpha.

End X192Original.

Lemma x132_triangle_free_compat (G : sgraph) :
  Legacy.x132_triangle_free G <->
  x132_triangle_free G.
Proof.
exact: girth_geq4_equiv_triangle_free.
Qed.

Lemma x187_triangle_free_compat (G : sgraph) :
  Legacy.x187_triangle_free G <->
  x187_triangle_free G.
Proof.
exact: girth_geq4_equiv_triangle_free.
Qed.

Lemma x192_triangle_free_compat (G : sgraph) :
  Legacy.x192_triangle_free G <->
  x192_triangle_free G.
Proof.
exact: girth_geq4_equiv_triangle_free.
Qed.

(** The same program [p] and the same polynomial-cost proof in both directions: only the triangle-free
    conjunct of the domain is converted; both output bounds are untouched. *)
Lemma x192_polytime_additive_chromatic_approx_compat (C : sgraph -> Prop) (alpha : nat) :
  X192Legacy.x192_polytime_additive_chromatic_approx C alpha <->
  x192_polytime_additive_chromatic_approx C alpha.
Proof.
split=> -[p [cost h]]; exists p; split=> // G [CG tf]; apply: h; split=> //;
  exact/x192_triangle_free_compat.
Qed.

Lemma dvorak_norin_postle_planar_list_flexibility_statement_compat :
  X132Legacy.dvorak_norin_postle_planar_list_flexibility_statement <->
  dvorak_norin_postle_planar_list_flexibility_statement.
Proof.
split=> -[p [q [p0 pq h]]]; exists p, q; split=> // G gp;
  have [h5 [h4 h3]] := h G gp; split=> //; split=> // tf; apply: h4;
  exact/x132_triangle_free_compat.
Qed.

Lemma planar_triangle_free_request_graph_fraction_statement_compat :
  X187Legacy.planar_triangle_free_request_graph_fraction_statement <->
  planar_triangle_free_request_graph_fraction_statement.
Proof.
split=> -[p [q [p0 pq h]]]; exists p, q; split=> // G E N w gp tf rq;
  apply: h => //; exact/x187_triangle_free_compat.
Qed.

Lemma triangle_free_minor_closed_chromatic_additive_approx_statement_compat :
  X192Legacy.triangle_free_minor_closed_chromatic_additive_approx_statement <->
  triangle_free_minor_closed_chromatic_additive_approx_statement.
Proof.
rewrite /X192Legacy.triangle_free_minor_closed_chromatic_additive_approx_statement /triangle_free_minor_closed_chromatic_additive_approx_statement.
by setoid_rewrite x192_polytime_additive_chromatic_approx_compat.
Qed.

(** Complete row: C5's frozen proper 3-colouring is kept; only the triangle-free hypothesis is converted,
    then C5's certificate finishes. *)
Lemma planar_triangle_free_request_graph_fraction_statement_original_compat :
  X187Original.planar_triangle_free_request_graph_fraction_statement <->
  planar_triangle_free_request_graph_fraction_statement.
Proof.
apply: (iff_trans _ C5.planar_triangle_free_request_graph_fraction_statement_compat).
split=> -[p [q [p0 pq h]]]; exists p, q; split=> // G E N w gp tf rq;
  apply: h => //; exact/x187_triangle_free_compat.
Qed.

(** Complete row: C11's frozen excluded-minor class is kept; the frozen chain is converted, then C11's
    certificate finishes. *)
Lemma triangle_free_minor_closed_chromatic_additive_approx_statement_original_compat :
  X192Original.triangle_free_minor_closed_chromatic_additive_approx_statement <->
  triangle_free_minor_closed_chromatic_additive_approx_statement.
Proof.
apply: (iff_trans _ C11.triangle_free_minor_closed_chromatic_additive_approx_statement_compat).
rewrite /X192Original.triangle_free_minor_closed_chromatic_additive_approx_statement /C11.Legacy.triangle_free_minor_closed_chromatic_additive_approx_statement.
by setoid_rewrite x192_polytime_additive_chromatic_approx_compat.
Qed.
