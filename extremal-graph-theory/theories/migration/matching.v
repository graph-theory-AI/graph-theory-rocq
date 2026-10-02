(** * Extremal.migration.matching -- frozen matching certificates (C1, 2026-10-02)

    Family: "matching" (meta/library_primitives.json), simple-graph edge-family
    representation; extremal row of X180.  Canonical primitive: upstream
    [GraphTheory.connectivity.matching]; API and grounding in
    packing-theory/theories/foundations/matching.v (not importable from this
    package, so the presentation proof is restated here); record
    meta/LIBRARY_MIGRATION_MATCHING.md (generated, with the source hashes
    of every frozen declaration).

    ** Frozen source

    [Legacy] copies verbatim, from work/coordinator 9e03072, the whole
    affected dependency chain of the X180 statement:
    - X180.v lines 11-13: [x180_matching] (the migrated helper; its edge set
      is [GTBase.finite_graph.fg_edges], an audited FAITHFUL primitive that no
      migration has redirected, so it is used as it is);
    - lines 15-18, 20-25, 27-28: [x180_induced_matching],
      [x180_multitasker_capacity_at_least], [x180_multitasker_capacity_positive]
      (not migrated; frozen because they reach [x180_matching]);
    - lines 60-65: the statement.  [x180_average_degree_logarithmic] reaches
      no migrated name and is used as it is.

    ** Certificates

    [fg_edgesE] relates [fg_edges G] to the upstream edge set [E(G)] (the
    explicit [x != y] guard is implied by simple-graph irreflexivity).
    [x180_matching_compat] is the helper certificate (frozen "empty
    intersection" body <-> live alias = upstream [matching]); the three chain
    certificates follow; [log_degree_multitasker_exists_statement_compat] is
    the row certificate.

    The row is BLOCKED (meta/BLOCKED_RETARGETING_AUDIT.md, 2026-07-17): the
    capacity ratio and the average-degree constants are quantified per graph.
    The certificate proves the frozen and the live statement equivalent, so
    that defect is preserved exactly, neither repaired nor worsened; it is a
    quantifier issue of the statement, not of the matching helper.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.
From Extremal.conjectures Require Import X180.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** X180.v lines 11-13, 15-18, 20-25 and 27-28 at 9e03072, verbatim. *)
Definition x180_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset fg_edges G /\
  forall e f : {set G}, e \in M -> f \in M -> e != f -> e :&: f = set0.

Definition x180_induced_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  x180_matching M /\
  forall e f : {set G}, e \in M -> f \in M -> e != f ->
    forall x y : G, x \in e -> y \in f -> ~~ (x -- y).

Definition x180_multitasker_capacity_at_least (G : sgraph) (a b : nat) : Prop :=
  0 < b /\
  forall M : {set {set G}},
    x180_matching M ->
    exists I : {set {set G}},
      I \subset M /\ x180_induced_matching I /\ b * #|I| >= a * #|M|.

Definition x180_multitasker_capacity_positive (G : sgraph) : Prop :=
  exists a b : nat, 0 < a /\ x180_multitasker_capacity_at_least G a b.

(** X180.v lines 60-65 at 9e03072, verbatim. *)
Definition log_degree_multitasker_exists_statement : Prop :=
  forall n0 : nat,
    exists G : sgraph,
      n0 <= #|G| /\
      x180_average_degree_logarithmic G /\
      x180_multitasker_capacity_positive G.

End Legacy.

(** ** The labelled-graph edge set is the upstream edge set *)

Lemma fg_edgesE (G : sgraph) : fg_edges G = E(G).
Proof.
apply/setP => e; rewrite in_sg_edge_set inE.
apply/existsP/existsP => -[x /existsP[y H]]; exists x; apply/existsP; exists y;
  move: H.
- by case/andP=> /andP[_ xy] /eqP->; rewrite xy eqxx.
- by case/andP=> xy /eqP->; rewrite xy eqxx (sg_edgeNeq xy).
Qed.

(** ** Helper and chain certificates *)

(** The migrated helper: the frozen "empty intersection" body is the upstream
    matching predicate. *)
Lemma x180_matching_compat (G : sgraph) (M : {set {set G}}) :
  Legacy.x180_matching M <-> x180_matching M.
Proof.
rewrite /Legacy.x180_matching /x180_matching fg_edgesE.
split=> [[MS M1]|[MS M1]]; split.
- exact/subsetP.
- move=> e f eM fM x xe xf; apply/eqP; apply/negPn/negP => ef.
  by move/setP/(_ x): (M1 e f eM fM ef); rewrite !inE xe xf.
- exact/subsetP.
- move=> e f eM fM ef; apply/setP => x; rewrite !inE.
  apply/negbTE/negP => /andP[xe xf].
  by move: ef; rewrite (M1 _ _ eM fM x xe xf) eqxx.
Qed.

Lemma x180_induced_matching_compat (G : sgraph) (M : {set {set G}}) :
  Legacy.x180_induced_matching M <-> x180_induced_matching M.
Proof.
rewrite /Legacy.x180_induced_matching /x180_induced_matching.
by split=> -[mM ind]; split=> //; apply/x180_matching_compat.
Qed.

Lemma x180_multitasker_capacity_at_least_compat (G : sgraph) (a b : nat) :
  Legacy.x180_multitasker_capacity_at_least G a b <->
  x180_multitasker_capacity_at_least G a b.
Proof.
rewrite /Legacy.x180_multitasker_capacity_at_least
  /x180_multitasker_capacity_at_least.
split=> -[bpos H]; split=> // M mM.
- have [I [IM [indI ratio]]] := H M ((x180_matching_compat M).2 mM).
  by exists I; split=> //; split=> //; apply/x180_induced_matching_compat.
- have [I [IM [indI ratio]]] := H M ((x180_matching_compat M).1 mM).
  by exists I; split=> //; split=> //; apply/x180_induced_matching_compat.
Qed.

Lemma x180_multitasker_capacity_positive_compat (G : sgraph) :
  Legacy.x180_multitasker_capacity_positive G <->
  x180_multitasker_capacity_positive G.
Proof.
rewrite /Legacy.x180_multitasker_capacity_positive
  /x180_multitasker_capacity_positive.
by split=> -[a [b [apos cap]]]; exists a, b; split=> //;
  apply/x180_multitasker_capacity_at_least_compat.
Qed.

(** ** Statement certificate *)

(** arxiv:1611.02400#01 (BLOCKED, unchanged). *)
Lemma log_degree_multitasker_exists_statement_compat :
  Legacy.log_degree_multitasker_exists_statement <->
  log_degree_multitasker_exists_statement.
Proof.
by split=> H n0; have [G [nG [avg cap]]] := H n0; exists G; split=> //; split=> //;
  apply/x180_multitasker_capacity_positive_compat.
Qed.

Print Assumptions fg_edgesE.
Print Assumptions x180_matching_compat.
Print Assumptions x180_induced_matching_compat.
Print Assumptions x180_multitasker_capacity_at_least_compat.
Print Assumptions x180_multitasker_capacity_positive_compat.
Print Assumptions log_degree_multitasker_exists_statement_compat.
