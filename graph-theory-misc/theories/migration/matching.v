(** * GTMisc.migration.matching -- frozen matching certificates (C1, 2026-10-02)

    Family: "matching" (meta/library_primitives.json), simple-graph edge-family
    representation; misc row of X14.  Canonical primitive: upstream
    [GraphTheory.connectivity.matching]; API and grounding in
    packing-theory/theories/foundations/matching.v (not importable from this
    package, so the presentation proof is restated here); record
    meta/LIBRARY_MIGRATION_MATCHING.md (generated, with the source hashes
    of every frozen declaration).

    ** Frozen source

    [Legacy] copies verbatim, from work/coordinator 9e03072, the affected
    dependency chain of the X14 statement, so that the frozen statement
    resolves through no live helper that any migration (M1 edge sets, C1
    matchings) has redirected:
    - [x14_edge_set] with its pre-M1 comprehension body (the body frozen as
      [GTMisc.migration.simple_edges.Legacy.exists_edge_set] on 2026-07-23;
      the live name has been the transparent alias [sg_edge_set G] since M1);
    - X14.v lines 14-17: [x14_matching] (the migrated helper);
    - X14.v lines 65-71: the statement.  [x14_subcubic] and
      [x14_degree_two_count] are untouched live helpers that reach no
      migrated name, so they are used as they are.

    ** Certificates

    [x14_matching_compat] is the helper certificate (frozen pairwise-disjoint
    body <-> live alias = upstream [matching]);
    [subcubic_matching_lower_bound_statement_compat] is the row certificate.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.
From GTMisc.conjectures Require Import X14.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** [x14_edge_set] before M1 (GTMisc.migration.simple_edges.Legacy.exists_edge_set). *)
Definition x14_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

(** X14.v lines 14-17 at 9e03072, verbatim. *)
Definition x14_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x14_edge_set G /\
  forall e f : {set G},
    e \in M -> f \in M -> e != f -> [disjoint e & f].

(** X14.v lines 65-71 at 9e03072, verbatim. *)
Definition subcubic_matching_lower_bound_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    x14_subcubic G ->
    exists M : {set {set G}},
      @x14_matching G M /\
      9 * #|M| >= 3 * #|G| + x14_degree_two_count G.

End Legacy.

(** ** Helper certificate *)

(** The pre-M1 edge set is the live alias (restates
    GTMisc.migration.simple_edges.x14_edge_set_compat so that this certificate
    is self-contained). *)
Lemma x14_edge_set_compat (G : sgraph) :
  Legacy.x14_edge_set G = x14_edge_set G.
Proof. by rewrite /x14_edge_set sg_edge_setE. Qed.

(** The migrated helper: the frozen "distinct members are disjoint" body is
    the upstream matching predicate (the proof of the former bridge
    vocabulary_misc.x14_matching_equiv_matching, moved here). *)
Lemma x14_matching_compat (G : sgraph) (M : {set {set G}}) :
  Legacy.x14_matching M <-> x14_matching M.
Proof.
rewrite /Legacy.x14_matching x14_edge_set_compat /x14_matching.
split=> [[MS M1]|[MS M1]]; split.
- by move=> e eM; exact: (subsetP MS).
- move=> e f eM fM x xe xf; apply/eqP; apply/negPn/negP => ef.
  by move: (M1 e f eM fM ef) => /disjointFr /(_ xe); rewrite xf.
- by apply/subsetP => e eM; exact: MS.
- move=> e f eM fM ef; rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE.
  apply/negbTE/negP => /andP[xe xf].
  by move: ef; rewrite (M1 _ _ eM fM x xe xf) eqxx.
Qed.

(** ** Statement certificate *)

(** studies:std_biedl_demaine_duncan_fleischer_kobourov_subcubic (unchanged). *)
Lemma subcubic_matching_lower_bound_statement_compat :
  Legacy.subcubic_matching_lower_bound_statement <->
  subcubic_matching_lower_bound_statement.
Proof.
split=> H G Gpos sub; have [M [mM bound]] := H G Gpos sub; exists M; split=> //.
- exact/x14_matching_compat.
- exact/x14_matching_compat.
Qed.

Print Assumptions x14_edge_set_compat.
Print Assumptions x14_matching_compat.
Print Assumptions subcubic_matching_lower_bound_statement_compat.
