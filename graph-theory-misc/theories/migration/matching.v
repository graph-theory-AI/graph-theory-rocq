(** * GTMisc.migration.matching -- frozen matching certificates (C1, 2026-10-02)

    Family: "matching" (meta/library_primitives.json), simple-graph edge-family
    representation; misc row of X14.  Canonical primitive: upstream
    [GraphTheory.connectivity.matching]; API and grounding in
    packing-theory/theories/foundations/matching.v (not importable from this
    package, so the presentation proof is restated here); generated report
    meta/migration_reports/matching.md (from matching.spec.json, with the
    source hash and git blob of every frozen declaration); record
    meta/LIBRARY_MIGRATION_C1.md.

    ** Frozen source

    [Legacy] freezes the migrated helper [x14_matching] verbatim as it stood
    at 9e03072, together with the pre-M1 comprehension body of
    [x14_edge_set] (X14.v at 061154c; M1 froze the same text as
    [GTMisc.migration.simple_edges.Legacy.exists_edge_set] and the live name
    has been the transparent alias [sg_edge_set G] since), so that the frozen
    helper resolves through no alias of any migration.

    [X14Legacy] freezes the statement with its reference to the helper
    replaced by the frozen copy ([x14_matching] -> [Legacy.x14_matching]).
    [x14_subcubic] and [x14_degree_two_count] are untouched live helpers that
    reach no migrated name, so they are used as they are.  The report checks
    the frozen copies against the source text at their commits modulo exactly
    these identifier substitutions.

    ** Certificates

    [x14_matching_compat] is the helper certificate (frozen pairwise-disjoint
    body <-> live alias = upstream [matching]); [x14_edge_set_compat] is the
    chain certificate; [subcubic_matching_lower_bound_statement_compat] is
    the row certificate.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.
From GTMisc.conjectures Require Import X14.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** [x14_edge_set] before M1: X14.v lines 11-13 at 061154c, verbatim
    (the text of GTMisc.migration.simple_edges.Legacy.exists_edge_set). *)
Definition x14_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

(** X14.v lines 14-17 at 9e03072, verbatim; [x14_edge_set] is the frozen
    comprehension above. *)
Definition x14_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x14_edge_set G /\
  forall e f : {set G},
    e \in M -> f \in M -> e != f -> [disjoint e & f].

End Legacy.

(** ** Helper certificates *)

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

(** ** X14: the statement *)

Module X14Legacy.

(** X14.v lines 65-71 at 9e03072 with [x14_matching] -> [Legacy.x14_matching]. *)
Definition subcubic_matching_lower_bound_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    x14_subcubic G ->
    exists M : {set {set G}},
      @Legacy.x14_matching G M /\
      9 * #|M| >= 3 * #|G| + x14_degree_two_count G.

End X14Legacy.

(** studies:std_biedl_demaine_duncan_fleischer_kobourov_subcubic (unchanged). *)
Lemma subcubic_matching_lower_bound_statement_compat :
  X14Legacy.subcubic_matching_lower_bound_statement <->
  subcubic_matching_lower_bound_statement.
Proof.
split=> H G Gpos sub; have [M [mM bound]] := H G Gpos sub; exists M; split=> //.
- exact/x14_matching_compat.
- exact/x14_matching_compat.
Qed.

Print Assumptions x14_edge_set_compat.
Print Assumptions x14_matching_compat.
Print Assumptions subcubic_matching_lower_bound_statement_compat.
