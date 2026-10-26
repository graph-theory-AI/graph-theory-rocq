(** * Minor.migration.path_edges — frozen path-edge sets of U7 and X174 (library migration B8)

    Batch B, family [path-edges] (meta/library_primitives/path-edges.json),
    finite-support class.  [Legacy] freezes U7's helper [path_edges] verbatim as it
    stood at the B8 baseline 048c768: the set of the two-element sets of consecutive
    entries of a vertex sequence, with no adjacency, uniqueness or nonemptiness
    filter.  The live helper now unfolds to [GTBase.walks_paths.seq_edge_set s],
    whose body is that comprehension, so every certificate below is a kernel-checked
    conversion.  [U7Legacy] freezes [immersion] (renamed [u7_immersion], since U7's
    names carry no wave prefix) and U7's colouring row; [X174Legacy] freezes X174's
    negated immersion and its row with BOTH halves (the universal upper bound and the
    existential attainment), keeping the documented natural-subtraction caveat
    [(n - t) + 3] verbatim.  Immersion walks stay walks: no uniqueness is added, only
    the pairwise edge-disjointness of their edge sets.  No earlier migration froze
    either chain, so no historical original is owed.  The grounding lemmas of
    grounding_U7.v keep their statements.  Source hashes, substitutions and the
    per-row theorem names are in meta/migration_reports/path_edges.md.
    - X174 source repair (2026-10-26, coordination/PROGRAMME.md A2; record meta/STATEMENT_IMPROVEMENTS.md): the frozen
      [X174Legacy] row is false ([X174Legacy_row_false]: at t = 2, n = 0 its bound [(n - t) + 3] asks the empty graph
      for three cliques) and the live row uses [x174_extremal_bound_exact].  Its certificate is a ONE-WAY source-repair
      certificate [frozen -> live] (direction "weaken"), not a migration equivalence; the other certificates keep their
      exact iffs. *)

From GTBase Require Import base.
From GraphTheory Require Import minor connectivity coloring.
From Minor.conjectures Require Import U7 X174.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition path_edges (G : sgraph) (s : seq G) : {set {set G}} :=
  [set e in [seq [set p.1; p.2] | p <- zip s (behead s)]].

End Legacy.

Module U7Legacy.

Definition u7_immersion (G H : sgraph) : Prop :=
  exists (f : H -> G) (P : H -> H -> seq G),
    injective f /\
    (forall u v : H, u -- v ->
        path sedge (f u) (P u v) /\ last (f u) (P u v) = f v) /\
    (forall u1 v1 u2 v2 : H, u1 -- v1 -> u2 -- v2 ->
        [set u1; v1] != [set u2; v2] ->
        [disjoint Legacy.path_edges (f u1 :: P u1 v1)
                & Legacy.path_edges (f u2 :: P u2 v2)]).

Definition coloring_and_immersion_statement : Prop :=
  forall (t : nat) (G : sgraph),
    0 < t -> t <= χ([set: G]) -> u7_immersion G 'K_t.

End U7Legacy.

Module X174Legacy.

Definition no_Kt_immersion (G : sgraph) (t : nat) : Prop :=
  ~ U7Legacy.u7_immersion G 'K_t.

Definition kt_immersion_clique_count_extremal_statement : Prop :=
  forall t n : nat,
    2 <= t ->
    t - 2 <= n ->
    (forall G : sgraph,
        #|G| = n ->
        no_Kt_immersion G t ->
        x174_clique_count G <= x174_extremal_bound t n) /\
    (exists G : sgraph,
        #|G| = n /\
        no_Kt_immersion G t /\
        x174_clique_count G = x174_extremal_bound t n).

End X174Legacy.

(** ** Certificates *)

Lemma path_edges_compat (G : sgraph) (s : seq G) : Legacy.path_edges s = path_edges s.
Proof. by []. Qed.

Lemma immersion_compat (G H : sgraph) : U7Legacy.u7_immersion G H <-> immersion G H.
Proof. exact: iff_refl. Qed.

Lemma coloring_and_immersion_statement_compat :
  U7Legacy.coloring_and_immersion_statement <-> coloring_and_immersion_statement.
Proof. exact: iff_refl. Qed.

Lemma x174_no_Kt_immersion_compat (G : sgraph) (t : nat) :
  X174Legacy.no_Kt_immersion G t <-> x174_no_Kt_immersion G t.
Proof. exact: iff_refl. Qed.

(** X174 SOURCE REPAIR (2026-10-26, PROGRAMME A2; record meta/STATEMENT_IMPROVEMENTS.md), not a migration
    equivalence.  [x174_extremal_bound] computes (n - t) + 3 in the naturals, so at n = t - 2 the frozen row asks for
    a graph on t - 2 vertices with 2^(t-2) * 3 cliques; at t = 2, n = 0 the only graph, the empty one, has one clique
    (the empty set), so the frozen row is false.  The live row uses [x174_extremal_bound_exact] (n + 3 - t); its
    certificate is ONE-WAY, [frozen -> live] (direction "weaken"), through that falsity. *)
Lemma x174_empty_clique_count (G : sgraph) : #|G| = 0 -> x174_clique_count G = 1.
Proof.
move=> h0; change (#|cliques [set: G]| = 1).
have e (K : {set G}) : K = set0.
  by apply/eqP; rewrite -cards_eq0 -leqn0 -h0; exact: max_card.
rewrite (_ : cliques _ = [set set0]) ?cards1 //.
apply/setP => K; rewrite !inE (e K) eqxx sub0set /=.
by apply/cliqueP => x; rewrite inE.
Qed.

Lemma X174Legacy_row_false : ~ X174Legacy.kt_immersion_clique_count_extremal_statement.
Proof.
move=> h; have [_ [G [hG [_ hc]]]] := h 2 0 (leqnn 2) (leq0n _).
by move: hc; rewrite x174_empty_clique_count.
Qed.

Lemma kt_immersion_clique_count_extremal_statement_compat :
  X174Legacy.kt_immersion_clique_count_extremal_statement ->
  kt_immersion_clique_count_extremal_statement.
Proof. by move/X174Legacy_row_false. Qed.

Print Assumptions path_edges_compat.
Print Assumptions immersion_compat.
Print Assumptions coloring_and_immersion_statement_compat.
Print Assumptions x174_no_Kt_immersion_compat.
Print Assumptions kt_immersion_clique_count_extremal_statement_compat.
Print Assumptions X174Legacy_row_false.
