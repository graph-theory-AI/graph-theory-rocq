(** * Digraph.migration.directed_neighbourhood — frozen directed neighbourhoods and in-degrees, their
    rows, chains and Originals (library migration, family directed-neighbourhood, option C)

    Family [directed-neighbourhood] (meta/library_primitives/directed-neighbourhood.json; contract
    master-directed-neighbourhood-contract.md 86b00148 and addendum ed04e65a).  [Legacy] freezes,
    verbatim as they stood at the family baseline (the A28 main 761e776c), the six endpoints this
    stage of the family turns into transparent aliases:
    - classic_core's [Nout], [Nin], [indeg] (over [Nin]), [Nout2] (over [Nout]) and [diregular]
      (over [indeg] and core [outdeg]), now aliases of the public [Digraph.foundations.neighbourhoods]
      [Nout]/[Nin]/[Nout2], of B16's [Digraph.foundations.degree_balance.indeg] and of the new
      [degree_balance.diregular];
    - colouring_variants' file-local [indeg] (frozen as [cv_indeg]), now B16's [indeg].
    STAGED (master-directed-neighbourhood-scope-decision.md 6d6d2b8d, option C): core/tournament's
    [N_out]/[N_in], the rows that reach them only (X2's two tournament out-neighbourhood rows and
    X93's row) and the X93 chain [x93_t_local_tournament] belong to a later stage of this family: the
    migration tools admit no public source under core/.  They are untouched here.
    Every frozen reference to a frozen neighbour is qualified ([Legacy.Nin], [@Legacy.indeg D]), so
    each body resolves exactly as its source did; all unfold to the same comprehensions as the live
    aliases, so the endpoint certificates are conversions.  [diregular_ascription] certifies the one
    textual difference of the public body, the binder ascription [[forall v : D, ...]].

    The per-row modules freeze the eleven live rows of this stage with their own chains only
    (classic_core: Seymour, long dicycle, Jackson; P9: the Hamilton alias of the Jackson row, the
    antidirected trees with the chain [antidirected_tree], the arc-disjoint cycles, the even-tournament
    path decomposition (its [classic_core.indeg] is qualified in the source); X19; X2: the
    Mader delta-zero row with its chains [min_semidegree_at_least], [mader_delta_zero_bound] and
    [least_mader_delta_zero], the semidegree row with [min_semidegree_half] and [antidirected_path];
    X17 with [x17_min_semidegree_strict_half]).  Every row guard is kept in its order, including the
    redundant ones.  Helpers of earlier families that the rows reach ([contains_subdivision], migrated
    by path-vertices / internal-vertices) stay live, as their keys record.

    LEXICAL-ONLY enrollment (decision X-a): X107's [x107_total_degree_at_most] binds a LOCAL
    [let indeg v := ...], which shadows every imported [indeg]; the migration tool's lexical discovery
    resolves the name to classic_core's [indeg] anyway, while the kernel closure (E1) shows no
    dependency on this family.  [X107Legacy] freezes that chain and its row verbatim (no substitution
    inside the let) so that the tool's conservative coverage holds; both certificates are [iff_refl]
    of unchanged text.

    Complete Originals: B16's five rows froze B16's own helpers over the then-live
    [classic_core.indeg] / [colouring_variants.indeg] (snapshots keyed in this family's spec);
    [DegreeBalanceOriginal] and the [*Original] row modules recompose them over the raw in-degrees
    frozen here, the X221 row also over poset-unavoidability's frozen [contains_subdigraph].  B1/B2's
    Mader chain in path_vertices.v calls the live [min_semidegree_at_least]; [X2Original] recomposes
    the Mader delta-zero row over B1's raw [contains_subdivision], this family's frozen
    [min_semidegree_at_least] and the raw in-degree.  Hashes and substitutions:
    meta/migration_reports/directed_neighbourhood.md.

    SOURCE REPAIR (2026-10-25, direction weaken): the live [majority_3col_eulerian_statement] gained a
    [loopless D] guard.  [ColouringVariantsOriginal] stays verbatim, and its certificate below is a
    ONE-WAY SOURCE-REPAIR certificate (original -> live), not a migration equivalence.  Its spec entry
    carries the identical repair as the degree_balance statement entry, which holds the text,
    doc-block, row and leg checks (meta/migration_report.py: an original-statement repair may rest on
    its statement in exactly one other family spec).

    SOURCE REPAIRS (2026-10-26, direction weaken): the live
    [arc_disjoint_directed_cycles_in_regular_directed_gra_statement] gained a [0 < #|D|] guard (the
    empty digraph is k-diregular for every k and has no cycle), and the live
    [antidirected_trees_in_digraphs_statement] gained a [loopless D] guard ([nb_arcs] counts loops).
    [P9Legacy] stays verbatim, and these two rows' certificates below are ONE-WAY SOURCE-REPAIR
    certificates (frozen -> live), not migration equivalences; their statement entries in this spec
    carry the repairs.

    Every other certificate keeps its exact iff. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order strong classic_core dichromatic omegabar.
From Digraph Require Import heroes heroes_dichotomy unvd twinwidth twinwidth_ordered.
From Digraph Require Import automorphism domination chi_bounded.
From Digraph Require Import two_extremal two_extremal_hajos two_extremal_glue generalised_wheel.
From Digraph Require Import glue_eul_subtype sad.
From GTBase Require Import asymptotics walks_paths.
From Digraph.conjectures Require Import X221 colouring_variants P9 X2 X17 X19 X107.
From Digraph.foundations Require neighbourhoods degree_balance.
From Digraph.migration Require path_vertices tournament_unavoidability.
From Digraph.migration Require degree_balance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Section NeighbourhoodsLegacy.
Variable D : diGraphType.
Implicit Types (v w : D).

Definition Nout v : {set D} := [set w | v --> w].
Definition Nin  v : {set D} := [set u | u --> v].

End NeighbourhoodsLegacy.

Section InDegreeLegacy.
Variable D : diGraphType.
Implicit Types (v w : D).

(** In-degree (companion of [outdeg], which is [#|Nout v|] by definition). *)
Definition indeg v : nat := #|Legacy.Nin v|.

(** Second out-neighbourhood: vertices at directed distance exactly two from [v]
    (an out-neighbour of an out-neighbour, distinct from [v] and not itself an
    out-neighbour). *)
Definition Nout2 v : {set D} :=
  [set w | [&& w != v, w \notin Legacy.Nout v & [exists u, (u \in Legacy.Nout v) && (u --> w)]]].

End InDegreeLegacy.

Section DiregularLegacy.
Variable D : diGraphType.

(** Diregular of degree [d]: every vertex has in-degree and out-degree exactly [d]. *)
Definition diregular (d : nat) : bool := [forall v, (outdeg v == d) && (@Legacy.indeg D v == d)].

End DiregularLegacy.

Definition cv_indeg (D : diGraphType) (v : D) : nat := #|[set u | u --> v]|.

End Legacy.

Module ClassicCoreLegacy.

Definition seymour_second_neighbourhood_statement : Prop :=
  forall D : orientedDigraph,
    (0 < #|D|)%N -> exists v : D, (outdeg v <= #|Legacy.Nout2 v|)%N.

Definition long_dicycle_diregular_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    (0 < #|D|)%N -> (0 < d)%N -> strongb D ->
    (forall v : D, (d <= Legacy.indeg v)%N) -> (forall v : D, (d <= outdeg v)%N) ->
    exists c : seq D, dicycle c /\ (2 * d + 1 <= size c)%N.

Definition jackson_hamilton_small_diregular_statement : Prop :=
  forall (D : orientedDigraph) (d : nat),
    (0 < #|D|)%N -> 2 < d -> Legacy.diregular D d -> (#|D| <= 4 * d + 1)%N ->
    exists c : seq D, dicycle c /\ size c = #|D|.

End ClassicCoreLegacy.

Module P9Legacy.

Definition antidirected_tree (T : orientedDigraph) : bool :=
  (* [classic_core.indeg] qualified: [indeg] is declared in both classic_core and
     colouring_variants (base-reuse duplicate, to consolidate at G3). *)
  tree_digraph T && [forall v : T, (outdeg v == 0) || (Legacy.indeg v == 0)].

Definition hamilton_cycle_in_small_d_diregular_graphs_statement : Prop :=
  ClassicCoreLegacy.jackson_hamilton_small_diregular_statement.

Definition antidirected_trees_in_digraphs_statement : Prop :=
  forall (D : diGraphType) (k : nat), 2 <= k ->
    (k - 2) * #|D| < nb_arcs D ->
    forall T : orientedDigraph, P9Legacy.antidirected_tree T -> #|T| = k -> contains_subdig D T.

Definition arc_disjoint_directed_cycles_in_regular_directed_gra_statement : Prop :=
  forall (D : diGraphType) (k : nat), Legacy.diregular D k ->
    exists P : seq (seq D),
      [/\ all (@dicycle D) P,
          pairwise (fun a b => [disjoint cyc_arcs a & cyc_arcs b]) P &
          'C(k.+1, 2) <= size P].

Definition decomposing_an_even_tournament_in_directed_paths_statement : Prop :=
  forall T : tournament, ~~ odd #|T| ->
    exists Q : seq (T * seq T),
      [/\ all (fun p => dipath p.1 p.2) Q,
          [forall e : T * T, (\sum_(p <- Q) (e \in dipath_arcs p.1 p.2)) == (e.1 --> e.2)] &
          size Q = \sum_(v : T) (outdeg v - Legacy.indeg v)].

End P9Legacy.

Module X19Legacy.

Definition behzad_chartrand_wall_girth_regular_digraph_statement : Prop :=
  forall (r g : nat) (D : diGraphType),
    0 < r -> 0 < g -> 0 < #|D| ->
    x19_loopless D ->
    Legacy.diregular D r ->
    x19_directed_girth_at_least D g ->
    (r * (g - 1) + 1 <= #|D|)%N.

End X19Legacy.

Module X2Legacy.

Definition min_semidegree_at_least (D : diGraphType) (m : nat) : Prop :=
  forall v : D, (m <= outdeg v)%N /\ (m <= Legacy.indeg v)%N.

Definition mader_delta_zero_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    X2Legacy.min_semidegree_at_least D m -> contains_subdivision F D.

Definition least_mader_delta_zero (F : diGraphType) (m : nat) : Prop :=
  X2Legacy.mader_delta_zero_bound F m /\
  forall c : nat, X2Legacy.mader_delta_zero_bound F c -> (m <= c)%N.

Definition mader_delta0_transitive_tournament_statement : Prop :=
  forall k : nat, exists m : nat, X2Legacy.least_mader_delta_zero (TT k) m.

Definition antidirected_path (P : diGraphType) : Prop :=
  forall v : P, Legacy.indeg v = 0 \/ outdeg v = 0.

Definition min_semidegree_half (D : diGraphType) (k : nat) : Prop :=
  forall v : D, (k <= 2 * outdeg v)%N /\ (k <= 2 * Legacy.indeg v)%N.

Definition semidegree_oriented_paths_statement : Prop :=
  forall (k : nat) (G : orientedDigraph),
    X2Legacy.min_semidegree_half G k ->
    forall P : orientedDigraph,
      oriented_path P k -> ~ X2Legacy.antidirected_path P -> subdigraph_embed P G.

End X2Legacy.

Module X17Legacy.

Definition x17_min_semidegree_strict_half (D : diGraphType) (k : nat) : Prop :=
  forall v : D, (k < 2 * outdeg v)%N /\ (k < 2 * Legacy.indeg v)%N.

Definition stein_oriented_paths_strict_semidegree_statement : Prop :=
  forall (k : nat) (G : orientedDigraph),
    0 < k ->
    (0 < #|G|)%N ->
    X17Legacy.x17_min_semidegree_strict_half G k ->
    forall P : orientedDigraph,
      oriented_path P k -> subdigraph_embed P G.

End X17Legacy.

Module X107Legacy.

(** Lexical-only: the local [let indeg] below shadows every imported [indeg]. *)
Definition x107_total_degree_at_most (D : diGraphType) (Delta : nat) : Prop :=
  let indeg v := #|[set u : D | u --> v]| in
  forall v : D, outdeg v + indeg v <= Delta.

Definition bounded_degree_acyclic_oriented_ramsey_linear_statement : Prop :=
  forall Delta : nat,
    exists C : nat,
      forall (n : nat) (H : diGraphType),
        #|H| = n ->
        acyclicb H ->
        X107Legacy.x107_total_degree_at_most H Delta ->
        x107_oriented_ramsey_at_most H (C * n).

End X107Legacy.

(** ** Complete Originals of B16's rows, over the raw in-degrees frozen here *)

Module DegreeBalanceOriginal.

Definition x221_eulerian (D : diGraphType) : Prop :=
  forall v : D, outdeg v = Legacy.indeg v.

Definition cv_eulerian (D : diGraphType) : bool :=
  [forall v : D, Legacy.cv_indeg v == outdeg v].

Definition Eulerian (D : diGraphType) : Prop :=
  forall v : D, Legacy.indeg v = outdeg v.

End DegreeBalanceOriginal.

Module X221Original.

Definition eulerian_avoidable (F : diGraphType) : Prop :=
  exists d : nat -> nat,
    forall (k : nat) (D : diGraphType),
      DegreeBalanceOriginal.x221_eulerian D -> (forall v : D, (d k <= outdeg v)%N) ->
      exists f : D -> {set D},
        (forall v : outsel f, (k <= outdeg v)%N)
        /\ ~ Digraph.migration.tournament_unavoidability.Legacy.contains_subdigraph F (outsel f).

Definition orientation_C4_eulerian_avoidable_statement : Prop :=
  forall b : 'Z_4 -> bool, X221Original.eulerian_avoidable (x221_c4or b).

End X221Original.

Module ColouringVariantsOriginal.

Definition majority_3col_eulerian_statement : Prop :=
  forall D : diGraphType, DegreeBalanceOriginal.cv_eulerian D ->
    exists col : D -> 'I_3, majority_col col.

End ColouringVariantsOriginal.

Module TwoExtremalOriginal.

Definition H6_no_full_cover : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (0 < #|D|)%N -> strongb D -> DegreeBalanceOriginal.Eulerian D ->
    arc_conn D = 2 ->
    three_connected_sg (underlyingG llD) ->
    ~ connected [set: digonG llD] ->
    dicolorableb D 2.

End TwoExtremalOriginal.

Module TwoExtremalGlueOriginal.

Definition realises_W (t : ptree) (D : diGraphType) : Prop :=
  exists llD : loopless D,
    [/\ (forall u v : D, ~~ ((u --> v) && (v --> u))),
        DegreeBalanceOriginal.Eulerian D
      & is_forest [set: digonG llD]].

Definition conj_9_2_glued : Prop := conj_9_2_concrete TwoExtremalGlueOriginal.realises_W.

End TwoExtremalGlueOriginal.

Module GlueEulSubtypeOriginal.

Definition realises_E (t : ptree) (D : diGraphType) : Prop :=
  exists llD : loopless D,
    [/\ (forall u v : D, ~~ ((u --> v) && (v --> u))),
        DegreeBalanceOriginal.Eulerian D
      & is_forest [set: digonG llD]].

Definition conj_9_2_glued_e : Prop := conj_9_2_concrete GlueEulSubtypeOriginal.realises_E.

End GlueEulSubtypeOriginal.

(** ** The complete Original of B1/B2's Mader delta-zero row *)

Module X2Original.

Definition mader_delta_zero_bound (F : diGraphType) (m : nat) : Prop :=
  forall D : diGraphType, (0 < #|D|)%N ->
    X2Legacy.min_semidegree_at_least D m ->
    Digraph.migration.path_vertices.X2Legacy.contains_subdivision F D.

Definition least_mader_delta_zero (F : diGraphType) (m : nat) : Prop :=
  X2Original.mader_delta_zero_bound F m /\
  forall c : nat, X2Original.mader_delta_zero_bound F c -> (m <= c)%N.

Definition mader_delta0_transitive_tournament_statement : Prop :=
  forall k : nat, exists m : nat, X2Original.least_mader_delta_zero (TT k) m.

End X2Original.

(** ** Endpoint certificates (conversions) *)

Lemma Nout_compat (D : diGraphType) (v : D) :
  Legacy.Nout v = Digraph.conjectures.classic_core.Nout v.
Proof. by []. Qed.

Lemma Nin_compat (D : diGraphType) (v : D) :
  Legacy.Nin v = Digraph.conjectures.classic_core.Nin v.
Proof. by []. Qed.

Lemma indeg_compat (D : diGraphType) (v : D) :
  Legacy.indeg v = Digraph.conjectures.classic_core.indeg v.
Proof. by []. Qed.

Lemma Nout2_compat (D : diGraphType) (v : D) :
  Legacy.Nout2 v = Digraph.conjectures.classic_core.Nout2 v.
Proof. by []. Qed.

Lemma diregular_compat (D : diGraphType) (d : nat) :
  Legacy.diregular D d = Digraph.conjectures.classic_core.diregular D d.
Proof. by []. Qed.

(** The public body ascribes its binder ([[forall v : D, ...]]): the same Boolean as the frozen one. *)
Lemma diregular_ascription (D : diGraphType) (d : nat) :
  Digraph.foundations.degree_balance.diregular D d = Legacy.diregular D d.
Proof. by []. Qed.

Lemma cv_indeg_compat (D : diGraphType) (v : D) :
  Legacy.cv_indeg v = Digraph.conjectures.colouring_variants.indeg v.
Proof. by []. Qed.

(** ** Chain certificates *)

Lemma antidirected_tree_compat (T : orientedDigraph) :
  P9Legacy.antidirected_tree T = Digraph.conjectures.P9.antidirected_tree T.
Proof. by []. Qed.

Lemma min_semidegree_at_least_compat (D : diGraphType) (m : nat) :
  X2Legacy.min_semidegree_at_least D m <-> Digraph.conjectures.X2.min_semidegree_at_least D m.
Proof. exact: iff_refl. Qed.

Lemma mader_delta_zero_bound_compat (F : diGraphType) (m : nat) :
  X2Legacy.mader_delta_zero_bound F m <-> Digraph.conjectures.X2.mader_delta_zero_bound F m.
Proof. exact: iff_refl. Qed.

Lemma least_mader_delta_zero_compat (F : diGraphType) (m : nat) :
  X2Legacy.least_mader_delta_zero F m <-> Digraph.conjectures.X2.least_mader_delta_zero F m.
Proof. exact: iff_refl. Qed.

Lemma antidirected_path_compat (P : diGraphType) :
  X2Legacy.antidirected_path P <-> Digraph.conjectures.X2.antidirected_path P.
Proof. exact: iff_refl. Qed.

Lemma min_semidegree_half_compat (D : diGraphType) (k : nat) :
  X2Legacy.min_semidegree_half D k <-> Digraph.conjectures.X2.min_semidegree_half D k.
Proof. exact: iff_refl. Qed.

Lemma x17_min_semidegree_strict_half_compat (D : diGraphType) (k : nat) :
  X17Legacy.x17_min_semidegree_strict_half D k <-> Digraph.conjectures.X17.x17_min_semidegree_strict_half D k.
Proof. exact: iff_refl. Qed.

(** Lexical-only (decision X-a): unchanged text, no dependency on this family. *)
Lemma x107_total_degree_at_most_compat (D : diGraphType) (Delta : nat) :
  X107Legacy.x107_total_degree_at_most D Delta <-> Digraph.conjectures.X107.x107_total_degree_at_most D Delta.
Proof. exact: iff_refl. Qed.

(** ** Row certificates (every row unchanged; the frozen rows are the live ones up to conversion) *)

Lemma seymour_second_neighbourhood_statement_compat :
  ClassicCoreLegacy.seymour_second_neighbourhood_statement
  <-> Digraph.conjectures.classic_core.seymour_second_neighbourhood_statement.
Proof. exact: iff_refl. Qed.

Lemma long_dicycle_diregular_statement_compat :
  ClassicCoreLegacy.long_dicycle_diregular_statement
  <-> Digraph.conjectures.classic_core.long_dicycle_diregular_statement.
Proof. exact: iff_refl. Qed.

Lemma jackson_hamilton_small_diregular_statement_compat :
  ClassicCoreLegacy.jackson_hamilton_small_diregular_statement
  <-> Digraph.conjectures.classic_core.jackson_hamilton_small_diregular_statement.
Proof. exact: iff_refl. Qed.

Lemma hamilton_cycle_in_small_d_diregular_graphs_statement_compat :
  P9Legacy.hamilton_cycle_in_small_d_diregular_graphs_statement
  <-> Digraph.conjectures.P9.hamilton_cycle_in_small_d_diregular_graphs_statement.
Proof. exact: iff_refl. Qed.

(** One-way source-repair certificate, not a migration equivalence (2026-10-26, direction weaken):
    the live row gained the [loopless D] guard, so the frozen row implies it. *)
Lemma antidirected_trees_in_digraphs_statement_compat :
  P9Legacy.antidirected_trees_in_digraphs_statement
  -> Digraph.conjectures.P9.antidirected_trees_in_digraphs_statement.
Proof. by move=> h D k hk _; exact: h. Qed.

(** One-way source-repair certificate, not a migration equivalence (2026-10-26, direction weaken):
    the live row gained the [0 < #|D|] guard, so the frozen row implies it. *)
Lemma arc_disjoint_directed_cycles_in_regular_directed_gra_statement_compat :
  P9Legacy.arc_disjoint_directed_cycles_in_regular_directed_gra_statement
  -> Digraph.conjectures.P9.arc_disjoint_directed_cycles_in_regular_directed_gra_statement.
Proof. by move=> h D k _; exact: h. Qed.

Lemma decomposing_an_even_tournament_in_directed_paths_statement_compat :
  P9Legacy.decomposing_an_even_tournament_in_directed_paths_statement
  <-> Digraph.conjectures.P9.decomposing_an_even_tournament_in_directed_paths_statement.
Proof. exact: iff_refl. Qed.

Lemma behzad_chartrand_wall_girth_regular_digraph_statement_compat :
  X19Legacy.behzad_chartrand_wall_girth_regular_digraph_statement
  <-> Digraph.conjectures.X19.behzad_chartrand_wall_girth_regular_digraph_statement.
Proof. exact: iff_refl. Qed.

Lemma mader_delta0_transitive_tournament_statement_compat :
  X2Legacy.mader_delta0_transitive_tournament_statement
  <-> Digraph.conjectures.X2.mader_delta0_transitive_tournament_statement.
Proof. exact: iff_refl. Qed.

Lemma semidegree_oriented_paths_statement_compat :
  X2Legacy.semidegree_oriented_paths_statement
  <-> Digraph.conjectures.X2.semidegree_oriented_paths_statement.
Proof. exact: iff_refl. Qed.

Lemma stein_oriented_paths_strict_semidegree_statement_compat :
  X17Legacy.stein_oriented_paths_strict_semidegree_statement
  <-> Digraph.conjectures.X17.stein_oriented_paths_strict_semidegree_statement.
Proof. exact: iff_refl. Qed.

Lemma bounded_degree_acyclic_oriented_ramsey_linear_statement_compat :
  X107Legacy.bounded_degree_acyclic_oriented_ramsey_linear_statement
  <-> Digraph.conjectures.X107.bounded_degree_acyclic_oriented_ramsey_linear_statement.
Proof. exact: iff_refl. Qed.

(** ** Original certificates *)

(** The Original copies of B16's helpers, over the raw in-degrees (as B16's own certificates). *)
Lemma x221_eulerian_original_compat (D : diGraphType) :
  DegreeBalanceOriginal.x221_eulerian D <-> Digraph.conjectures.X221.x221_eulerian D.
Proof. exact: Digraph.migration.degree_balance.x221_eulerian_compat. Qed.

Lemma cv_eulerian_original_compat (D : diGraphType) :
  DegreeBalanceOriginal.cv_eulerian D = Digraph.conjectures.colouring_variants.eulerian D.
Proof. by []. Qed.

Lemma Eulerian_original_compat (D : diGraphType) :
  DegreeBalanceOriginal.Eulerian D <-> Digraph.conjectures.two_extremal.Eulerian D.
Proof. exact: iff_refl. Qed.

Lemma realises_W_original_compat (t : ptree) (D : diGraphType) :
  TwoExtremalGlueOriginal.realises_W t D <-> Digraph.conjectures.two_extremal_glue.realises_W t D.
Proof. exact: iff_refl. Qed.

Lemma realises_E_original_compat (t : ptree) (D : diGraphType) :
  GlueEulSubtypeOriginal.realises_E t D <-> Digraph.conjectures.glue_eul_subtype.realises_E t D.
Proof. exact: iff_refl. Qed.

(** B16's X221 row over the raw in-degree and poset-unavoidability's frozen [contains_subdigraph]. *)
Lemma x221_eulerian_avoidable_original_compat (F : diGraphType) :
  X221Original.eulerian_avoidable F <-> Digraph.conjectures.X221.x221_eulerian_avoidable F.
Proof.
have eE (D : diGraphType) : DegreeBalanceOriginal.x221_eulerian D <-> Digraph.conjectures.X221.x221_eulerian D.
  exact: Digraph.migration.degree_balance.x221_eulerian_compat.
have cE := Digraph.migration.tournament_unavoidability.contains_subdigraph_compat.
split=> -[d h]; exists d => k D eD dk.
  have [f [hf nc]] := h k D (iffRL (eE D) eD) dk.
  by exists f; split=> // c; apply: nc; apply/cE.
have [f [hf nc]] := h k D (iffLR (eE D) eD) dk.
by exists f; split=> // c; apply: nc; apply/cE.
Qed.

Lemma orientation_C4_eulerian_avoidable_statement_original_compat :
  X221Original.orientation_C4_eulerian_avoidable_statement
  <-> Digraph.conjectures.X221.orientation_C4_eulerian_avoidable_statement.
Proof. by split=> h b; apply/x221_eulerian_avoidable_original_compat. Qed.

(** One-way source-repair certificate, not a migration equivalence (2026-10-25, direction weaken; the
    identical repair is carried by the degree_balance statement entry): the live row gained the
    [loopless D] guard, so the original row implies it. *)
Lemma majority_3col_eulerian_statement_original_compat :
  ColouringVariantsOriginal.majority_3col_eulerian_statement
  -> Digraph.conjectures.colouring_variants.majority_3col_eulerian_statement.
Proof. by move=> h D _; exact: h. Qed.

Lemma H6_no_full_cover_original_compat :
  TwoExtremalOriginal.H6_no_full_cover <-> Digraph.conjectures.two_extremal.H6_no_full_cover.
Proof. exact: iff_refl. Qed.

Lemma conj_9_2_glued_original_compat :
  TwoExtremalGlueOriginal.conj_9_2_glued <-> Digraph.conjectures.two_extremal_glue.conj_9_2_glued.
Proof. exact: iff_refl. Qed.

Lemma conj_9_2_glued_e_original_compat :
  GlueEulSubtypeOriginal.conj_9_2_glued_e <-> Digraph.conjectures.glue_eul_subtype.conj_9_2_glued_e.
Proof. exact: iff_refl. Qed.

(** B1/B2's Mader delta-zero row over B1's raw subdivision and this family's frozen chain. *)
Lemma mader_delta_zero_bound_original_compat (F : diGraphType) (m : nat) :
  X2Original.mader_delta_zero_bound F m <-> Digraph.conjectures.X2.mader_delta_zero_bound F m.
Proof.
have sE := Digraph.migration.path_vertices.contains_subdivision_compat.
by split=> h D D0 sD; apply/sE; apply: h.
Qed.

Lemma mader_delta0_transitive_tournament_statement_original_compat :
  X2Original.mader_delta0_transitive_tournament_statement
  <-> Digraph.conjectures.X2.mader_delta0_transitive_tournament_statement.
Proof.
have bE := mader_delta_zero_bound_original_compat.
split=> h k; have [m [hm lm]] := h k; exists m; split.
- exact/bE.
- by move=> c /bE; apply: lm.
- exact/bE.
- by move=> c /bE; apply: lm.
Qed.

Print Assumptions Nout_compat.
Print Assumptions Nin_compat.
Print Assumptions indeg_compat.
Print Assumptions Nout2_compat.
Print Assumptions diregular_compat.
Print Assumptions diregular_ascription.
Print Assumptions cv_indeg_compat.
Print Assumptions antidirected_tree_compat.
Print Assumptions min_semidegree_at_least_compat.
Print Assumptions mader_delta_zero_bound_compat.
Print Assumptions least_mader_delta_zero_compat.
Print Assumptions antidirected_path_compat.
Print Assumptions min_semidegree_half_compat.
Print Assumptions x17_min_semidegree_strict_half_compat.
Print Assumptions x107_total_degree_at_most_compat.
Print Assumptions seymour_second_neighbourhood_statement_compat.
Print Assumptions long_dicycle_diregular_statement_compat.
Print Assumptions jackson_hamilton_small_diregular_statement_compat.
Print Assumptions hamilton_cycle_in_small_d_diregular_graphs_statement_compat.
Print Assumptions antidirected_trees_in_digraphs_statement_compat.
Print Assumptions arc_disjoint_directed_cycles_in_regular_directed_gra_statement_compat.
Print Assumptions decomposing_an_even_tournament_in_directed_paths_statement_compat.
Print Assumptions behzad_chartrand_wall_girth_regular_digraph_statement_compat.
Print Assumptions mader_delta0_transitive_tournament_statement_compat.
Print Assumptions semidegree_oriented_paths_statement_compat.
Print Assumptions stein_oriented_paths_strict_semidegree_statement_compat.
Print Assumptions bounded_degree_acyclic_oriented_ramsey_linear_statement_compat.
Print Assumptions x221_eulerian_original_compat.
Print Assumptions cv_eulerian_original_compat.
Print Assumptions Eulerian_original_compat.
Print Assumptions realises_W_original_compat.
Print Assumptions realises_E_original_compat.
Print Assumptions x221_eulerian_avoidable_original_compat.
Print Assumptions orientation_C4_eulerian_avoidable_statement_original_compat.
Print Assumptions majority_3col_eulerian_statement_original_compat.
Print Assumptions H6_no_full_cover_original_compat.
Print Assumptions conj_9_2_glued_original_compat.
Print Assumptions conj_9_2_glued_e_original_compat.
Print Assumptions mader_delta_zero_bound_original_compat.
Print Assumptions mader_delta0_transitive_tournament_statement_original_compat.
