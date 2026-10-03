(** * Extremal.migration.consecutive_in_cycle — frozen cyclic-adjacency chains (library migration B4)

    Batch B, family [consecutive-in-cycle]
    (meta/library_primitives/consecutive-in-cycle.json).  [Legacy] freezes the
    boolean helpers [x4_consecutive_in_cycle] and D2str's same-body cross-name
    adapter [cyc_edge] (an eta-expanded [rel G]) verbatim as they stood at 49ddc03,
    before the migration; the live helpers now unfold to
    [GTBase.walks_paths.seq_cyclic_consecutiveb], whose body is the same
    disjunction, so every certificate below is a kernel-checked conversion.

    [X4Legacy] freezes the five-tuple C5 edge predicate, its count and the
    statement; [XE1Legacy] the cross-module H5 graph (two negated chord exclusions
    and the positive edge-coverage clause) and erdos:567; [XE2Legacy] the incident
    chord count, the no-cycle predicate, the extremal predicate (maximum
    quantifier) and erdos:767 (strict [< k], truncated subtraction).
    [D2strLegacy] freezes [on_cycle_walk], [induced_cycle], [peripheral_cycle], the
    OPG statement, and [geodesic_cycle] inside a verbatim copy of the weighted
    Section (real field [R], graph [G], [ell] of type [G -> G -> R], ring scope).
    D2str's names carry no wave prefix, so their frozen copies are renamed with a
    [d2str_] prefix; the frozen source is [Legacy.cyc_edge].  Definitions that do
    not reach a helper (edge counts, [shortest_walk], [edge_length]) are the live
    ones.  Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/consecutive_in_cycle.md. *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra.
From Extremal.conjectures Require Import X4 XE1 XE2 D2str.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x4_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

Definition cyc_edge (G : sgraph) (c : seq G) : rel G :=
  fun x y => ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

End Legacy.

Module X4Legacy.

Definition edge_in_c5 (G : sgraph) (x y : G) : bool :=
  [exists c : 5.-tuple G,
      [&& ucycleb (--) (val c), x \in val c, y \in val c
        & Legacy.x4_consecutive_in_cycle (val c) x y]].

Definition c5_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      [&& (p.1 -- p.2), ((enum_rank p.1) < (enum_rank p.2))%N
        & edge_in_c5 p.1 p.2]]|.

Definition c5_edge_count_above_turan_statement : Prop :=
  forall G : sgraph, forall n : nat,
    #|G| = n -> n * n < 4 * x4_edge_count G ->
    2 * n * n <= 9 * c5_edge_count G.

End X4Legacy.

Module XE1Legacy.

Definition h5_graph (G : sgraph) : Prop :=
  exists c : seq G, exists e1 e2 : {set G},
    #|G| = 5 /\
    (forall v : G, v \in c) /\
    ucycle (--) c /\
    size c = 5 /\
    #|e1| = 2 /\ #|e2| = 2 /\
    e1 \in x4_edge_set G /\
    e2 \in x4_edge_set G /\
    [disjoint e1 & e2] /\
    e1 \subset [set v : G | v \in c] /\
    e2 \subset [set v : G | v \in c] /\
    (forall x y : G, [set x; y] = e1 -> ~~ Legacy.x4_consecutive_in_cycle c x y) /\
    (forall x y : G, [set x; y] = e2 -> ~~ Legacy.x4_consecutive_in_cycle c x y) /\
    (forall x y : G, x -- y ->
      Legacy.x4_consecutive_in_cycle c x y \/ [set x; y] = e1 \/ [set x; y] = e2).

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

End XE1Legacy.

Module XE2Legacy.

Definition incident_cycle_chord_count (G : sgraph) (c : seq G) (v : G) : nat :=
  #|[set u : G |
      [&& u \in c, v \in c, u != v, v -- u
        & ~~ Legacy.x4_consecutive_in_cycle c v u]]|.

Definition no_cycle_with_incident_chords (G : sgraph) (k : nat) : Prop :=
  forall c : seq G, xe2_cycle c ->
    forall v : G, v \in c -> incident_cycle_chord_count c v < k.

Definition incident_chord_extremal (k n m : nat) : Prop :=
  (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m /\
      no_cycle_with_incident_chords G k) /\
  forall m' : nat,
    (exists G : sgraph,
      #|G| = n /\ x4_edge_count G = m' /\
      no_cycle_with_incident_chords G k) ->
    m' <= m.

Definition erdos_767_statement : Prop :=
  forall k : nat, exists N : nat,
    forall (n m : nat),
      N <= n ->
      incident_chord_extremal k n m ->
      m = (k + 1) * n - (k + 1) ^ 2.

End XE2Legacy.

Module D2strLegacy.

Definition d2str_on_cycle_walk (G : sgraph) (c : seq G) (u : G) (p : seq G) : bool :=
  all (fun e => Legacy.cyc_edge c e.1 e.2) (zip (u :: p) p).

Section Weighted.
Variable R : realFieldType.
Variable G : sgraph.
Implicit Type ell : G -> G -> R.
Local Open Scope ring_scope.

Definition d2str_geodesic_cycle ell (c : seq G) : Prop :=
  ucycle (--) c /\
  forall u v : G, u \in c -> v \in c ->
    exists p : seq G, shortest_walk ell u v p /\ d2str_on_cycle_walk c u p.

End Weighted.

Definition d2str_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  forall x y : G, x \in c -> y \in c -> x -- y -> Legacy.cyc_edge c x y.

Definition d2str_peripheral_cycle (G : sgraph) (c : seq G) : Prop :=
  d2str_induced_cycle c /\ connected (~: [set x in c]).

Definition geodesic_cycles_and_tuttes_theorem_statement : Prop :=
  forall (R : realFieldType) (G : sgraph),
    k_connected G 3 ->
    exists ell : G -> G -> R,
      edge_length ell /\
      (forall c : seq G, d2str_geodesic_cycle ell c -> d2str_peripheral_cycle c).

End D2strLegacy.

(** ** Certificates *)

Lemma x4_consecutive_in_cycle_compat (G : sgraph) (c : seq G) (u v : G) :
  Legacy.x4_consecutive_in_cycle c u v = x4_consecutive_in_cycle c u v.
Proof. by []. Qed.

Lemma cyc_edge_compat (G : sgraph) (c : seq G) : Legacy.cyc_edge c = cyc_edge c.
Proof. by []. Qed.

Lemma x4_edge_in_c5_compat (G : sgraph) (x y : G) :
  X4Legacy.edge_in_c5 x y = x4_edge_in_c5 x y.
Proof. by []. Qed.

Lemma x4_c5_edge_count_compat (G : sgraph) : X4Legacy.c5_edge_count G = x4_c5_edge_count G.
Proof. by []. Qed.

Lemma c5_edge_count_above_turan_statement_compat :
  X4Legacy.c5_edge_count_above_turan_statement <-> c5_edge_count_above_turan_statement.
Proof. exact: iff_refl. Qed.

Lemma xe1_h5_graph_compat (G : sgraph) : XE1Legacy.h5_graph G <-> xe1_h5_graph G.
Proof. exact: iff_refl. Qed.

Lemma erdos_567_statement_compat : XE1Legacy.erdos_567_statement <-> erdos_567_statement.
Proof. exact: iff_refl. Qed.

Lemma xe2_incident_cycle_chord_count_compat (G : sgraph) (c : seq G) (v : G) :
  XE2Legacy.incident_cycle_chord_count c v = xe2_incident_cycle_chord_count c v.
Proof. by []. Qed.

Lemma xe2_no_cycle_with_incident_chords_compat (G : sgraph) (k : nat) :
  XE2Legacy.no_cycle_with_incident_chords G k <-> xe2_no_cycle_with_incident_chords G k.
Proof. exact: iff_refl. Qed.

Lemma xe2_incident_chord_extremal_compat (k n m : nat) :
  XE2Legacy.incident_chord_extremal k n m <-> xe2_incident_chord_extremal k n m.
Proof. exact: iff_refl. Qed.

Lemma erdos_767_statement_compat : XE2Legacy.erdos_767_statement <-> erdos_767_statement.
Proof. exact: iff_refl. Qed.

Lemma on_cycle_walk_compat (G : sgraph) (c : seq G) (u : G) (p : seq G) :
  D2strLegacy.d2str_on_cycle_walk c u p = on_cycle_walk c u p.
Proof. by []. Qed.

Lemma geodesic_cycle_compat (R : realFieldType) (G : sgraph) (ell : G -> G -> R) (c : seq G) :
  D2strLegacy.d2str_geodesic_cycle ell c <-> geodesic_cycle ell c.
Proof. exact: iff_refl. Qed.

Lemma induced_cycle_compat (G : sgraph) (c : seq G) :
  D2strLegacy.d2str_induced_cycle c <-> induced_cycle c.
Proof. exact: iff_refl. Qed.

Lemma peripheral_cycle_compat (G : sgraph) (c : seq G) :
  D2strLegacy.d2str_peripheral_cycle c <-> peripheral_cycle c.
Proof. exact: iff_refl. Qed.

Lemma geodesic_cycles_and_tuttes_theorem_statement_compat :
  D2strLegacy.geodesic_cycles_and_tuttes_theorem_statement <->
  geodesic_cycles_and_tuttes_theorem_statement.
Proof. exact: iff_refl. Qed.
