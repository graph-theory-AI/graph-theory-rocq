(** * Packing.foundations.matching -- simple-graph matchings: the upstream API

    Library migration, batch C family "matching" (meta/LIBRARY_MIGRATION_PLAN.md
    section 15; registry entry [matching] in meta/library_primitives.json;
    generated report meta/migration_reports/matching.md from
    matching.spec.json; record meta/LIBRARY_MIGRATION_C1.md; public client
    theories/examples/matching.v).

    ** Canonical primitive

    The corpus notion "M is a matching of the simple graph G" is the upstream
    [GraphTheory.connectivity.matching] (re-exported by [GTBase.base]):

      matching M := {subset M <= E(G)} /\
                    {in M &, forall e1 e2 (x : G), x \in e1 -> x \in e2 -> e1 = e2}.

    Contract: [M : {set {set G}}] is a set of edges of [G] -- every member is a
    two-element set [[set x; y]] with [x -- y] -- and no vertex lies in two
    distinct members.  Nothing is assumed about [G]: the empty graph, the
    one-vertex graph and edgeless graphs are allowed, and [set0] is their only
    matching.

    ** Corner cases, all proved below

    - [set0] is a matching of every graph ([matching0]);
    - a member is an edge, hence has exactly two vertices
      ([matching_card_edge]); no singleton "loop" [[set x]] and no empty member
      is ever allowed ([not_matching_loop], [not_matching_set0_member]);
    - matchings are closed under subsets ([matching_sub]);
    - a single edge is a matching ([matching_edge1], [matching_K2],
      [matching_K3_edge]); two adjacent edges never are
      ([not_matching_K3_adjacent]: the second clause has teeth).

    ** The three local presentations

    The statement waves spelled the second clause in three ways; each is
    proved equivalent to the upstream clause, with the subset clause in the
    boolean [\subset] form the waves use:

    - every vertex lies in at most one member (X15, X18): [matching_at_most_oneP];
    - distinct members are [disjoint] (X14):                [matching_pairwise_disjointP];
    - distinct members have empty intersection (X180):      [matching_setI_eq0P].

    The frozen legacy bodies and the per-statement old/new certificates are in
    [theories/migration/matching.v] of each package concerned (packing, misc,
    extremal; not re-exported).  Perfect matchings are
    [GTBase.common.perfect_matching]; the local perfect-matching,
    edge-partition and edge-family helpers are separate families and are not
    touched by this module.

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Basic API *)

(** The subset clause in boolean form. *)
Lemma matching_subset (G : sgraph) (M : {set {set G}}) :
  matching M -> M \subset E(G).
Proof. by case=> MS _; apply/subsetP. Qed.

(** Members are edges, hence two-element sets. *)
Lemma matching_card_edge (G : sgraph) (M : {set {set G}}) (e : {set G}) :
  matching M -> e \in M -> #|e| = 2.
Proof.
by move=> [MS _] /MS /edgesP[x [y [-> xy]]]; rewrite cards2 (sg_edgeNeq xy).
Qed.

(** Matchings are closed under subsets. *)
Lemma matching_sub (G : sgraph) (M N : {set {set G}}) :
  matching M -> N \subset M -> matching N.
Proof.
move=> [MS M1] /subsetP NM; split=> [e /NM/MS //|e1 e2 /NM e1M /NM e2M].
exact: M1.
Qed.

(** ** The three local presentations *)

(** At most one member through each vertex (the X15/X18 spelling). *)
Lemma matching_at_most_oneP (G : sgraph) (M : {set {set G}}) :
  matching M <->
  M \subset E(G) /\ forall v : G, #|[set e in M | v \in e]| <= 1.
Proof.
split=> [[MS M1]|[MS M1]]; split.
- exact/subsetP.
- move=> v; apply/card_le1_eqP => e1 e2.
  rewrite !inE => /andP[e1M ve1] /andP[e2M ve2].
  exact: (M1 _ _ e2M e1M v ve2 ve1).
- exact/subsetP.
- move=> e1 e2 e1M e2M x xe1 xe2; symmetry.
  move/card_le1_eqP: (M1 x) => H; apply: H; rewrite !inE.
  + by rewrite e1M xe1.
  + by rewrite e2M xe2.
Qed.

(** Distinct members are disjoint (the X14 spelling). *)
Lemma matching_pairwise_disjointP (G : sgraph) (M : {set {set G}}) :
  matching M <->
  M \subset E(G) /\
  forall e f : {set G}, e \in M -> f \in M -> e != f -> [disjoint e & f].
Proof.
split=> [[MS M1]|[MS M1]]; split.
- exact/subsetP.
- move=> e f eM fM ef; rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE.
  apply/negbTE/negP => /andP[xe xf].
  by move: ef; rewrite (M1 _ _ eM fM x xe xf) eqxx.
- exact/subsetP.
- move=> e f eM fM x xe xf; apply/eqP; apply/negPn/negP => ef.
  by move: (M1 e f eM fM ef) => /disjointFr /(_ xe); rewrite xf.
Qed.

(** Distinct members have an empty intersection (the X180 spelling). *)
Lemma matching_setI_eq0P (G : sgraph) (M : {set {set G}}) :
  matching M <->
  M \subset E(G) /\
  forall e f : {set G}, e \in M -> f \in M -> e != f -> e :&: f = set0.
Proof.
split=> [/matching_pairwise_disjointP [MS M1]|[MS M1]].
- by split=> // e f eM fM ef; apply/eqP; rewrite setI_eq0; exact: M1.
- apply/matching_pairwise_disjointP; split=> // e f eM fM ef.
  by rewrite -setI_eq0; apply/eqP; exact: M1.
Qed.

(** ** Grounding *)

(** The empty set is a matching of every graph, the empty graph included. *)
Lemma matching0 (G : sgraph) : matching (G := G) set0.
Proof. by split=> [e|e1 e2]; rewrite inE. Qed.

(** A singleton "loop" [[set x]] is never a member of a matching. *)
Lemma not_matching_loop (G : sgraph) (M : {set {set G}}) (x : G) :
  matching M -> [set x] \notin M.
Proof.
move=> mM; apply/negP => xM; have := matching_card_edge mM xM.
by rewrite cards1.
Qed.

(** Nor is the empty set. *)
Lemma not_matching_set0_member (G : sgraph) (M : {set {set G}}) :
  matching M -> set0 \notin M.
Proof.
move=> mM; apply/negP => zM; have := matching_card_edge mM zM.
by rewrite cards0.
Qed.

(** A single edge is a matching (non-vacuity for every graph with an edge). *)
Lemma matching_edge1 (G : sgraph) (x y : G) :
  x -- y -> matching [set [set x; y]].
Proof.
move=> xy; split=> [e|e1 e2]; rewrite !inE.
- by move/eqP->; rewrite in_edges.
- by move=> /eqP-> /eqP->.
Qed.

(** The edge of [K_2] (shared with [GTBase.common.perfect_matching_K2]). *)
Lemma matching_K2 : matching [set [set: 'K_2]].
Proof. exact: (proj1 perfect_matching_K2). Qed.

Local Notation k0 := (@Ordinal 3 0 isT : 'K_3).
Local Notation k1 := (@Ordinal 3 1 isT : 'K_3).
Local Notation k2 := (@Ordinal 3 2 isT : 'K_3).

(** One edge of the triangle is a matching. *)
Lemma matching_K3_edge : matching [set [set k0; k1]].
Proof. exact: matching_edge1. Qed.

(** Two adjacent edges of the triangle are not (the second clause has teeth). *)
Lemma not_matching_K3_adjacent : ~ matching [set [set k0; k1]; [set k0; k2]].
Proof.
move=> [_ M1].
have := M1 _ _ (set21 _ _) (set22 _ _) k0 (set21 _ _) (set21 _ _).
by move/setP/(_ k1); rewrite !inE eqxx orbT.
Qed.

Print Assumptions matching_at_most_oneP.
Print Assumptions matching_pairwise_disjointP.
Print Assumptions matching_setI_eq0P.
Print Assumptions matching_sub.
Print Assumptions matching_card_edge.
Print Assumptions matching0.
Print Assumptions not_matching_loop.
Print Assumptions matching_edge1.
Print Assumptions matching_K2.
Print Assumptions matching_K3_edge.
Print Assumptions not_matching_K3_adjacent.
