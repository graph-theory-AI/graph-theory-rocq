(** * Packing.examples.supplied_matchings -- supplied edge-family corners (C25)

    Public-only: this client imports [GTBase] and [Packing.foundations.matching], never a
    conjecture or migration module.  A supplied family M is an upstream
    [GraphTheory.connectivity.matching] when its members are genuine edges and each vertex
    lies in at most one member; the edge-validity clause is not implied by the incidence
    bound:
    - the empty family is a matching of every graph, isolated vertices included;
    - one genuine edge is a matching, even beside an uncovered vertex;
    - an empty member, a singleton member, an off-edge pair and two distinct incident edges
      are each rejected. *)
From GTBase Require Import base common.
From Packing.foundations Require Import matching.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation v0 := (@Ordinal 3 0 isT : 'K_3).
Local Notation v1 := (@Ordinal 3 1 isT : 'K_3).
Local Notation v2 := (@Ordinal 3 2 isT : 'K_3).

Example empty_family_matching (G : sgraph) : matching (G := G) set0.
Proof. exact: matching0. Qed.

Example one_edge_beside_isolated_vertex : matching [set [set v0; v1]].
Proof. exact: matching_K3_edge. Qed.

Example empty_member_rejected (G : sgraph) (M : {set {set G}}) :
  set0 \in M -> ~ matching M.
Proof. by move=> zM mM; move: zM; rewrite (negbTE (not_matching_set0_member mM)). Qed.

Example singleton_member_rejected (G : sgraph) (M : {set {set G}}) (x : G) :
  [set x] \in M -> ~ matching M.
Proof. by move=> xM mM; move: xM; rewrite (negbTE (@not_matching_loop G M x mM)). Qed.

Example off_edge_pair_rejected (G : sgraph) (x y : G) :
  ~~ x -- y -> ~ matching [set [set x; y]].
Proof.
move=> nxy /matching_at_most_oneP [/subsetP sub _].
by move: (sub _ (set11 _)); rewrite in_edges (negbTE nxy).
Qed.

Example incident_edges_rejected : ~ matching [set [set v0; v1]; [set v0; v2]].
Proof. exact: not_matching_K3_adjacent. Qed.
