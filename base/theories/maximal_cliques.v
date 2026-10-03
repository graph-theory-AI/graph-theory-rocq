(** * GTBase.maximal_cliques -- inclusion-maximal cliques of a finite simple graph

    [maximal_clique S] is MathComp's inclusion-maximality [maxset] of the clique predicate [cliqueb]: [S] is a
    clique and no proper superset of [S] is a clique ([maximal_cliqueP], through GraphTheory's [maxset_properP]
    and [cliqueP]).  [nontrivial_maximal_clique S] adds the size guard [1 < #|S|].  Every clique extends to a
    maximal one ([maximal_clique_exists]).
    Inclusion-maximal is NOT maximum cardinality: upstream [maxcliques] (cliques of size omega) and GTMisc U13's
    [is_max_clique] are different contracts; a singleton next to a larger clique, or the [K_2] of a disjoint
    [K_2 + K_3], is inclusion-maximal without being maximum (examples/maximal_cliques.v).
    Registry: meta/library_primitives/maximal-clique.json (A18). *)
From GTBase Require Import base.
From GraphTheory Require Import preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MaximalCliques.
Variable G : sgraph.
Implicit Types S T : {set G}.

(** Inclusion-maximal cliques: no proper superset is a clique. *)
Definition maximal_clique S : bool := maxset (@cliqueb G) S.

(** Inclusion-maximal cliques with at least two vertices. *)
Definition nontrivial_maximal_clique S : bool := (1 < #|S|) && maximal_clique S.

Lemma maximal_cliqueP S :
  reflect (clique S /\ forall T, S \proper T -> ~ clique T) (maximal_clique S).
Proof.
apply: (iffP maxset_properP) => [[/cliqueP cS h]|[cS h]].
  by split=> // T ST /cliqueP cT; move: (h T ST); rewrite cT.
by split=> [|T ST]; [exact/cliqueP | apply/negP => /cliqueP; exact: h].
Qed.

(** The Boolean presentation, conjunction order included. *)
Lemma maximal_cliqueE S :
  maximal_clique S = cliqueb S && [forall T : {set G}, (S \proper T) ==> ~~ cliqueb T].
Proof.
apply/maxset_properP/andP => -[cS h]; split=> //.
  by apply/forallP => T; apply/implyP; exact: h.
by move=> T ST; exact: (implyP (forallP h T)).
Qed.

Lemma nontrivial_maximal_cliqueE S :
  nontrivial_maximal_clique S =
  [&& 1 < #|S|, cliqueb S & [forall T : {set G}, (S \proper T) ==> ~~ cliqueb T]].
Proof. by rewrite /nontrivial_maximal_clique maximal_cliqueE. Qed.

Lemma maximal_clique_clique S : maximal_clique S -> clique S.
Proof. by case/maximal_cliqueP. Qed.

Lemma maximal_clique_proper S T : maximal_clique S -> S \proper T -> ~ clique T.
Proof. by case/maximal_cliqueP => _; exact. Qed.

Lemma maximal_clique_exists S : clique S -> exists2 T, maximal_clique T & S \subset T.
Proof. by move=> /cliqueP cS; have [T mT ST] := maxset_exists cS; exists T. Qed.

Lemma nontrivial_maximal_clique_maximal S : nontrivial_maximal_clique S -> maximal_clique S.
Proof. by case/andP. Qed.

End MaximalCliques.
