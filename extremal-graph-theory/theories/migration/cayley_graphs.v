(** A26 Cayley graphs (extremal): D2ram's undirected Cayley graph -- Section [CayleyGraph], its relation, two
    constructor proofs and graph -- frozen at the A25 pin 5832ba9 with the complete Ramsey row over it.  Baseline,
    hashes and exact substitutions are recorded in meta/migration_reports/cayley_graphs.spec.json.
    - [Legacy], [ProofsLegacy], [GraphLegacy]: the Section in dependency order, each in a verbatim copy of its
      scaffolding [Variables (gT : finGroupType) (S : {set gT})], so the discharged arguments are the original's;
      references to earlier frozen names are module-qualified ([cayley_adj] -> [(@Legacy.cayley_adj gT S)], the same
      term once the Section is closed).
    - [D2ramLegacy]: the Ramsey row (one positive [c] before every finite abelian group of order > 1, then one
      inverse-closed [S] with both [2 ^ omega] and [2 ^ alpha] at most [#|gT| ^ c] for that same graph).
    The frozen relation is convertible to GTBase.cayley_graphs's; the frozen graph differs from
    [undirected_cayley_graph] only in its opaque proof fields, so the two are related by pointwise adjacency and the
    identity isomorphism, and the row, which reads the graph only through its vertices and adjacency, converts. *)
From mathcomp Require Import all_boot all_fingroup.
From GTBase Require Import base set_pairs cayley_graphs.
From Extremal.conjectures Require Import D2ram.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Section CayleyGraph.
Variables (gT : finGroupType) (S : {set gT}).
Definition cayley_adj : rel gT :=
  fun x y => (x != y) && (((x^-1 * y)%g \in S) || ((y^-1 * x)%g \in S)).
End CayleyGraph.

End Legacy.

Module ProofsLegacy.

Section CayleyGraph.
Variables (gT : finGroupType) (S : {set gT}).
Lemma cayley_adj_sym : symmetric (@Legacy.cayley_adj gT S).
Proof. by move=> x y; rewrite /Legacy.cayley_adj eq_sym orbC. Qed.
Lemma cayley_adj_irrefl : irreflexive (@Legacy.cayley_adj gT S).
Proof. by move=> x; rewrite /Legacy.cayley_adj eqxx. Qed.
End CayleyGraph.

End ProofsLegacy.

Module GraphLegacy.

Section CayleyGraph.
Variables (gT : finGroupType) (S : {set gT}).
Definition cayley_graph : sgraph := SGraph (@ProofsLegacy.cayley_adj_sym gT S) (@ProofsLegacy.cayley_adj_irrefl gT S).
End CayleyGraph.

End GraphLegacy.

Module D2ramLegacy.

Definition ramsey_properties_of_cayley_graphs_statement : Prop :=
  exists c : nat, (0 < c)%N /\
    forall gT : finGroupType, abelian [set: gT] -> (1 < #|gT|)%N ->
      exists S : {set gT},
        (forall x : gT, (x \in S) = ((x^-1)%g \in S)) /\
        (2 ^ ω([set: GraphLegacy.cayley_graph S]) <= #|gT| ^ c)%N /\
        (2 ^ α([set: GraphLegacy.cayley_graph S]) <= #|gT| ^ c)%N.

End D2ramLegacy.

(** The Section: the relation is the public one by conversion; the constructor proofs and the graphs are related by
    the identity isomorphism, never by an equation between proof fields. *)
Lemma cayley_adj_compat (gT : finGroupType) (S : {set gT}) (x y : gT) :
  @Legacy.cayley_adj gT S x y = @Extremal.conjectures.D2ram.cayley_adj gT S x y.
Proof.
by [].
Qed.

Lemma cayley_adj_proofs_compat (gT : finGroupType) (S : {set gT}) :
  SGraph (@ProofsLegacy.cayley_adj_sym gT S) (@ProofsLegacy.cayley_adj_irrefl gT S) ≃
  SGraph (@Extremal.conjectures.D2ram.cayley_adj_sym gT S) (@Extremal.conjectures.D2ram.cayley_adj_irrefl gT S).
Proof. by apply: eq_diso => x y. Qed.

Lemma cayley_graph_compat (gT : finGroupType) (S : {set gT}) :
  @edge_rel (GraphLegacy.cayley_graph S) =2 @edge_rel (Extremal.conjectures.D2ram.cayley_graph S).
Proof.
by [].
Qed.

Lemma cayley_graph_diso (gT : finGroupType) (S : {set gT}) : GraphLegacy.cayley_graph S ≃ Extremal.conjectures.D2ram.cayley_graph S.
Proof. by rewrite /GraphLegacy.cayley_graph /Extremal.conjectures.D2ram.cayley_graph /undirected_cayley_graph; apply: eq_diso => x y. Qed.

(** The row: clique and independence numbers read the graph only through its vertices and adjacency. *)
Lemma ramsey_properties_of_cayley_graphs_statement_compat :
  D2ramLegacy.ramsey_properties_of_cayley_graphs_statement <->
  Extremal.conjectures.D2ram.ramsey_properties_of_cayley_graphs_statement.
Proof.
rewrite /D2ramLegacy.ramsey_properties_of_cayley_graphs_statement.
reflexivity.
Qed.
