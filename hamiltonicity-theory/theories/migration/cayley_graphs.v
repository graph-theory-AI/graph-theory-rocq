(** A26 Cayley graphs (Hamilton): U2's undirected Cayley graph -- Section [Cayley], its relation, two constructor
    proofs and graph -- with U2's [hamiltonian_cycle] (and its [Arguments]), [is_hamiltonian] and [symmetric_set]
    and the complete Hamiltonicity row, frozen at the A25 pin 5832ba9.  Baseline, hashes and exact substitutions are
    recorded in meta/migration_reports/cayley_graphs.spec.json.
    - [Legacy], [ProofsLegacy], [GraphLegacy]: the Section in dependency order, each in a verbatim copy of its
      scaffolding [Variable gT : finGroupType], [Variable S : {set gT}] and [Local Open Scope group_scope], so the
      texts elaborate as in U2 and the discharged arguments are the original's; references to earlier frozen names
      are module-qualified.
    - [U2Legacy]: [hamiltonian_cycle] with its [Arguments ... : clear implicits], [is_hamiltonian], [symmetric_set]
      and the row (more than two elements, [S] inverse-closed and generating, then a Hamiltonian cycle).
    The frozen relation is convertible to GTBase.cayley_graphs's (the source's [group_scope] elaborates to the same
    term as the explicit [%g] of D2ram and of the public relation); the frozen graph differs from
    [undirected_cayley_graph] only in its opaque proof fields, so the two are related by pointwise adjacency and the
    identity isomorphism, and the chains and the row, which read graphs only through vertices and adjacency,
    convert. *)
From mathcomp Require Import all_boot fingroup.
From GTBase Require Import base cayley_graphs.
From Hamilton.conjectures Require Import U2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Section Cayley.
Variable gT : finGroupType.
Variable S : {set gT}.
Local Open Scope group_scope.
Definition cayley_rel : rel gT :=
  fun x y => (x != y) && ((x^-1 * y \in S) || (y^-1 * x \in S)).
End Cayley.

End Legacy.

Module ProofsLegacy.

Section Cayley.
Variable gT : finGroupType.
Variable S : {set gT}.
Local Open Scope group_scope.
Lemma cayley_sym : symmetric (@Legacy.cayley_rel gT S).
Proof. by move=> x y; rewrite /Legacy.cayley_rel eq_sym orbC. Qed.
Lemma cayley_irrefl : irreflexive (@Legacy.cayley_rel gT S).
Proof. by move=> x; rewrite /Legacy.cayley_rel eqxx. Qed.
End Cayley.

End ProofsLegacy.

Module GraphLegacy.

Section Cayley.
Variable gT : finGroupType.
Variable S : {set gT}.
Local Open Scope group_scope.
Definition cayley_graph : sgraph := SGraph (@ProofsLegacy.cayley_sym gT S) (@ProofsLegacy.cayley_irrefl gT S).
End Cayley.

End GraphLegacy.

Module U2Legacy.

Definition hamiltonian_cycle (G : sgraph) (c : seq G) : bool :=
  ucycleb (--) c && (size c == #|G|).
Arguments U2Legacy.hamiltonian_cycle : clear implicits.

Definition is_hamiltonian (G : sgraph) : Prop :=
  exists c : seq G, U2Legacy.hamiltonian_cycle G c.

Definition symmetric_set (gT : finGroupType) (S : {set gT}) : Prop :=
  forall x : gT, (x \in S) = (x^-1 \in S)%g.

Definition hamiltonicity_of_cayley_graphs_statement : Prop :=
  forall (gT : finGroupType) (S : {set gT}),
    2 < #|gT| -> U2Legacy.symmetric_set S -> <<S>>%g = [set: gT] ->
    U2Legacy.is_hamiltonian (GraphLegacy.cayley_graph S).

End U2Legacy.

(** The Section: the relation is the public one by conversion; the constructor proofs and the graphs are related by
    the identity isomorphism, never by an equation between proof fields. *)
Lemma cayley_rel_compat (gT : finGroupType) (S : {set gT}) (x y : gT) :
  @Legacy.cayley_rel gT S x y = @Hamilton.conjectures.U2.cayley_rel gT S x y.
Proof.
by [].
Qed.

Lemma cayley_proofs_compat (gT : finGroupType) (S : {set gT}) :
  SGraph (@ProofsLegacy.cayley_sym gT S) (@ProofsLegacy.cayley_irrefl gT S) ≃
  SGraph (@Hamilton.conjectures.U2.cayley_sym gT S) (@Hamilton.conjectures.U2.cayley_irrefl gT S).
Proof. by apply: eq_diso => x y. Qed.

Lemma cayley_graph_compat (gT : finGroupType) (S : {set gT}) :
  @edge_rel (GraphLegacy.cayley_graph S) =2 @edge_rel (Hamilton.conjectures.U2.cayley_graph S).
Proof.
by [].
Qed.

Lemma cayley_graph_diso (gT : finGroupType) (S : {set gT}) : GraphLegacy.cayley_graph S ≃ Hamilton.conjectures.U2.cayley_graph S.
Proof. by rewrite /GraphLegacy.cayley_graph /Hamilton.conjectures.U2.cayley_graph /undirected_cayley_graph; apply: eq_diso => x y. Qed.

(** The Hamiltonicity vocabulary is unchanged text: the same terms. *)
Lemma hamiltonian_cycle_compat (G : sgraph) (c : seq G) :
  U2Legacy.hamiltonian_cycle G c = Hamilton.conjectures.U2.hamiltonian_cycle G c.
Proof.
by [].
Qed.

Lemma is_hamiltonian_compat (G : sgraph) :
  U2Legacy.is_hamiltonian G <-> Hamilton.conjectures.U2.is_hamiltonian G.
Proof.
rewrite /U2Legacy.is_hamiltonian.
reflexivity.
Qed.

Lemma symmetric_set_compat (gT : finGroupType) (S : {set gT}) :
  U2Legacy.symmetric_set S <-> Hamilton.conjectures.U2.symmetric_set S.
Proof.
rewrite /U2Legacy.symmetric_set.
reflexivity.
Qed.

(** The row: Hamiltonian cycles read the graph only through its vertices and adjacency. *)
Lemma hamiltonicity_of_cayley_graphs_statement_compat :
  U2Legacy.hamiltonicity_of_cayley_graphs_statement <->
  Hamilton.conjectures.U2.hamiltonicity_of_cayley_graphs_statement.
Proof.
rewrite /U2Legacy.hamiltonicity_of_cayley_graphs_statement.
reflexivity.
Qed.
