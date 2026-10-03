(** * Packing.migration.ordinal_path — B21 certificates: the X18 / X226 path graphs onto GTBase.path_graphs

    Frozen verbatim at 9921abb (the B20 pin; byte-identical at 6de6ce3): the guarded relations
    [x18_path_rel] / [x226_path_rel], their symmetry and irreflexivity proofs with their original
    proof scripts, the constructors [x18_path_graph] / [x226_path_graph], and the two complete rows
    [path_partition_independent_set_balance_statement] (X18, arxiv:1611.03196#00) and
    [eta_bounded_path_free_classes_statement] (X226, arxiv:2302.04986#01).  Since B21 the live
    helpers are transparent aliases of [GTBase.path_graphs.ordinal_path_rel] / [ordinal_path].

    Certificates.  The frozen relations are pointwise equal to the canonical one: the guard
    [i != j] is redundant for consecutive indices ([ordinal_path_rel_guardedE]); this is an equality
    of Boolean relations, not a conversion.  The frozen constructors are isomorphic to the canonical
    path graph through upstream [eq_diso] (the identity on 'I_n); they are not convertible to it,
    their proof fields differ.  Both rows are equivalent to the live rows: independence transports
    along the pointwise edge equality, induced-freeness along the isomorphism
    ([GTBase.common.induced_free_diso]).  Every guard, quantifier order, bound and natural-number
    inequality of the rows is kept exactly; no statement, doc block, manifest row or status changes. *)

From GTBase Require Import base path_graphs.
From Packing.conjectures Require Import X15 X18 X226.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x18_path_rel (n : nat) : rel 'I_n :=
  fun i j => (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).

Lemma x18_path_sym (n : nat) : symmetric (@Legacy.x18_path_rel n).
Proof.
by move=> i j; rewrite /x18_path_rel eq_sym orbC.
Qed.

Lemma x18_path_irrefl (n : nat) : irreflexive (@Legacy.x18_path_rel n).
Proof. by move=> i; rewrite /x18_path_rel eqxx. Qed.

Definition x18_path_graph (n : nat) : sgraph :=
  SGraph (@Legacy.x18_path_sym n) (@Legacy.x18_path_irrefl n).

Definition x226_path_rel (t : nat) : rel 'I_t :=
  fun i j => (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).

Lemma x226_path_sym (t : nat) : symmetric (@Legacy.x226_path_rel t).
Proof. by move=> i j; rewrite /x226_path_rel eq_sym orbC. Qed.

Lemma x226_path_irrefl (t : nat) : irreflexive (@Legacy.x226_path_rel t).
Proof. by move=> i; rewrite /x226_path_rel eqxx. Qed.

Definition x226_path_graph (t : nat) : sgraph :=
  SGraph (@Legacy.x226_path_sym t) (@Legacy.x226_path_irrefl t).

End Legacy.

Module X18Legacy.

Definition path_partition_independent_set_balance_statement : Prop :=
  forall (n m : nat) (V : 'I_m -> {set Legacy.x18_path_graph n}),
    x18_vertex_partition V ->
    exists (S : {set Legacy.x18_path_graph n}) (b : 'I_m -> nat),
      x18_independent_set S /\
      (forall i : 'I_m, 2 * (#|S :&: V i| + b i) >= #|V i|)%N /\
      (2 * \sum_(i : 'I_m) b i <= m)%N /\
      forall i : 'I_m, b i <= 1.

End X18Legacy.

Module X226Legacy.

Definition eta_bounded_path_free_classes_statement : Prop :=
  forall t : nat,
    6 <= t ->
    x226_eta_bounded (fun G : sgraph => induced_free G (Legacy.x226_path_graph t)).

End X226Legacy.

(** ** Relations: the guard is redundant, so the frozen relations are pointwise the canonical one *)

Lemma x18_path_rel_compat (n : nat) (i j : 'I_n) :
  @Legacy.x18_path_rel n i j = @x18_path_rel n i j.
Proof. exact: ordinal_path_rel_guardedE. Qed.

Lemma x226_path_rel_compat (t : nat) (i j : 'I_t) :
  @Legacy.x226_path_rel t i j = @x226_path_rel t i j.
Proof. exact: ordinal_path_rel_guardedE. Qed.

(** ** Proofs: the frozen symmetry/irreflexivity proofs build a graph isomorphic to the live one *)

Lemma x18_path_proofs_compat (n : nat) :
  SGraph (@Legacy.x18_path_sym n) (@Legacy.x18_path_irrefl n)
    ≃ SGraph (@x18_path_sym n) (@x18_path_irrefl n).
Proof. by apply: eq_diso => i j; rewrite x18_path_rel_compat. Qed.

Lemma x226_path_proofs_compat (t : nat) :
  SGraph (@Legacy.x226_path_sym t) (@Legacy.x226_path_irrefl t)
    ≃ SGraph (@x226_path_sym t) (@x226_path_irrefl t).
Proof. by apply: eq_diso => i j; rewrite x226_path_rel_compat. Qed.

(** ** Constructors: isomorphic to the canonical path graph, by the identity on 'I_n *)

Lemma x18_path_graph_compat (n : nat) : Legacy.x18_path_graph n ≃ x18_path_graph n.
Proof. by apply: guarded_ordinal_path_diso => i j. Qed.

Lemma x226_path_graph_compat (t : nat) : Legacy.x226_path_graph t ≃ x226_path_graph t.
Proof. by apply: guarded_ordinal_path_diso => i j. Qed.

(** ** Rows *)

Lemma x18_independent_set_compat (n : nat) (S : {set 'I_n}) :
  @x18_independent_set (Legacy.x18_path_graph n) S <->
  @x18_independent_set (x18_path_graph n) S.
Proof.
have E (u v : Legacy.x18_path_graph n) :
  (u -- v) = ((u : x18_path_graph n) -- (v : x18_path_graph n)).
  exact: x18_path_rel_compat.
by split=> ind u v uS vS uv; apply: (ind u v uS vS); move: uv; rewrite E.
Qed.

Lemma path_partition_independent_set_balance_statement_compat :
  X18Legacy.path_partition_independent_set_balance_statement <->
  path_partition_independent_set_balance_statement.
Proof.
split=> h n m V part; have [S [b [ind rest]]] := h n m V part;
  by exists S, b; split=> //; apply/x18_independent_set_compat; exact: ind.
Qed.

Lemma eta_bounded_path_free_classes_statement_compat :
  X226Legacy.eta_bounded_path_free_classes_statement <->
  eta_bounded_path_free_classes_statement.
Proof.
split=> h t t6; have [f hf] := h t t6; exists f => G free G0; apply: (hf G) => //.
  exact: induced_free_diso (diso_sym (x226_path_graph_compat t)) free.
exact: induced_free_diso (x226_path_graph_compat t) free.
Qed.

Print Assumptions x18_path_rel_compat.
Print Assumptions x226_path_rel_compat.
Print Assumptions x18_path_proofs_compat.
Print Assumptions x226_path_proofs_compat.
Print Assumptions x18_path_graph_compat.
Print Assumptions x226_path_graph_compat.
Print Assumptions x18_independent_set_compat.
Print Assumptions path_partition_independent_set_balance_statement_compat.
Print Assumptions eta_bounded_path_free_classes_statement_compat.
