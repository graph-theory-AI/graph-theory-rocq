(** * Hom.migration.ordinal_path — B21 certificates: the U3 path graph onto GTBase.path_graphs

    Frozen verbatim at 9921abb (the B20 pin; byte-identical at 6de6ce3), with the original Section
    parameter [n]: the raw relation [pth_rel], its symmetry and irreflexivity proofs with their
    original proof scripts, the constructor [path_graph], and the complete row
    [extremal_problem_on_the_number_of_tree_endomorphism_statement]
    (opg:extremal_problem_on_the_number_of_tree_endomorphism).  Since B21 the live helpers are
    transparent aliases of [GTBase.path_graphs.ordinal_path_rel] / [ordinal_path].

    Certificates.  The frozen relation is the canonical one by conversion (the same raw body), so
    the frozen proofs build a graph isomorphic to the live one and the frozen constructor is
    isomorphic to the canonical path graph through upstream [eq_diso] (the identity on 'I_n); the
    constructors are not convertible, their proof fields differ.  The endomorphism count of the
    frozen constructor equals that of the live one by conversion (the Boolean [hom_ffun] unfolds the
    edge relation of each graph to the same raw relation), so the whole row is equivalent by
    conversion; the tree, cardinality and positivity premises and both inequalities are kept
    exactly, and no general isomorphism-invariance claim is used. *)

From GTBase Require Import base path_graphs.
From Hom.conjectures Require Import U3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The original declarations live in one Section with [Variable n].  A frozen copy must name the frozen
    relation and proofs by their qualified names ([Legacy.pth_rel], [Legacy.pth_sym], [Legacy.pth_irrefl]),
    and a section-local constant cannot be referenced with its module prefix before its section closes; so
    the copies keep the Section parameter [n] with one Section per declaration group, each generalising over
    [n] exactly as the originals do (the kernel evidence checks the exact types
    [forall n : nat, 'I_n -> 'I_n -> bool] and [nat -> sgraph]).  Recorded substitutions:
    [pth_rel -> (@Legacy.pth_rel n)], [pth_sym -> (@Legacy.pth_sym n)], [pth_irrefl -> (@Legacy.pth_irrefl n)];
    the proof scripts are the original ones. *)
Module Legacy.

Section PathGraphRel.
Variable n : nat.
Definition pth_rel (i j : 'I_n) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).
End PathGraphRel.

Section PathGraphProofs.
Variable n : nat.
Lemma pth_sym : symmetric (@Legacy.pth_rel n).
Proof. by move=> i j; rewrite /pth_rel orbC. Qed.
Lemma pth_irrefl : irreflexive (@Legacy.pth_rel n).
Proof. by move=> i; rewrite /pth_rel orbb (gtn_eqF (ltnSn _)). Qed.
End PathGraphProofs.

Section PathGraph.
Variable n : nat.
Definition path_graph : sgraph := SGraph (@Legacy.pth_sym n) (@Legacy.pth_irrefl n).
End PathGraph.

End Legacy.

Module U3Legacy.

Definition extremal_problem_on_the_number_of_tree_endomorphism_statement : Prop :=
  forall (n : nat) (T : sgraph),
    0 < n -> is_tree [set: T] -> #|T| = n ->
    (endo_count (Legacy.path_graph n) <= endo_count T)
      /\ (endo_count T <= endo_count (star_graph n)).

End U3Legacy.

(** ** Relation: the same raw body, by conversion *)

Lemma pth_rel_compat (n : nat) (i j : 'I_n) : Legacy.pth_rel i j = pth_rel i j.
Proof. by []. Qed.

(** ** Proofs: the frozen proofs build a graph isomorphic to the live one *)

Lemma pth_proofs_compat (n : nat) :
  SGraph (@Legacy.pth_sym n) (@Legacy.pth_irrefl n) ≃ SGraph (@pth_sym n) (@pth_irrefl n).
Proof. by apply: eq_diso => i j. Qed.

(** ** Constructor: isomorphic to the canonical path graph, by the identity on 'I_n *)

Lemma path_graph_compat (n : nat) : Legacy.path_graph n ≃ path_graph n.
Proof. by apply: eq_ordinal_path_diso => i j. Qed.

(** ** Row: the endomorphism counts agree by conversion, hence the whole row *)

Lemma endo_count_compat (n : nat) :
  endo_count (Legacy.path_graph n) = endo_count (path_graph n).
Proof. by []. Qed.

Lemma extremal_problem_on_the_number_of_tree_endomorphism_statement_compat :
  U3Legacy.extremal_problem_on_the_number_of_tree_endomorphism_statement <->
  extremal_problem_on_the_number_of_tree_endomorphism_statement.
Proof. by []. Qed.

Print Assumptions pth_rel_compat.
Print Assumptions pth_proofs_compat.
Print Assumptions path_graph_compat.
Print Assumptions endo_count_compat.
Print Assumptions extremal_problem_on_the_number_of_tree_endomorphism_statement_compat.
