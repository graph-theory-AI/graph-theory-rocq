(** * Packing.migration.set_separators — B26 certificates: X26's set separator and its row

    Frozen verbatim at the fixed B25 baseline a02e1c2: X26's [x26_separates_xy] (no simple sequence
    path from X to Y, [x26_xy_path] = B5's alias of [seq_set_path], has its vertex set
    [x26_path_vertices] = B1's alias of [seq_vertices] disjoint from Z) and the complete current row
    [bounded_degree_distant_induced_menger_statement] (for all d and Dmax a constant C > 0 before k, G,
    X and Y; maximum degree at most Dmax; k distinct distant X-Y paths or fewer than C * k vertices
    separating X from Y; d = 0 and the distinct-sequence reading kept).  Since B26 the live
    [x26_separates_xy] is a transparent alias of upstream [GraphTheory.core.connectivity.separator G X Y Z];
    the separator certificate is the unconditional [GTBase.set_separators.seq_separatorP] and the row
    certificate transports the separator clause pointwise.  The copies keep the live B1 / B5 aliases,
    the live distant-path vocabulary and the live balls.  The complete earlier row is B5's
    [X26Original] in Packing.migration.set_path (raw B1 support, raw B5 path predicate, raw separator;
    the balls are live at this pin), reused with B5's own certificate. *)

From GTBase Require Import base.
From GTBase Require set_separators.
From Packing.conjectures Require Import X26.
From Packing.migration Require set_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B5 := Packing.migration.set_path.

Module Legacy.

Definition x26_separates_xy (G : sgraph) (X Y Z : {set G}) : Prop :=
  forall p : seq G,
    x26_xy_path X Y p ->
    [disjoint x26_path_vertices p & Z] ->
    False.

End Legacy.

Module X26Legacy.

Definition bounded_degree_distant_induced_menger_statement : Prop :=
  forall d Dmax : nat, exists C : nat,
    0 < C /\
    forall (k : nat) (G : sgraph) (X Y : {set G}),
      Delta G <= Dmax ->
      x26_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < C * k /\
        Legacy.x26_separates_xy X Y Z.

End X26Legacy.

(** ** The separator: the sequence body is upstream [separator] *)

Lemma x26_separates_xy_compat (G : sgraph) (X Y Z : {set G}) :
  Legacy.x26_separates_xy X Y Z <-> x26_separates_xy X Y Z.
Proof. exact: set_separators.seq_separatorP. Qed.

(** ** The complete current row *)

Lemma bounded_degree_distant_induced_menger_statement_compat :
  X26Legacy.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof.
split=> h d Dmax; have [C [C0 hC]] := h d Dmax; exists C; split=> // k G X Y DG;
  case: (hC k G X Y DG) => [l | [Z [Zk sep]]];
  first [by left | by right; exists Z; split=> //; apply/x26_separates_xy_compat].
Qed.

(** ** The complete earlier row, reused from B5 with B5's own certificate *)

Lemma bounded_degree_distant_induced_menger_statement_original_compat :
  Packing.migration.set_path.X26Original.bounded_degree_distant_induced_menger_statement <->
  bounded_degree_distant_induced_menger_statement.
Proof. exact: B5.bounded_degree_distant_induced_menger_statement_original_compat. Qed.

Print Assumptions x26_separates_xy_compat.
Print Assumptions bounded_degree_distant_induced_menger_statement_compat.
Print Assumptions bounded_degree_distant_induced_menger_statement_original_compat.
