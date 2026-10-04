(** * GTMisc.migration.set_separators — B26 certificates: X39's set separator and the X39 / X40 rows

    Frozen verbatim at the fixed B25 baseline a02e1c2: X39's [x39_separates_xy] (no simple sequence
    path from X to Y, [x39_xy_path] = B5's alias of [seq_set_path], has its vertex set
    [x39_path_vertices] = B1's alias of [seq_vertices] disjoint from A) and the two complete current rows
    [coarse_menger_ball_separator_statement] (X39: for every k a constant c before d, G, X and Y; k
    distinct distant X-Y paths or fewer than k centres whose (c * d)-ball separates X from Y; no guard on
    k or d) and [coarse_menger_distance_two_separator_statement] (X40, a partial row: k >= 1, a positive
    radius ell before G, S and T, distance 2, at most k - 1 centres whose ell-ball separates).  Since B26
    the live [x39_separates_xy] is a transparent alias of upstream
    [GraphTheory.core.connectivity.separator G X Y A]; the separator certificate is the unconditional
    [GTBase.set_separators.seq_separatorP] and the row certificates transport the separator clause
    pointwise.  The copies keep the live B1 / B5 aliases, the live distant-path vocabulary and the live
    balls.  The complete earlier rows are B5's [X39Original] and [X40Original] in
    GTMisc.migration.set_path (raw B1 support, raw B5 path predicate, raw separator; the balls are
    live at this pin), reused with B5's own certificates. *)

From GTBase Require Import base.
From GTBase Require set_separators.
From GTMisc.conjectures Require Import X39 X40.
From GTMisc.migration Require set_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B5 := GTMisc.migration.set_path.

Module Legacy.

Definition x39_separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    x39_xy_path X Y p ->
    [disjoint x39_path_vertices p & A] ->
    False.

End Legacy.

Module X39Legacy.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        Legacy.x39_separates_xy X Y (x39_set_ball (c * d) Z).

End X39Legacy.

Module X40Legacy.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          Legacy.x39_separates_xy S T (x39_set_ball ell X).

End X40Legacy.

(** ** The separator: the sequence body is upstream [separator] *)

Lemma x39_separates_xy_compat (G : sgraph) (X Y A : {set G}) :
  Legacy.x39_separates_xy X Y A <-> x39_separates_xy X Y A.
Proof. exact: set_separators.seq_separatorP. Qed.

(** ** The two complete current rows *)

Lemma coarse_menger_ball_separator_statement_compat :
  X39Legacy.coarse_menger_ball_separator_statement <-> coarse_menger_ball_separator_statement.
Proof.
split=> h k; have [c hc] := h k; exists c => d G X Y;
  case: (hc d G X Y) => [l | [Z [Zk sep]]];
  first [by left | by right; exists Z; split=> //; apply/x39_separates_xy_compat].
Qed.

Lemma coarse_menger_distance_two_separator_statement_compat :
  X40Legacy.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof.
split=> h k k1; have [ell [ell0 he]] := h k k1; exists ell; split=> // G S T;
  case: (he G S T) => [l | [X [Xk sep]]];
  first [by left | by right; exists X; split=> //; apply/x39_separates_xy_compat].
Qed.

(** ** The two complete earlier rows, reused from B5 with B5's own certificates *)

Lemma coarse_menger_ball_separator_statement_original_compat :
  GTMisc.migration.set_path.X39Original.coarse_menger_ball_separator_statement <->
  coarse_menger_ball_separator_statement.
Proof. exact: B5.coarse_menger_ball_separator_statement_original_compat. Qed.

Lemma coarse_menger_distance_two_separator_statement_original_compat :
  GTMisc.migration.set_path.X40Original.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof. exact: B5.coarse_menger_distance_two_separator_statement_original_compat. Qed.

Print Assumptions x39_separates_xy_compat.
Print Assumptions coarse_menger_ball_separator_statement_compat.
Print Assumptions coarse_menger_distance_two_separator_statement_compat.
Print Assumptions coarse_menger_ball_separator_statement_original_compat.
Print Assumptions coarse_menger_distance_two_separator_statement_original_compat.
