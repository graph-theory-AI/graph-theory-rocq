(** * GTMisc.migration.distant_paths — B27 certificates: distant path families of X39, X116 and X146, four rows

    Frozen verbatim at the fixed prerequisite 058da18 (B26 plus the A22 ball delta): the raw pairwise relations of
    X39, X116 and X146 (unequal sequence values; disjoint supports and the closed [d.-1]-set-ball condition), the X39
    and X116 existence wrappers (exact size [k], [uniq], endpoint-set paths), X146's dependent A-path existence chain
    (its distinct endpoints in [A] and internal [A] avoidance kept) and four complete current rows: X39's ball
    separator row, the cross-module X40 distance-2 row (partial), X116's bounded-separator row and X146's coarse
    Gallai row.  Since B27 the six GTMisc sources are aliases of [GTBase.distant_paths]; the conjunct presentation
    goes through the unconditional [pairwise_distant_seqsP] / [has_k_distant_set_pathsP] and the rows through
    pointwise transports.  The copies keep the live B1 / B5 / A22 / B26 vocabulary (supports, set paths, balls,
    separators, X146's A-paths and hitting clause).  The complete earlier rows are A22's [X39Original],
    [X40Original], [X116Original] and [X146Original] in GTMisc.migration.balls, reused with A22's certificates. *)

From GTBase Require Import base balls.
From GTBase Require distant_paths.
From GTMisc.conjectures Require Import X39 X40 X116 X146.
From GTMisc.migration Require balls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module A22 := GTMisc.migration.balls.

Module Legacy.

Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x39_path_vertices p & x39_path_vertices q] /\
    [disjoint x39_set_ball (d.-1) (x39_path_vertices p) & x39_path_vertices q].

Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x39_xy_path X Y p) /\
    Legacy.x39_pairwise_distant_paths d paths.

Definition x116_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x116_path_vertices p & x116_path_vertices q] /\
    [disjoint x116_set_ball (d.-1) (x116_path_vertices p) & x116_path_vertices q].

Definition x116_has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x116_ST_path S T p) /\
    Legacy.x116_pairwise_distant_paths d paths.

Definition x146_pairwise_distant_A_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x146_path_vertices p & x146_path_vertices q] /\
    [disjoint x146_set_ball (d.-1) (x146_path_vertices p) & x146_path_vertices q].

End Legacy.

Module X39Legacy.

Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      Legacy.x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        x39_separates_xy X Y (x39_set_ball (c * d) Z).

End X39Legacy.

Module X40Legacy.

Definition coarse_menger_distance_two_separator_statement : Prop :=
  forall k : nat,
    1 <= k ->
    exists ell : nat,
      0 < ell /\
      forall (G : sgraph) (S T : {set G}),
        Legacy.x39_has_k_distant_xy_paths 2 k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          x39_separates_xy S T (x39_set_ball ell X).

End X40Legacy.

Module X116Legacy.

Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        Legacy.x116_has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            x116_ST_path S T p ->
            exists v : G,
              v \in x116_path_vertices p /\ v \in x116_set_ball l X.

End X116Legacy.

Module X146Legacy.

Definition x146_has_k_distant_A_paths
    (G : sgraph) (A : {set G}) (d k : nat) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x146_A_path A p) /\
    Legacy.x146_pairwise_distant_A_paths d paths.

Definition geelen_coarse_gallai_A_paths_statement : Prop :=
  exists f g : nat -> nat,
    forall (k d : nat) (G : sgraph) (A : {set G}),
      1 <= k ->
      1 <= d ->
      X146Legacy.x146_has_k_distant_A_paths A d k \/
      exists Z : {set G},
        #|Z| <= f k /\
        x146_every_A_path_hits_ball A Z (g d).

End X146Legacy.

(** ** The raw relations and wrappers: the conjunct presentation through the unconditional bridges *)

Lemma x39_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  Legacy.x39_pairwise_distant_paths d paths <-> x39_pairwise_distant_paths d paths.
Proof. exact: distant_paths.pairwise_distant_seqsP. Qed.

Lemma x116_pairwise_distant_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  Legacy.x116_pairwise_distant_paths d paths <-> x116_pairwise_distant_paths d paths.
Proof. exact: distant_paths.pairwise_distant_seqsP. Qed.

Lemma x146_pairwise_distant_A_paths_compat (G : sgraph) (d : nat) (paths : seq (seq G)) :
  Legacy.x146_pairwise_distant_A_paths d paths <-> x146_pairwise_distant_A_paths d paths.
Proof. exact: distant_paths.pairwise_distant_seqsP. Qed.

Lemma x39_has_k_distant_xy_paths_compat (G : sgraph) (d k : nat) (X Y : {set G}) :
  Legacy.x39_has_k_distant_xy_paths d k X Y <-> x39_has_k_distant_xy_paths d k X Y.
Proof. exact: distant_paths.has_k_distant_set_pathsP. Qed.

Lemma x116_has_k_distant_ST_paths_compat (G : sgraph) (d k : nat) (S T : {set G}) :
  Legacy.x116_has_k_distant_ST_paths d k S T <-> x116_has_k_distant_ST_paths d k S T.
Proof. exact: distant_paths.has_k_distant_set_pathsP. Qed.

(** ** X146's A-path chain: the same list, the A-path clause unchanged *)

Lemma x146_has_k_distant_A_paths_compat (G : sgraph) (A : {set G}) (d k : nat) :
  X146Legacy.x146_has_k_distant_A_paths A d k <-> x146_has_k_distant_A_paths A d k.
Proof.
split=> -[ps [sz [u [ap dist]]]]; exists ps; split=> //; split=> //; split=> //.
  exact: (proj1 (x146_pairwise_distant_A_paths_compat d ps) dist).
exact: (proj2 (x146_pairwise_distant_A_paths_compat d ps) dist).
Qed.

(** ** The four complete current rows *)

Lemma coarse_menger_ball_separator_statement_compat :
  X39Legacy.coarse_menger_ball_separator_statement <-> coarse_menger_ball_separator_statement.
Proof.
split=> h k; have [c hc] := h k; exists c => d G X Y;
  case: (hc d G X Y) => [l | r];
  first [by left; apply/x39_has_k_distant_xy_paths_compat | by right].
Qed.

Lemma coarse_menger_distance_two_separator_statement_compat :
  X40Legacy.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof.
split=> h k k1; have [ell [ell0 he]] := h k k1; exists ell; split=> // G S T;
  case: (he G S T) => [l | r];
  first [by left; apply/x39_has_k_distant_xy_paths_compat | by right].
Qed.

Lemma coarse_menger_paths_bounded_separator_statement_compat :
  X116Legacy.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof.
split=> h k d k1 d1; have [l [l0 hl]] := h k d k1 d1; exists l; split=> // G S T;
  case: (hl G S T) => [hk | r];
  first [by left; apply/x116_has_k_distant_ST_paths_compat | by right].
Qed.

Lemma geelen_coarse_gallai_A_paths_statement_compat :
  X146Legacy.geelen_coarse_gallai_A_paths_statement <-> geelen_coarse_gallai_A_paths_statement.
Proof.
split=> -[f [g h]]; exists f, g => k d G A k1 d1;
  case: (h k d G A k1 d1) => [hk | r];
  first [by left; apply/x146_has_k_distant_A_paths_compat | by right].
Qed.

(** ** The four complete earlier rows, reused from A22 with A22's own certificates *)

Lemma coarse_menger_ball_separator_statement_original_compat :
  GTMisc.migration.balls.X39Original.coarse_menger_ball_separator_statement <->
  coarse_menger_ball_separator_statement.
Proof. exact: A22.coarse_menger_ball_separator_statement_original_compat. Qed.

Lemma coarse_menger_distance_two_separator_statement_original_compat :
  GTMisc.migration.balls.X40Original.coarse_menger_distance_two_separator_statement <->
  coarse_menger_distance_two_separator_statement.
Proof. exact: A22.coarse_menger_distance_two_separator_statement_original_compat. Qed.

Lemma coarse_menger_paths_bounded_separator_statement_original_compat :
  GTMisc.migration.balls.X116Original.coarse_menger_paths_bounded_separator_statement <->
  coarse_menger_paths_bounded_separator_statement.
Proof. exact: A22.coarse_menger_paths_bounded_separator_statement_original_compat. Qed.

Lemma geelen_coarse_gallai_A_paths_statement_original_compat :
  GTMisc.migration.balls.X146Original.geelen_coarse_gallai_A_paths_statement <->
  geelen_coarse_gallai_A_paths_statement.
Proof. exact: A22.geelen_coarse_gallai_A_paths_statement_original_compat. Qed.

Print Assumptions x39_pairwise_distant_paths_compat.
Print Assumptions x116_pairwise_distant_paths_compat.
Print Assumptions x146_pairwise_distant_A_paths_compat.
Print Assumptions x39_has_k_distant_xy_paths_compat.
Print Assumptions x116_has_k_distant_ST_paths_compat.
Print Assumptions x146_has_k_distant_A_paths_compat.
Print Assumptions coarse_menger_ball_separator_statement_compat.
Print Assumptions coarse_menger_distance_two_separator_statement_compat.
Print Assumptions coarse_menger_paths_bounded_separator_statement_compat.
Print Assumptions geelen_coarse_gallai_A_paths_statement_compat.
Print Assumptions coarse_menger_ball_separator_statement_original_compat.
Print Assumptions coarse_menger_distance_two_separator_statement_original_compat.
Print Assumptions coarse_menger_paths_bounded_separator_statement_original_compat.
Print Assumptions geelen_coarse_gallai_A_paths_statement_original_compat.
