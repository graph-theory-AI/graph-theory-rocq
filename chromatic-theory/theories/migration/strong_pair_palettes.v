(** * Chromatic.migration.strong_pair_palettes — D13 stage 1 certificates: U5's pair-palette helpers and row

    Frozen verbatim at the D11 pin 5a107c3, references between the frozen helpers qualified [Legacy.]: U5's
    [diff_edge x y u v] (the unordered pairs differ), [near_edge x y u v] (the eight disjuncts: a shared vertex or an
    adjacent pair of endpoints), [strong_edge_colourable G k] (a map on ALL ordered vertex pairs into ['I_k],
    symmetric, separating two host edges whose pairs are distinct and near, the guards in this order; no nonemptiness or
    palette guard) and the complete row [strong_edge_colouring_statement] (every [G] with [0 < Delta G] is colourable
    with [(5 * Delta G ^ 2 - 2 * Delta G + 1) %/ 4] colours when [Delta G] is odd and [5 * Delta G ^ 2 %/ 4] when it is
    even; [Delta] and [odd] stay the live providers).  The row's documentation, including its line-graph-distance
    wording, is unchanged.  Since D13 stage 1 the three helpers are
    Chromatic.foundations.strong_pair_palettes' [distinct_edge_pairs], [near_edge_pairs] and [strong_pair_colourable],
    the same bodies by conversion, so all four certificates below are kernel-checked conversions.  No earlier
    migration snapshot reaches these declarations. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import strong_pair_palettes.
From Chromatic.conjectures Require Import U5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition diff_edge (G : sgraph) (x y u v : G) : bool :=
  ~~ (((x == u) && (y == v)) || ((x == v) && (y == u))).

Definition near_edge (G : sgraph) (x y u v : G) : bool :=
  [|| x == u, x == v, y == u, y == v, x -- u, x -- v, y -- u | y -- v].

Definition strong_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> G -> 'I_k,
    (forall x y : G, col x y = col y x) /\
    (forall x y u v : G, x -- y -> u -- v ->
        Legacy.diff_edge x y u v -> Legacy.near_edge x y u v -> col x y != col u v).

End Legacy.

Module U5Legacy.

Definition strong_edge_colouring_statement : Prop :=
  forall G : sgraph, 0 < Delta G ->
    Legacy.strong_edge_colourable G
      (if odd (Delta G)
       then (5 * (Delta G) ^ 2 - 2 * (Delta G) + 1) %/ 4
       else (5 * (Delta G) ^ 2) %/ 4).

End U5Legacy.

Lemma diff_edge_compat (G : sgraph) (x y u v : G) : Legacy.diff_edge x y u v = diff_edge x y u v.
Proof. by []. Qed.

Lemma near_edge_compat (G : sgraph) (x y u v : G) : Legacy.near_edge x y u v = near_edge x y u v.
Proof. by []. Qed.

Lemma strong_edge_colourable_compat (G : sgraph) (k : nat) :
  Legacy.strong_edge_colourable G k <-> strong_edge_colourable G k.
Proof. exact: iff_refl. Qed.

Lemma strong_edge_colouring_statement_compat :
  U5Legacy.strong_edge_colouring_statement <-> strong_edge_colouring_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions diff_edge_compat.
Print Assumptions near_edge_compat.
Print Assumptions strong_edge_colourable_compat.
Print Assumptions strong_edge_colouring_statement_compat.
