(** * Chromatic.migration.ordinal_path — B21 certificates: the X170 P_4 relation onto GTBase.path_graphs

    Frozen verbatim at 9921abb (the B20 pin; byte-identical at 6de6ce3): the relation
    [x170_p4_edge] on 'I_4, the two intermediaries [x170_induced_oriented_P4] and
    [x170_forb_oriented_P4_family] over the frozen relation, and the complete row
    [oriented_P4_forb_chi_bounded_statement] (arxiv:1605.07411#02) over the frozen intermediaries
    and the live C9 alias [x170_chi_bounded].  Since B21 the live relation is a transparent alias
    of [GTBase.path_graphs.ordinal_path_rel] at n = 4 (the same raw body, by conversion), so every
    certificate of this file but the Original is a conversion.

    The complete pre-C9/B21 Original [X170Original.oriented_P4_forb_chi_bounded_statement]
    combines the frozen P_4 chain with C9's frozen [X170Legacy.x170_chi_bounded] (bound as module
    [C9]) and is certified end to end through C9's own [x170_chi_bounded_compat].  C9's per-row
    snapshot [X170StatementsLegacy.oriented_P4_forb_chi_bounded_statement] intentionally keeps the
    live [x170_forb_oriented_P4_family]; it is left byte-exact and recorded reciprocally.

    The row is the corpus' BLOCKED known-unfaithful encoding (its exceptional set is mis-encoded,
    see the X170 doc block): the oriented-graph Record, the injective four-vertex map, the induced
    adjacency equality on every pair, the three orientation bits, the universal forbidden-code guard,
    [x170_nonexceptional] and the chi-bounding order are frozen exactly as they are, and nothing is
    repaired, relabelled or unblocked here. *)

From GTBase Require Import base chi_bounding path_graphs.
From Chromatic.conjectures Require Import X170.
From Chromatic.migration Require chi_bounded_classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module C9 := Chromatic.migration.chi_bounded_classes.

Module Legacy.

Definition x170_p4_edge (i j : 'I_4) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).

End Legacy.

Module X170Legacy.

Definition x170_induced_oriented_P4
    (O : x170_oriented_graph) (P : x170_oriented_P4_code) : Prop :=
  exists v : 'I_4 -> O,
    injective v /\
    (forall i j : 'I_4, (v i -- v j) = Legacy.x170_p4_edge i j) /\
    (forall i : 'I_3,
      x170_arc (v (inord (val i))) (v (inord (val i).+1)) =
        x170_code_forward P i).

Definition x170_forb_oriented_P4_family
    (P : {set x170_oriented_P4_code}) (O : x170_oriented_graph) : Prop :=
  forall Q : x170_oriented_P4_code,
    Q \in P -> ~ X170Legacy.x170_induced_oriented_P4 O Q.

Definition oriented_P4_forb_chi_bounded_statement : Prop :=
  forall P : {set x170_oriented_P4_code},
    x170_nonexceptional P ->
    x170_chi_bounded (X170Legacy.x170_forb_oriented_P4_family P).

End X170Legacy.

(** The complete pre-C9/B21 row: frozen P_4 chain and C9's frozen chi-boundedness. *)
Module X170Original.

Definition oriented_P4_forb_chi_bounded_statement : Prop :=
  forall P : {set x170_oriented_P4_code},
    x170_nonexceptional P ->
    C9.X170Legacy.x170_chi_bounded (X170Legacy.x170_forb_oriented_P4_family P).

End X170Original.

(** ** Relation and intermediaries: conversions *)

Lemma x170_p4_edge_compat (i j : 'I_4) : Legacy.x170_p4_edge i j = x170_p4_edge i j.
Proof. by []. Qed.

Lemma x170_induced_oriented_P4_compat (O : x170_oriented_graph) (P : x170_oriented_P4_code) :
  X170Legacy.x170_induced_oriented_P4 O P <-> x170_induced_oriented_P4 O P.
Proof. by []. Qed.

Lemma x170_forb_oriented_P4_family_compat
    (P : {set x170_oriented_P4_code}) (O : x170_oriented_graph) :
  X170Legacy.x170_forb_oriented_P4_family P O <-> x170_forb_oriented_P4_family P O.
Proof. by []. Qed.

(** ** Row and Original *)

Lemma oriented_P4_forb_chi_bounded_statement_compat :
  X170Legacy.oriented_P4_forb_chi_bounded_statement <->
  oriented_P4_forb_chi_bounded_statement.
Proof. by []. Qed.

Lemma oriented_P4_forb_chi_bounded_statement_original_compat :
  X170Original.oriented_P4_forb_chi_bounded_statement <->
  oriented_P4_forb_chi_bounded_statement.
Proof.
split=> h P nP; have := h P nP.
  by move/C9.x170_chi_bounded_compat.
by move/C9.x170_chi_bounded_compat.
Qed.

Print Assumptions x170_p4_edge_compat.
Print Assumptions x170_induced_oriented_P4_compat.
Print Assumptions x170_forb_oriented_P4_family_compat.
Print Assumptions oriented_P4_forb_chi_bounded_statement_compat.
Print Assumptions oriented_P4_forb_chi_bounded_statement_original_compat.
