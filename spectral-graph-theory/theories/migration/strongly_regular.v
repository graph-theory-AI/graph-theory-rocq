(** * Spectral.migration.strongly_regular -- A33 frozen D5 strongly regular predicate and its matrix grounding

    The D5 predicate (frozen at 7c23ef2) is ONE flat existential of five conjuncts: [connected [set: G]], the degree
    guard [0 < k /\ k < #|G|.-1], [regular G k] and the two counting clauses.  It is equivalent (proved iff, not
    convertible: the three counting clauses are grouped into [strongly_regular_parameters]) to GTBase's
    [connected_nontrivial_strongly_regular], with exactly the same three guards; [K_{2,2}] stays in, [K_2] and the
    degenerate graphs stay out.  The eight-graph row keeps its quantifiers and non-isomorphism clause.
    The grounding_D5 matrix theory (frozen at 9c47cd0): [sr_clauses], [sr_mateq] and [strongly_regular_alg] convert
    to [strongly_regular_parameters], [Spectral.foundations.strongly_regular_matrix.strongly_regular_matrix_identity]
    and [connected_nontrivial_strongly_regular_matrix]; its two theorems hold of the frozen bodies
    ([legacy_sr_mateqE], [legacy_strongly_regularE]).  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/strongly_regular.spec.json. *)

From GTBase Require Import base strongly_regular.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral foundations.strongly_regular_matrix.
From Spectral.conjectures Require Import D5 grounding_D5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Legacy.

Definition strongly_regular (G : sgraph) : Prop :=
  exists k lam mu : nat,
    [/\ connected [set: G],
        (0 < k)%N /\ (k < (#|G|).-1)%N,
        regular G k,
        (forall u v : G, u -- v -> #|common_nbr u v| = lam) &
        (forall u v : G, u != v -> ~~ (u -- v) -> #|common_nbr u v| = mu)].

End Legacy.

Module D5Legacy.

Definition triangle_free_strongly_regular_graphs_statement : Prop :=
  exists g : 'I_8 -> sgraph,
    (forall i, triangle_free (g i) /\ Legacy.strongly_regular (g i)) /\
    (forall i j, i != j -> ~ inhabited (g i ≃ g j)).

End D5Legacy.

Module GroundingLegacy.

Definition sr_clauses (G:sgraph) (k lam mu : nat) : Prop :=
  [/\ regular G k,
      (forall u v : G, u -- v -> #|common_nbr u v| = lam) &
      (forall u v : G, u != v -> ~~ (u -- v) -> #|common_nbr u v| = mu)].

Definition sr_mateq (G : sgraph) (k lam mu : nat) : Prop :=
  adjmx int G *m adjmx int G
    = k%:R%:M + lam%:R *: adjmx int G
      + mu%:R *: (const_mx 1 - 1%:M - adjmx int G).

Definition strongly_regular_alg (G : sgraph) : Prop :=
  exists k lam mu : nat,
    [/\ connected [set: G], (0 < k)%N /\ (k < (#|G|).-1)%N & GroundingLegacy.sr_mateq G k lam mu].

End GroundingLegacy.

(** ** Source certificates. *)

Lemma d5_strongly_regular_compat (G : sgraph) :
  Legacy.strongly_regular G <-> strongly_regular G.
Proof.
split.
- by case=> k [lam] [mu] [conn kk rk hlam hmu]; exists k, lam, mu.
- by case=> k [lam] [mu] [conn kk [rk hlam hmu]]; exists k, lam, mu.
Qed.

Lemma sr_clauses_compat (G : sgraph) (k lam mu : nat) :
  GroundingLegacy.sr_clauses G k lam mu <-> sr_clauses G k lam mu.
Proof. exact: iff_refl. Qed.

Lemma sr_mateq_compat (G : sgraph) (k lam mu : nat) :
  GroundingLegacy.sr_mateq G k lam mu <-> sr_mateq G k lam mu.
Proof. exact: iff_refl. Qed.

Lemma strongly_regular_alg_compat (G : sgraph) :
  GroundingLegacy.strongly_regular_alg G <-> strongly_regular_alg G.
Proof. exact: iff_refl. Qed.

(** ** The frozen matrix theory still holds of the frozen bodies. *)

Lemma legacy_sr_mateqE (G : sgraph) (k lam mu : nat) :
  GroundingLegacy.sr_mateq G k lam mu <-> GroundingLegacy.sr_clauses G k lam mu.
Proof. exact: sr_mateqE. Qed.

Lemma legacy_strongly_regularE (G : sgraph) :
  Legacy.strongly_regular G <-> GroundingLegacy.strongly_regular_alg G.
Proof.
split=> [/d5_strongly_regular_compat/strongly_regularE // | /(strongly_regularE G)/d5_strongly_regular_compat //].
Qed.

(** ** Full-statement certificate. *)

Lemma triangle_free_strongly_regular_graphs_statement_compat :
  D5Legacy.triangle_free_strongly_regular_graphs_statement <-> triangle_free_strongly_regular_graphs_statement.
Proof.
split=> -[g [hg hiso]]; exists g; split=> // i; have [tf sr] := hg i; split=> //.
- exact/d5_strongly_regular_compat.
- exact/d5_strongly_regular_compat.
Qed.
