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
    meta/migration_reports/strongly_regular.spec.json.

    SOURCE REPAIR (2026-10-25): the frozen eight-graph row is a theorem: K_{2,2}, ..., K_{9,9} are connected
    nontrivial, triangle-free and strongly regular ([D5Legacy_row_holds]).  The live D5 row now asks for an
    eighth triangle-free strongly regular graph with [0 < mu < k], isomorphic to none of the seven known graphs
    (Spectral.foundations.triangle_free_srg; see the triangle_free_strongly_regular_graphs entry of
    meta/STATEMENT_IMPROVEMENTS.md).  Its certificate below is therefore a ONE-WAY SOURCE-REPAIR certificate
    (live -> frozen), NOT a migration equivalence, bound by the spec's [repair] entry.  The other certificates
    of this file keep their exact iffs. *)

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

(** ** The frozen eight-graph row is a theorem

    [K_{n,n}] is triangle-free and, for [n >= 2], connected nontrivial strongly regular with [(n, 0, n)];
    [K_{2,2}], ..., [K_{9,9}] have pairwise different vertex counts.  This is the defect that the source repair
    of 2026-10-25 removes (meta/STATEMENT_IMPROVEMENTS.md, triangle_free_strongly_regular_graphs entry). *)

Lemma d5_Knn_triangle_free n : triangle_free 'K_n,n.
Proof. by move=> [x|x] [y|y] [z|z]. Qed.

Lemma d5_Knn_strongly_regular n : connected_nontrivial_strongly_regular 'K_n.+2,n.+2.
Proof.
exists n.+2, 0%N, n.+2; split.
- exact: (@Knm_connected n.+1 n.+1).
- by split=> //; rewrite card_sum !card_ord addnS /= -addSnnS ltn_addr.
split.
- by move=> [x|y]; rewrite ?deg_Knm_l ?deg_Knm_r.
- move=> [x|x] [y|y] uv //.
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
- move=> [x|x] [y|y] _ nadj //.
  + by rewrite /common_nbr !opn_Knm_l setIid card_imset ?cardsT ?card_ord //; exact: inr_inj.
  + by rewrite /common_nbr !opn_Knm_r setIid card_imset ?cardsT ?card_ord //; exact: inl_inj.
Qed.

Lemma d5_diso_card (G H : sgraph) : inhabited (G ≃ H) -> #|G| = #|H|.
Proof. by case=> i; exact: bij_eq_card (bij.bij_bijective (diso_v i)). Qed.

Lemma D5Legacy_row_holds : D5Legacy.triangle_free_strongly_regular_graphs_statement.
Proof.
exists (fun i : 'I_8 => 'K_(val i).+2,(val i).+2); split.
- move=> i; split; first exact: d5_Knn_triangle_free.
  by apply/d5_strongly_regular_compat; exact: d5_Knn_strongly_regular.
- move=> i j ij /d5_diso_card.
  rewrite !card_sum !card_ord !addnS !addSn => /eqP.
  rewrite !eqSS => /eqP h.
  have ji : i = j by apply: val_inj; move: h; rewrite !addnn; exact: double_inj.
  by rewrite ji eqxx in ij.
Qed.

(** ** Full-statement certificate: a ONE-WAY SOURCE-REPAIR certificate (live -> frozen), not a migration
    equivalence (2026-10-25).  The live row asks for an eighth triangle-free strongly regular graph with
    [0 < mu < k], isomorphic to none of the seven known graphs; the frozen row is a theorem
    ([D5Legacy_row_holds]), so the live row implies it.  The converse would solve the open problem. *)

Lemma triangle_free_strongly_regular_graphs_statement_compat :
  triangle_free_strongly_regular_graphs_statement -> D5Legacy.triangle_free_strongly_regular_graphs_statement.
Proof. by move=> _; exact: D5Legacy_row_holds. Qed.
