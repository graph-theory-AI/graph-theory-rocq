(** A16 clique number (chromatic): the frozen X112 and X124 clique-number helpers, X124's polynomial chi-bound
    chain and row, and X112's complete row.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/clique_number.spec.json.
    - [Legacy]: X112's helper is already upstream [ω([set: G])] (a conversion); X124's bigmax over all cliques
      equals it by the unconditional [omega_setT_maxE] (no nonempty guard).
    - [X124Legacy]: the chain and the row over the frozen bigmax; X124's blocked merge-width antecedent is kept
      verbatim.  X124 has no earlier frozen history, so this row is also its complete row.
    - [X112Original]: X112's helper no longer reaches its current row (C9 moved the chi-bound to the public
      predicate), so only its complete row is owed: C9's pre-C9 chi-bound helper with the frozen clique number
      and the whole closure row, both copied from 0659592.  C9's module is aliased, not imported; the bridges
      reuse C9's certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Chromatic.conjectures Require Import X112 X124.
From Chromatic.migration Require chi_bounded_classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** C9's certificate module, aliased without Import: its module names coincide with this file's. *)
Module C9 := Chromatic.migration.chi_bounded_classes.

Module Legacy.

Definition x112_omega (G : sgraph) : nat := ω([set: G]).

Definition x124_omega (G : sgraph) : nat := \max_(S : {set G} | cliqueb S) #|S|.

End Legacy.

Module X124Legacy.

Definition x124_poly_chi_bounded (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G -> χ([set: G]) <= x124_poly_eval p (Legacy.x124_omega G).

Definition dreier_torunczyk_merge_width_poly_chi_bounded_statement : Prop :=
  forall C : sgraph -> Prop,
    x124_bounded_merge_width C -> X124Legacy.x124_poly_chi_bounded C.

End X124Legacy.

Module X112Original.

Definition x112_chi_bounded (D : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, D G -> χ([set: G]) <= f (Legacy.x112_omega G).

Definition chi_bounded_closure_substitution_gluing_statement : Prop :=
  forall (C : sgraph -> Prop) (b : nat),
    X112Original.x112_chi_bounded C -> X112Original.x112_chi_bounded (x112_closure C b).

End X112Original.

Lemma x112_omega_compat (G : sgraph) :
  Legacy.x112_omega G = x112_omega G.
Proof. by []. Qed.

(** Not a conversion: the bigmax over all cliques against upstream [ω([set: G])] ([omega_setT_maxE],
    unconditional, [K_0] included). *)
Lemma x124_omega_compat (G : sgraph) :
  Legacy.x124_omega G = x124_omega G.
Proof. exact: esym (omega_setT_maxE G). Qed.

(** The same coefficient list [p] in both directions; only the clique number is rewritten. *)
Lemma x124_poly_chi_bounded_compat (C : sgraph -> Prop) :
  X124Legacy.x124_poly_chi_bounded C <-> x124_poly_chi_bounded C.
Proof. by split=> -[p h]; exists p => G CG; move: (h G CG); rewrite x124_omega_compat. Qed.

Lemma dreier_torunczyk_merge_width_poly_chi_bounded_statement_compat :
  X124Legacy.dreier_torunczyk_merge_width_poly_chi_bounded_statement <-> dreier_torunczyk_merge_width_poly_chi_bounded_statement.
Proof. rewrite /X124Legacy.dreier_torunczyk_merge_width_poly_chi_bounded_statement /dreier_torunczyk_merge_width_poly_chi_bounded_statement; by setoid_rewrite x124_poly_chi_bounded_compat. Qed.

(** Complete X112: conversions to C9's frozen chi-bound and row, then C9's certificates. *)
Lemma x112_chi_bounded_original_compat (D : sgraph -> Prop) :
  X112Original.x112_chi_bounded D <-> x112_chi_bounded D.
Proof. exact: C9.x112_chi_bounded_compat. Qed.

Lemma chi_bounded_closure_substitution_gluing_statement_original_compat :
  X112Original.chi_bounded_closure_substitution_gluing_statement <-> chi_bounded_closure_substitution_gluing_statement.
Proof. exact: C9.chi_bounded_closure_substitution_gluing_statement_compat. Qed.
