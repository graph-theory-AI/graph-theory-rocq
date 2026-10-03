(** A12 exact minimum degree (misc): the frozen X227 attained minimum and row arxiv:1812.09752#00.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree.spec.json.
    [x227_min_degree] (universal bound first, attaining vertex second) converts to [GTBase.base.min_degree];
    the three conjuncts of the row, including the eventual growth of the third function, are frozen verbatim. *)
From GTBase Require Import base.
From GTMisc.conjectures Require Import X227.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x227_min_degree (G : sgraph) (d : nat) : Prop :=
  (forall v : G, (d <= #|N(v)|)%N) /\ (exists v : G, #|N(v)| = d).

End Legacy.

Module X227Legacy.

Definition hat_guessing_degree_degeneracy_bounds_statement : Prop :=
  [/\ (exists f1 : nat -> nat,
         forall G : sgraph, x227_hat_guessing_le G (f1 (Delta G))),
      (exists f2 : nat -> nat,
         forall (G : sgraph) (d : nat), k_degenerate G d -> x227_hat_guessing_le G (f2 d))
    & (exists f3 : nat -> nat,
         (forall (G : sgraph) (d : nat),
            Legacy.x227_min_degree G d -> x227_hat_guessing_win G (f3 d)) /\
         (forall M : nat, eventually (fun d => (M <= f3 d)%N)))].

End X227Legacy.

Lemma x227_min_degree_compat (G : sgraph) (d : nat) :
  Legacy.x227_min_degree G d <->
  x227_min_degree G d.
Proof. exact: iff_refl. Qed.

Lemma hat_guessing_degree_degeneracy_bounds_statement_compat :
  X227Legacy.hat_guessing_degree_degeneracy_bounds_statement <->
  hat_guessing_degree_degeneracy_bounds_statement.
Proof. exact: iff_refl. Qed.
