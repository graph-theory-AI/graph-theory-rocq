From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp classical_sets zify.
From GraphTheory Require Import digraph sgraph.
Lemma aws_environment_smoke : forall n : nat, n = n.
Proof. intros n. reflexivity. Qed.
