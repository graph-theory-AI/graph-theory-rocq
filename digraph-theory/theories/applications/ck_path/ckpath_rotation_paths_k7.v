(** * Numeric Hamilton-path bridges needed by the k=7 certificates *)

From HB Require Import structures.
From mathcomp Require Import all_boot zify.
From Stdlib Require Import Lia.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cert_base ckpath_cert_k7_base ckpath_rotation_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma two_chord_paths12_numeric endpoint : endpoint < 12 ->
  all (numeric_hamilton_pathb 12 endpoint) (two_chord_paths 12 endpoint).
Proof.
move=> hlt.
do 12 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Lemma two_chord_paths13_numeric endpoint : endpoint < 13 ->
  all (numeric_hamilton_pathb 13 endpoint) (two_chord_paths 13 endpoint).
Proof.
move=> hlt.
do 13 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Lemma reverse_three_block_paths13_numeric endpoint : endpoint < 13 ->
  all (numeric_hamilton_pathb 13 endpoint)
      (reverse_three_block_paths 13 endpoint).
Proof.
move=> hlt.
do 13 (case: endpoint hlt => [|endpoint] hlt; first by vm_compute).
by [].
Qed.

Section Bridge.
Variable D : diGraphType.

Theorem two_chord_path12_hamilton endpoint c root path :
  dicycle c -> size c = 12 -> root \in c -> endpoint < 12 ->
  path \in two_chord_paths 12 endpoint ->
  path_chords_realized c root 12 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 12 endpoint path.
  exact: (allP (two_chord_paths12_numeric endlt) path pin).
have hp : numeric_hamilton_path 12 endpoint path :=
  elimT (@numeric_hamilton_pathP 12 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge D 12 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

Theorem two_chord_path13_hamilton endpoint c root path :
  dicycle c -> size c = 13 -> root \in c -> endpoint < 13 ->
  path \in two_chord_paths 13 endpoint ->
  path_chords_realized c root 13 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 13 endpoint path.
  exact: (allP (two_chord_paths13_numeric endlt) path pin).
have hp : numeric_hamilton_path 13 endpoint path :=
  elimT (@numeric_hamilton_pathP 13 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge D 13 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

Theorem reverse_three_block_path13_hamilton endpoint c root path :
  dicycle c -> size c = 13 -> root \in c -> endpoint < 13 ->
  path \in reverse_three_block_paths 13 endpoint ->
  path_chords_realized c root 13 path ->
  exists x : D, exists s : seq D,
    [/\ labelled_numeric_path c root path = x :: s,
        dipath x s,
        [set z in x :: s] = [set z in c]
      & last x s = cycle_label c root endpoint].
Proof.
move=> dc sizec rootc endlt pin chords.
have hpB : numeric_hamilton_pathb 13 endpoint path.
  exact: (allP (reverse_three_block_paths13_numeric endlt) path pin).
have hp : numeric_hamilton_path 13 endpoint path :=
  elimT (@numeric_hamilton_pathP 13 endpoint path) hpB.
exact: (@numeric_hamilton_path_bridge D 13 endpoint c root path
          erefl dc sizec rootc hp chords).
Qed.

End Bridge.
