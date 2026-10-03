(** * Extremal.migration.path_tree — frozen path tree of X105 (library migration B9)

    Batch B, family [path-tree] (meta/library_primitives/path-tree.json).  [Legacy]
    freezes X105's [x105_path_tree] verbatim as it stood at the B9 baseline e377dcb:
    a tree of maximum degree at most two.  The live helper now unfolds to
    [GTBase.path_trees.path_tree T], whose body is that conjunction, so the
    certificates are kernel-checked conversions.  [X105Legacy] freezes the tree
    inducibility row, which uses the helper negatively ([~ x105_path_tree T]) next
    to the unchanged [is_tree] hypothesis, the star exclusion, the eventual density
    bound and the [0 < eps_num < eps_den] guard.  No earlier migration froze this
    row.  Hashes and substitutions: meta/migration_reports/path_tree.md. *)

From GTBase Require Import base path_trees.
From Extremal.conjectures Require Import X105.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x105_path_tree (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

End Legacy.

Module X105Legacy.

Definition non_star_non_path_tree_inducibility_bounded_away_statement : Prop :=
  exists eps_num eps_den : nat,
    [/\ 0 < eps_num, eps_num < eps_den
      & forall T : sgraph,
          is_tree [set: T] ->
          ~ x105_star_tree T ->
          ~ Legacy.x105_path_tree T ->
          exists N : nat,
            forall (G : sgraph) (C : {set {set G}}),
              N <= #|G| ->
              @x105_induced_copy_family T G C ->
              @x105_density_at_most T G C (eps_den - eps_num) eps_den].

End X105Legacy.

(** ** Certificates *)

Lemma x105_path_tree_compat (T : sgraph) : Legacy.x105_path_tree T <-> x105_path_tree T.
Proof. exact: iff_refl. Qed.

Lemma non_star_non_path_tree_inducibility_bounded_away_statement_compat :
  X105Legacy.non_star_non_path_tree_inducibility_bounded_away_statement <->
  non_star_non_path_tree_inducibility_bounded_away_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions x105_path_tree_compat.
Print Assumptions non_star_non_path_tree_inducibility_bounded_away_statement_compat.
