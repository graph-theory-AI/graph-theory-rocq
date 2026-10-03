(** Public-only clients of the weak branch-path contract. These examples do
    not assert induced-subdivision containment. *)
From GTBase Require Import base.
From Chromatic.foundations Require Import branch_paths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_pattern_and_host : branch_paths_at_least 'K_0 'K_0 100.
Proof. exact: branch_paths_empty_pattern. Qed.

Example nonempty_pattern_empty_host (ell : nat) :
  ~ branch_paths_at_least 'K_0 'K_1 ell.
Proof. exact: (@not_branch_paths_empty_host 'K_1 ord0 ell). Qed.

Definition isolated_pair : sgraph :=
  @SGraph 'I_2 preliminaries.rel0 preliminaries.rel0_sym preliminaries.rel0_irrefl.

Example edgeless_pattern_any_bound (ell : nat) :
  branch_paths_at_least 'K_2 isolated_pair ell.
Proof.
have noedges : forall x y : isolated_pair, ~~ (x -- y) by move=> x y.
apply/(@branch_paths_edgelessE 'K_2 isolated_pair ell noedges).
by exists id; exact: inj_id.
Qed.

Example lower_bound_can_decrease (G H : sgraph) (ell : nat) :
  branch_paths_at_least G H ell.+1 -> branch_paths_at_least G H ell.
Proof. exact: branch_paths_at_leastW (leqnSn ell). Qed.

Example zero_bound_view (G H : sgraph) :
  branch_paths_at_least G H 0 <->
  exists br : H -> G, injective br /\
    forall x y : H, x -- y -> exists p : seq G,
      [/\ path (--) (br x) p, last (br x) p = br y, uniq (br x :: p) &
          forall z : G, z \in p -> z != br y -> forall u : H, z != br u].
Proof. exact: branch_paths_zeroE. Qed.

Example singleton_identity : branch_paths_at_least 'K_1 'K_1 1.
Proof. exact: branch_paths_refl. Qed.

Example edge_identity : branch_paths_at_least 'K_2 'K_2 1.
Proof. exact: branch_paths_refl. Qed.

(** A four-cycle pattern on the same four branch vertices in a complete host.
    The host has diagonals absent from the pattern; the weak contract allows it. *)
Definition square_rel (x y : 'I_4) : bool :=
  (x != y) && (odd x != odd y).
Lemma square_sym : symmetric square_rel.
Proof. by move=> x y; rewrite /square_rel eq_sym (eq_sym (odd x)). Qed.
Lemma square_irrefl : irreflexive square_rel.
Proof. by move=> x; rewrite /square_rel eqxx. Qed.
Definition square := SGraph square_sym square_irrefl.

Example square_in_complete_host : branch_paths_at_least 'K_4 square 1.
Proof.
apply: (@branch_paths_of_embedding 'K_4 square id); first exact: inj_id.
by move=> x y /andP[xy _].
Qed.

Example host_has_extra_diagonal :
  (@Ordinal 4 0 isT : 'K_4) -- (@Ordinal 4 2 isT : 'K_4) /\
  ~~ ((@Ordinal 4 0 isT : square) -- (@Ordinal 4 2 isT : square)).
Proof. by vm_compute. Qed.
