(** * The checked Cheng--Keevash directed-path theorem at out-degree seven *)

From Stdlib Require Import List.
From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath
  ckpath_cnf ckpath_k7_orbits ckpath_cert_k7_c12_low3_reduction
  ckpath_k7
  ckpath_cert_k7_c12_cover4_micro_final
  ckpath_cert_k7_c12_low3_orbits
  ckpath_cert_k7_c13_orbit_union_concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Adapt the checked table of nineteen orbit representatives to the argument
    order used by the finite-refutation theorem. *)
Lemma c12_k7_low3_all_unsatisfiable :
  forall mask rho,
    List.In mask (orbit_representatives 12 3) ->
    satisfies_cnf rho (c12_k7_low3_instance mask) -> False.
Proof.
move=> mask rho Hmask.
exact: (@c12_k7_low3_orbit_instance_unsatisfiable mask Hmask rho).
Qed.

(** Conjecture 1 at minimum out-degree seven. *)
Theorem ck_conj1_delta7 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 7 <= outdeg v) -> 14 <= ell D.
Proof.
exact: (@ck_conj1_delta7_from_finite_refutations
          c12_k7_cover4_micro_base_unsatisfiable
          c12_k7_low3_all_unsatisfiable
          c13_k7_orbit_union3_unsatisfiable
          c13_k7_orbit_union4_unsatisfiable
          c13_k7_orbit_union5_unsatisfiable D).
Qed.

(** Explicit simple directed path with fourteen arcs. *)
Corollary ck_conj1_delta7_path (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 7 <= outdeg v) ->
  exists x : D, exists s : seq D, dipath x s /\ size s = 14.
Proof.
exact: (@ck_conj1_delta7_path_from_finite_refutations
          c12_k7_cover4_micro_base_unsatisfiable
          c12_k7_low3_all_unsatisfiable
          c13_k7_orbit_union3_unsatisfiable
          c13_k7_orbit_union4_unsatisfiable
          c13_k7_orbit_union5_unsatisfiable D).
Qed.

(** Conjecture-1-shaped alias. *)
Corollary ck_conj1_at_7 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 7 <= outdeg v) -> 2 * 7 <= ell D.
Proof.
exact: (@ck_conj1_at_7_from_finite_refutations
          c12_k7_cover4_micro_base_unsatisfiable
          c12_k7_low3_all_unsatisfiable
          c13_k7_orbit_union3_unsatisfiable
          c13_k7_orbit_union4_unsatisfiable
          c13_k7_orbit_union5_unsatisfiable D).
Qed.
