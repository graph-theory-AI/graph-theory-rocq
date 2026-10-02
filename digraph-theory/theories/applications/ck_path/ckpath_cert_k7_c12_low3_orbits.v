(** * Complete certificate table for the k=7 C12 low-three branch *)

From Stdlib Require Import List Bool.
From Digraph Require Import ckpath_cnf ckpath_k7_orbits
  ckpath_cert_k7_c12_low3_reduction
  ckpath_cert_k7_c12_low3_mask00_final
  ckpath_cert_k7_c12_low3_mask01_final
  ckpath_cert_k7_c12_low3_mask02_final
  ckpath_cert_k7_c12_low3_mask03_final
  ckpath_cert_k7_c12_low3_mask04_final
  ckpath_cert_k7_c12_low3_mask05_final
  ckpath_cert_k7_c12_low3_mask06_final
  ckpath_cert_k7_c12_low3_mask07_final
  ckpath_cert_k7_c12_low3_mask08_final
  ckpath_cert_k7_c12_low3_mask09_final
  ckpath_cert_k7_c12_low3_mask10_final
  ckpath_cert_k7_c12_low3_mask11_final
  ckpath_cert_k7_c12_low3_mask12_final
  ckpath_cert_k7_c12_low3_mask13_final
  ckpath_cert_k7_c12_low3_mask14_final
  ckpath_cert_k7_c12_low3_mask15_final
  ckpath_cert_k7_c12_low3_mask16_final
  ckpath_cert_k7_c12_low3_mask17_final
  ckpath_cert_k7_c12_low3_mask18_final.
Import ListNotations.

(** Keep this executable table in the exact order produced by
    [orbit_representatives 12 3]. *)
Definition c12_k7_low3_masks : list (list bool) :=
  [[true; false; false; false; true; false; false; false; true; false; false; false];
   [true; false; false; true; false; false; false; true; false; false; false; false];
   [true; false; false; true; false; false; false; false; true; false; false; false];
   [true; false; true; false; false; false; false; true; false; false; false; false];
   [true; true; false; false; false; false; true; false; false; false; false; false];
   [true; false; true; false; false; false; true; false; false; false; false; false];
   [true; false; false; true; false; false; true; false; false; false; false; false];
   [true; false; true; false; false; false; false; false; true; false; false; false];
   [true; true; false; false; false; false; false; true; false; false; false; false];
   [true; true; false; false; false; true; false; false; false; false; false; false];
   [true; false; true; false; false; true; false; false; false; false; false; false];
   [true; false; true; false; false; false; false; false; false; true; false; false];
   [true; true; false; false; false; false; false; false; true; false; false; false];
   [true; true; false; false; true; false; false; false; false; false; false; false];
   [true; false; true; false; true; false; false; false; false; false; false; false];
   [true; true; false; false; false; false; false; false; false; true; false; false];
   [true; true; false; true; false; false; false; false; false; false; false; false];
   [true; true; false; false; false; false; false; false; false; false; true; false];
   [true; true; true; false; false; false; false; false; false; false; false; false]].

Lemma c12_k7_low3_masks_exact :
  c12_k7_low3_masks = orbit_representatives 12 3.
Proof. vm_compute. reflexivity. Qed.

Theorem c12_k7_low3_orbit_instance_unsatisfiable mask :
  List.In mask (orbit_representatives 12 3) ->
  forall rho, ~ satisfies_cnf rho (c12_k7_low3_instance mask).
Proof.
intro Hmask.
rewrite <- c12_k7_low3_masks_exact in Hmask.
unfold c12_k7_low3_masks in Hmask.
simpl in Hmask.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask00_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask01_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask02_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask03_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask04_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask05_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask06_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask07_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask08_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask09_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask10_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask11_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask12_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask13_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask14_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask15_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask16_base_unsatisfiable.
destruct Hmask as [<- | Hmask].
- exact c12_k7_low3_mask17_base_unsatisfiable.
destruct Hmask as [<- | []].
exact c12_k7_low3_mask18_base_unsatisfiable.
Qed.
