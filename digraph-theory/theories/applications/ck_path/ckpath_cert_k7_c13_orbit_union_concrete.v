(** * Checked finite refutations for the three k=7 C13 orbit unions *)

From Digraph Require Import ckpath_cnf ckpath_cert_k7_c13_orbit_union
  ckpath_cert_k7_c13_orbit_union3_base_bridge
  ckpath_cert_k7_c13_orbit_union3_micro_final
  ckpath_cert_k7_c13_orbit_union4_base_bridge
  ckpath_cert_k7_c13_orbit_union4_micro_final
  ckpath_cert_k7_c13_orbit_union5_base_bridge
  ckpath_cert_k7_c13_orbit_union5_micro_final.

Theorem c13_k7_orbit_union3_unsatisfiable :
  forall rho, ~ satisfies_cnf rho (c13_k7_orbit_union_base 3).
Proof.
intros rho Hsemantic.
apply (c13_k7_orbit_union3_micro_base_unsatisfiable rho).
rewrite c13_k7_orbit_union3_explicit_base_eq.
exact Hsemantic.
Qed.

Theorem c13_k7_orbit_union4_unsatisfiable :
  forall rho, ~ satisfies_cnf rho (c13_k7_orbit_union_base 4).
Proof.
intros rho Hsemantic.
apply (c13_k7_orbit_union4_micro_base_unsatisfiable rho).
rewrite c13_k7_orbit_union4_explicit_base_eq.
exact Hsemantic.
Qed.

Theorem c13_k7_orbit_union5_unsatisfiable :
  forall rho, ~ satisfies_cnf rho (c13_k7_orbit_union_base 5).
Proof.
intros rho Hsemantic.
apply (c13_k7_orbit_union5_micro_base_unsatisfiable rho).
rewrite c13_k7_orbit_union5_explicit_base_eq.
exact Hsemantic.
Qed.
