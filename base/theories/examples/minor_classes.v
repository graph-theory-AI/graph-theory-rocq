(** Public-only clients: no conjecture, area foundation or migration import. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph minor.
From GTBase Require Import graph_classes minor_classes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_class_is_proper_minor_closed :
  proper_minor_closed_class (fun _ : sgraph => False).
Proof. exact: proper_minor_closed_class_empty. Qed.

Example universal_class_is_minor_closed : minor_closed (fun _ : sgraph => True).
Proof. exact: minor_closed_all. Qed.

Example universal_class_excludes_no_minor : ~ excludes_a_minor (fun _ : sgraph => True).
Proof. exact: not_excludes_a_minor_all. Qed.

Example one_vertex_class_excludes_a_minor : excludes_a_minor (fun G : sgraph => #|G| = 1).
Proof. exact: excludes_a_minor_exact_order. Qed.

Example one_vertex_class_is_not_minor_closed : ~ minor_closed (fun G : sgraph => #|G| = 1).
Proof. exact: not_minor_closed_positive_exact_order (isT : 0 < 1). Qed.

Example excluded_witness_does_not_imply_closure :
  exists C : sgraph -> Prop, excludes_a_minor C /\ ~ proper_minor_closed_class C.
Proof.
exists (fun G : sgraph => #|G| = 1); split; first exact: one_vertex_class_excludes_a_minor.
by move/proper_minor_closed_class_closed; exact: one_vertex_class_is_not_minor_closed.
Qed.

Example zero_order_class_excludes_a_minor : excludes_a_minor (fun G : sgraph => #|G| <= 0).
Proof. exact: excludes_a_minor_order_le. Qed.

Example any_forbidden_minor_class (H : sgraph) :
  proper_minor_closed_class (fun G : sgraph => ~ minor G H).
Proof. exact: excluded_minor_class_proper. Qed.

Example minor_closed_implies_strong_hereditary (C : sgraph -> Prop) :
  minor_closed C -> hereditary_class C.
Proof. exact: minor_closed_hereditary. Qed.

Example omission_bridge_under_minor_closure (C : sgraph -> Prop) :
  minor_closed C -> (excludes_a_minor C <-> exists H : sgraph, ~ C H).
Proof. exact: minor_closed_omits_iff. Qed.
