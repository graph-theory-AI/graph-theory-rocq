(** Public-only clients; no conjecture, area foundation or migration import. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries bij digraph sgraph.
From GTBase Require Import graph_classes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example empty_class_is_hereditary : hereditary_class (fun _ : sgraph => False).
Proof. exact: hereditary_class_empty. Qed.

Example universal_class_is_hereditary : hereditary_class (fun _ : sgraph => True).
Proof. exact: hereditary_class_all. Qed.

Example zero_order_class_is_hereditary : hereditary_class (fun G : sgraph => #|G| <= 0).
Proof. exact: hereditary_class_order_le. Qed.

Example bounded_order_class_is_hereditary n : hereditary_class (fun G : sgraph => #|G| <= n).
Proof. exact: hereditary_class_order_le. Qed.

Example two_vertices_is_iso_closed : iso_closed (fun G : sgraph => #|G| = 2).
Proof.
move=> G H G2 iso; have cardGH := bij_card_eq (bij_bijective (diso_v iso)).
by rewrite -cardGH.
Qed.

Example two_vertices_is_not_induced_closed :
  ~ induced_closed (fun G : sgraph => #|G| = 2).
Proof. exact: not_induced_closed_positive_exact_order (isT : 0 < 2). Qed.

Example two_vertices_is_not_hereditary :
  ~ hereditary_class (fun G : sgraph => #|G| = 2).
Proof. by move/hereditary_class_induced; exact: two_vertices_is_not_induced_closed. Qed.

Example intersection (C D : sgraph -> Prop) :
  hereditary_class C -> hereditary_class D -> hereditary_class (fun G => C G /\ D G).
Proof. exact: hereditary_class_inter. Qed.

Example union (C D : sgraph -> Prop) :
  hereditary_class C -> hereditary_class D -> hereditary_class (fun G => C G \/ D G).
Proof. exact: hereditary_class_union. Qed.

Example induced_only_empty_class : induced_closed (fun _ : sgraph => False).
Proof. exact: induced_closed_empty. Qed.

Example supplied_isomorphism (C : sgraph -> Prop) (G H : sgraph) :
  iso_closed C -> diso G H -> (C G <-> C H).
Proof. exact: iso_closed_transport. Qed.
