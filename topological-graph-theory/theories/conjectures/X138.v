(** * Topological.conjectures.X138 -- v2 clustered-colouring on surfaces row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X138 vocabulary ***********************************************)

Definition x138_embeddable_in_connected_orientable_genus
    (orientable_genus : nat) (G : sgraph) : Prop :=
  surface_embeddable orientable_genus G.

(** Historical compatibility name.  This is only the connected orientable
    genus proxy above, not arbitrary embeddability in a fixed surface. *)
Definition x138_embeddable_on_surface
    (orientable_genus : nat) (G : sgraph) : Prop :=
  x138_embeddable_in_connected_orientable_genus orientable_genus G.

Definition x138_clustered_two_colourable (G : sgraph) : Prop :=
  clustered_chromatic_at_most G 2.

Definition x138_clustered_two_colourable_with_clustering
    (c : nat) (G : sgraph) : Prop :=
  clustered_colouring G 2 c.

(** ** X138 statements *****************************************************)

(** Connected-orientable proxy for the Esperet-Joret question: for every
    orientable-genus and maximum-degree bound, connected triangle-free graphs
    within that genus have a uniform clustered two-colouring.  This is not yet
    the full source statement for arbitrary (possibly disconnected) graphs or
    arbitrary surfaces. *)
Definition esperet_joret_surface_triangle_free_clustered_two_colouring_statement : Prop :=
  forall orientable_genus Delta0 : nat,
    exists c : nat,
      forall G : sgraph,
        girth_geq G 4 ->
        Delta G <= Delta0 ->
        x138_embeddable_in_connected_orientable_genus orientable_genus G ->
        x138_clustered_two_colourable_with_clustering c G.
