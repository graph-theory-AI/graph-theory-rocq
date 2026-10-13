(** Public-only clients of the list-form polynomial chi-bound [poly_list_chi_bounded]: one coefficient list, chosen
    before the graphs, bounds the chromatic number by its natural Horner evaluation at the clique number. *)
From GTBase Require Import base.
From GTBase Require poly_nat.
From Chromatic.foundations Require Import chi_bounding poly_forms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Non-vacuity: the graphs with at most one vertex, by the constant list [[:: 1]]. *)
Example at_most_one_vertex : poly_list_chi_bounded (fun G : sgraph => #|G| <= 1).
Proof. exact: poly_list_chi_bounded_small. Qed.

(** The empty coefficient list evaluates to [0] at every point, so it bounds only chromatic number zero. *)
Example empty_list_forces_chi0 (G : sgraph) :
  χ([set: G]) <= GTBase.poly_nat.horner_nat [::] (ω([set: G])) -> χ([set: G]) = 0.
Proof. by rewrite GTBase.poly_nat.horner_nat_nil leqn0 => /eqP. Qed.

(** Coefficients are listed lowest degree first: [[:: 0; 1]] is the identity, so a class with [chi <= omega] is
    list-bounded by it. *)
Example perfect_bound (F : sgraph -> Prop) :
  (forall G : sgraph, F G -> χ([set: G]) <= ω([set: G])) -> poly_list_chi_bounded F.
Proof.
move=> H; exists [:: 0; 1] => G FG.
by rewrite !GTBase.poly_nat.horner_nat_cons GTBase.poly_nat.horner_nat_nil muln0 addn0 muln1 add0n; exact: H.
Qed.

(** The list form and the normal form [c * omega ^ d] agree on every class (the [omega = 0] corner included). *)
Example list_and_normal_forms_agree (F : sgraph -> Prop) :
  poly_list_chi_bounded F <-> poly_chi_bounded F.
Proof. exact: poly_chi_bounded_x3E. Qed.

(** Teeth: chromatic number unbounded at clique number at most [k] defeats every coefficient list. *)
Example unbounded_at_bounded_clique_number (F : sgraph -> Prop) (k : nat) :
  (forall n : nat, exists G : sgraph, [/\ F G, ω([set: G]) <= k & n < χ([set: G])]) ->
  ~ poly_list_chi_bounded F.
Proof. exact: not_poly_list_chi_bounded_of_unbounded. Qed.

(** Heredity: a subclass of a list-bounded class is list-bounded by the same list. *)
Example subclass (F F' : sgraph -> Prop) :
  (forall G, F G -> F' G) -> poly_list_chi_bounded F' -> poly_list_chi_bounded F.
Proof. exact: poly_list_chi_bounded_sub. Qed.
