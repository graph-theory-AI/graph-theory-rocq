(** C18: X220 internal-radius shallow minors, frozen at
    311fdcb89dc12a78c62cb0ee6d2477896cbce9a7.  The ball keeps its supplied
    centre without a membership clause, its vacuity on the empty set and its
    exact walk-length bound inside the set; the model keeps its supplied branch
    and centre maps.  The polynomial-expansion chain and the whole row keep one
    polynomial for the whole class and every depth, and one twin-width bound d
    for the whole class.  No ambient-radius or graph_dist reading is introduced. *)
From GTBase Require Import base.
From Minor.foundations Require Import shallow_minors.
From Minor.conjectures Require Import X220.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x220_ball_in (G : sgraph) (B : {set G}) (c : G) (r : nat) : Prop :=
  forall v : G, v \in B ->
    exists p : seq G,
      [/\ path (--) c p, last c p = v, size p <= r & all (mem B) (c :: p)].

Definition x220_shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists (B : H -> {set G}) (ctr : H -> G),
    [/\ forall x : H, ctr x \in B x,
        forall x : H, Legacy.x220_ball_in (B x) (ctr x) r,
        forall x y : H, x != y -> [disjoint B x & B y] &
        forall x y : H, x -- y -> exists u v : G, [/\ u \in B x, v \in B y & u -- v]].

Definition x220_polynomial_expansion (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G ->
      forall (r : nat) (H : sgraph),
        Legacy.x220_shallow_minor G H r -> #|E(H)| <= x220_poly_eval p r * #|H|.

Definition polynomial_expansion_bounded_twin_width_statement : Prop :=
  forall C : sgraph -> Prop,
    Legacy.x220_polynomial_expansion C ->
    exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

End Legacy.

Lemma x220_ball_in_compat (G : sgraph) (B : {set G}) (c : G) (r : nat) :
  @Legacy.x220_ball_in G B c r <-> @x220_ball_in G B c r.
Proof. exact: iff_refl. Qed.

Lemma x220_shallow_minor_compat (G H : sgraph) (r : nat) :
  Legacy.x220_shallow_minor G H r <-> x220_shallow_minor G H r.
Proof. exact: (iff_sym (internal_shallow_minorE G H r)). Qed.

Lemma x220_polynomial_expansion_compat (C : sgraph -> Prop) :
  Legacy.x220_polynomial_expansion C <-> x220_polynomial_expansion C.
Proof.
split=> -[p bound]; exists p => G CG r H model.
- exact: bound G CG r H (proj2 (x220_shallow_minor_compat G H r) model).
- exact: bound G CG r H (proj1 (x220_shallow_minor_compat G H r) model).
Qed.

Lemma polynomial_expansion_bounded_twin_width_statement_compat :
  Legacy.polynomial_expansion_bounded_twin_width_statement <->
  polynomial_expansion_bounded_twin_width_statement.
Proof.
split=> statement C expansion.
- exact: statement C (proj2 (x220_polynomial_expansion_compat C) expansion).
- exact: statement C (proj1 (x220_polynomial_expansion_compat C) expansion).
Qed.
