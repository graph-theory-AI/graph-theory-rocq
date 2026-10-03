(** * Uniform ordinary chromatic bounds for graph classes

    One arbitrary [f : nat -> nat] is chosen before ALL members of a class.
    [chi_bounded_via U F] measures the ordinary chi and omega of the supplied
    simple graph [U x]. The indexing type need not be finite or inhabited;
    each graph itself is finite. Neither f nor F is required to be monotone,
    hereditary, isomorphism closed, or polynomially bounded.

    [chi_bounded_class] specializes to simple graphs themselves. Other graph
    representations keep their underlying-map and membership guards explicit.
    In particular a nonempty-member adapter uses [F x /\ 0 < #|U x|]. This is
    not dichromatic boundedness or the stronger polynomial/constant contract.
    Registry: meta/library_primitives/chi-bounded.json (C9). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition chi_bounded_via (A : Type) (U : A -> sgraph) (F : A -> Prop) : Prop :=
  exists f : nat -> nat,
    forall x : A, F x -> χ([set: U x]) <= f (ω([set: U x])).

Definition chi_bounded_class (F : sgraph -> Prop) : Prop :=
  chi_bounded_via (fun G : sgraph => G) F.

Lemma chi_bounded_via_empty (A : Type) (U : A -> sgraph) :
  chi_bounded_via U (fun _ => False).
Proof. by exists (fun _ => 0) => x []. Qed.

Lemma chi_bounded_via_sub (A : Type) (U : A -> sgraph) (F H : A -> Prop) :
  (forall x, F x -> H x) -> chi_bounded_via U H -> chi_bounded_via U F.
Proof. by move=> sub [f hf]; exists f => x Fx; apply: hf; exact: sub Fx. Qed.

Lemma chi_bounded_via_ext (A : Type) (U : A -> sgraph) (F H : A -> Prop) :
  (forall x, F x <-> H x) -> (chi_bounded_via U F <-> chi_bounded_via U H).
Proof.
move=> eqFH; split; apply: chi_bounded_via_sub => x hx.
- exact: (eqFH x).2 hx.
- exact: (eqFH x).1 hx.
Qed.

Lemma chi_bounded_via_union (A : Type) (U : A -> sgraph) (F H : A -> Prop) :
  chi_bounded_via U F -> chi_bounded_via U H ->
  chi_bounded_via U (fun x => F x \/ H x).
Proof.
move=> [f hf] [h hh]; exists (fun n => f n + h n) => x [Fx|Hx].
- exact: leq_trans (hf x Fx) (leq_addr _ _).
- exact: leq_trans (hh x Hx) (leq_addl _ _).
Qed.

Lemma chi_bounded_via_bounded_order (A : Type) (U : A -> sgraph) n :
  chi_bounded_via U (fun x => #|U x| <= n).
Proof.
exists (fun _ => n) => x hn; apply: leq_trans (leq_chi _) _.
by rewrite cardsT.
Qed.

Lemma chi_bounded_via_image (A B : Type) (U : B -> sgraph) (h : A -> B)
    (F : A -> Prop) :
  chi_bounded_via (fun x => U (h x)) F <->
  chi_bounded_via U (fun y => exists x, F x /\ h x = y).
Proof.
split=> -[f hf]; exists f.
- by move=> y [x [Fx <-]]; exact: hf x Fx.
- move=> x Fx; apply: hf; by exists x.
Qed.

(** A precise obstruction, conditional on an actual unbounded family at one
    fixed clique number; this lemma does not assert such a family exists. *)
Lemma not_chi_bounded_via_of_unbounded_at (A : Type) (U : A -> sgraph)
    (F : A -> Prop) m :
  (forall n, exists x, [/\ F x, ω([set: U x]) = m & n < χ([set: U x])]) ->
  ~ chi_bounded_via U F.
Proof.
move=> unbounded [f hf]; have [x [Fx wx big]] := unbounded (f m).
have := hf x Fx; by rewrite wx leqNgt big.
Qed.

Lemma chi_bounded_class_empty : chi_bounded_class (fun _ : sgraph => False).
Proof. exact: chi_bounded_via_empty. Qed.

Lemma chi_bounded_class_sub (F H : sgraph -> Prop) :
  (forall G, F G -> H G) -> chi_bounded_class H -> chi_bounded_class F.
Proof. exact: chi_bounded_via_sub. Qed.

Lemma chi_bounded_class_ext (F H : sgraph -> Prop) :
  (forall G, F G <-> H G) -> (chi_bounded_class F <-> chi_bounded_class H).
Proof. exact: chi_bounded_via_ext. Qed.

Lemma chi_bounded_class_union (F H : sgraph -> Prop) :
  chi_bounded_class F -> chi_bounded_class H ->
  chi_bounded_class (fun G => F G \/ H G).
Proof. exact: chi_bounded_via_union. Qed.

Lemma chi_bounded_class_bounded_order n :
  chi_bounded_class (fun G : sgraph => #|G| <= n).
Proof. exact: chi_bounded_via_bounded_order. Qed.

(** The empty graph does not force a value of f at zero: its chromatic number
    is already zero. Membership guards remain explicit at each client. *)
Lemma empty_graph_chi_bound (G : sgraph) (f : nat -> nat) :
  #|G| = 0 -> χ([set: G]) <= f (ω([set: G])).
Proof.
move=> G0; have chi0G : χ([set: G]) = 0.
  by apply/eqP; rewrite -leqn0 -G0 -cardsT; exact: leq_chi.
by rewrite chi0G.
Qed.
