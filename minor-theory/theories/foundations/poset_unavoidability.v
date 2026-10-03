(** * Graphs unavoidable as minors of cover graphs of finite posets

    [poset_unavoidable H] holds when ONE natural threshold [d], chosen before all
    posets, is such that every finite poset [P] whose dimension is NOT at most [d]
    has [H] as a minor of its cover graph: [minor (poset_cover_graph P) H], host
    before pattern.  The poset vocabulary is GTBase.posets unchanged: a realizer may
    be the empty list, so a one-point poset has dimension at most 0, and [d = 0],
    empty carriers and empty graphs are all allowed.  Minors are upstream
    [GraphTheory.core.minor.minor].

    This is not an induced-minor, subdivision, exact-order or eventual-cardinality
    predicate, and it is not the exact-order tournament unavoidability of
    [Digraph.conjectures.unvd.unavoidable].  No planarity or width bound on [H] is
    part of the definition. *)
From GTBase Require Import base minor_models.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition poset_unavoidable (H : sgraph) : Prop :=
  exists d : nat,
    forall P : finite_poset,
      ~ poset_dimension_at_most P d -> minor (poset_cover_graph P) H.

(** Dimension-at-most is monotone in the bound. *)
Lemma poset_dimension_at_mostW (P : finite_poset) (d e : nat) :
  d <= e -> poset_dimension_at_most P d -> poset_dimension_at_most P e.
Proof. by move=> de [ls [sz r]]; exists ls; split=> //; exact: leq_trans sz de. Qed.

(** Introduction and elimination with one supplied threshold. *)
Lemma poset_unavoidableI (H : sgraph) (d : nat) :
  (forall P : finite_poset, ~ poset_dimension_at_most P d -> minor (poset_cover_graph P) H) ->
  poset_unavoidable H.
Proof. by exists d. Qed.

(** A working threshold can be raised. *)
Lemma poset_unavoidable_threshold (H : sgraph) (d e : nat) :
  d <= e ->
  (forall P : finite_poset, ~ poset_dimension_at_most P d -> minor (poset_cover_graph P) H) ->
  forall P : finite_poset, ~ poset_dimension_at_most P e -> minor (poset_cover_graph P) H.
Proof.
move=> de hd P ne; apply: hd => dP; apply: ne.
exact: poset_dimension_at_mostW de dP.
Qed.

Lemma poset_unavoidable_large (H : sgraph) :
  poset_unavoidable H ->
  exists d : nat, forall e : nat, d <= e ->
    forall P : finite_poset, ~ poset_dimension_at_most P e -> minor (poset_cover_graph P) H.
Proof. by move=> [d hd]; exists d => e de; exact: poset_unavoidable_threshold de hd. Qed.

(** Minors of unavoidable graphs are unavoidable, with the same threshold. *)
Lemma poset_unavoidable_minor (H K : sgraph) :
  poset_unavoidable H -> minor H K -> poset_unavoidable K.
Proof.
move=> [d hd] hk; exists d => P nP.
exact: (minor_trans (hd P nP) hk).
Qed.

(** The empty graph is unavoidable, already with threshold 0. *)
Lemma poset_unavoidable_K0 : poset_unavoidable 'K_0.
Proof.
exists 0 => P _; apply/minor_rmap_existsE.
by exists (fun _ => set0); exact: minor_rmap_empty_pattern.
Qed.
