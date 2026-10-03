(** C16: exact X128/X139 ambient-radius snapshots. The A7 count snapshots
    remain verbatim. Each new Original combines their frozen public edge count
    with these frozen radius/model chains; no internal-radius repair is made. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From GTBase Require migration.edge_count.
From GTMisc.foundations Require Import ambient_shallow_minors.
From GTMisc.conjectures Require Import X128 X139.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module FG := GTBase.migration.edge_count.

Module X128Legacy.

Definition x128_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition x128_shallow_minor_model (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, X128Legacy.x128_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x128_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    X128Legacy.x128_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, X128Legacy.x128_grad_at_most G r (x128_poly_eval p r).

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        X128Legacy.x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).

End X128Legacy.

Module X128Original.

Definition x128_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    X128Legacy.x128_shallow_minor_model G H r ->
    2 * FG.Legacy.fg_edge_count H <= d * #|H|.

Definition x128_expansion_bounded (G : sgraph) (p : seq nat) : Prop :=
  forall r : nat, X128Original.x128_grad_at_most G r (x128_poly_eval p r).

Definition dvorak_cheap_balanced_separator_bounded_expansion_statement : Prop :=
  forall p : seq nat,
    exists q : nat -> nat,
      forall (G : sgraph) (rho : G -> nat) (t : nat),
        1 <= t ->
        X128Original.x128_expansion_bounded G p ->
        x128_cheap_bal_sep rho t (q t).

End X128Original.

Module X139Legacy.

Definition x139_radius_at_most (G : sgraph) (S : {set G}) (r : nat) : Prop :=
  exists c : G,
    c \in S /\ forall x : G, x \in S -> @graph_dist G c x <= r.

Definition x139_shallow_minor_model (G H : sgraph) (r : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h : H, X139Legacy.x139_radius_at_most (branch h) r) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x139_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    X139Legacy.x139_shallow_minor_model G H r ->
    2 * fg_edge_count H <= d * #|H|.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> X139Legacy.x139_grad_at_most G r (x139_poly_eval p r).

Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    X139Legacy.x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (x139_poly_eval f r).

End X139Legacy.

Module X139Original.

Definition x139_grad_at_most (G : sgraph) (r d : nat) : Prop :=
  forall H : sgraph,
    X139Legacy.x139_shallow_minor_model G H r ->
    2 * FG.Legacy.fg_edge_count H <= d * #|H|.

Definition x139_polynomial_expansion_class (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall (r : nat) (G : sgraph), C G -> X139Original.x139_grad_at_most G r (x139_poly_eval p r).

Definition esperet_raymond_polynomial_expansion_scol_statement : Prop :=
  forall C : sgraph -> Prop,
    X139Original.x139_polynomial_expansion_class C ->
    exists f : seq nat,
      forall (r : nat) (G : sgraph),
        C G -> x139_scol_at_most G r (x139_poly_eval f r).

End X139Original.

Lemma x128_radius_at_most_compat (G : sgraph) (S : {set G}) (r : nat) :
  @X128Legacy.x128_radius_at_most G S r <-> @x128_radius_at_most G S r.
Proof. reflexivity. Qed.

Lemma x128_shallow_minor_model_compat (G H : sgraph) (r : nat) :
  @X128Legacy.x128_shallow_minor_model G H r <-> @x128_shallow_minor_model G H r.
Proof. exact: (iff_sym (ambient_shallow_minor_nestedE G H r)). Qed.

Lemma x128_grad_at_most_compat (G : sgraph) (r d : nat) :
  @X128Legacy.x128_grad_at_most G r d <-> @x128_grad_at_most G r d.
Proof. rewrite /X128Legacy.x128_grad_at_most /x128_grad_at_most; setoid_rewrite x128_shallow_minor_model_compat; reflexivity. Qed.

Lemma x128_expansion_bounded_compat (G : sgraph) (p : seq nat) :
  @X128Legacy.x128_expansion_bounded G p <-> @x128_expansion_bounded G p.
Proof. rewrite /X128Legacy.x128_expansion_bounded /x128_expansion_bounded; setoid_rewrite x128_grad_at_most_compat; reflexivity. Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_compat : X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement <-> dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof. rewrite /X128Legacy.dvorak_cheap_balanced_separator_bounded_expansion_statement /dvorak_cheap_balanced_separator_bounded_expansion_statement; setoid_rewrite x128_expansion_bounded_compat; reflexivity. Qed.

Lemma x128_grad_at_most_original_compat (G : sgraph) (r d : nat) :
  @X128Original.x128_grad_at_most G r d <-> @x128_grad_at_most G r d.
Proof. rewrite /X128Original.x128_grad_at_most /x128_grad_at_most; setoid_rewrite x128_shallow_minor_model_compat; setoid_rewrite FG.fg_edge_count_compat; reflexivity. Qed.

Lemma x128_expansion_bounded_original_compat (G : sgraph) (p : seq nat) :
  @X128Original.x128_expansion_bounded G p <-> @x128_expansion_bounded G p.
Proof. rewrite /X128Original.x128_expansion_bounded /x128_expansion_bounded; setoid_rewrite x128_grad_at_most_original_compat; reflexivity. Qed.

Lemma dvorak_cheap_balanced_separator_bounded_expansion_statement_original_compat : X128Original.dvorak_cheap_balanced_separator_bounded_expansion_statement <-> dvorak_cheap_balanced_separator_bounded_expansion_statement.
Proof. rewrite /X128Original.dvorak_cheap_balanced_separator_bounded_expansion_statement /dvorak_cheap_balanced_separator_bounded_expansion_statement; setoid_rewrite x128_expansion_bounded_original_compat; reflexivity. Qed.

Lemma x139_radius_at_most_compat (G : sgraph) (S : {set G}) (r : nat) :
  @X139Legacy.x139_radius_at_most G S r <-> @x139_radius_at_most G S r.
Proof. reflexivity. Qed.

Lemma x139_shallow_minor_model_compat (G H : sgraph) (r : nat) :
  @X139Legacy.x139_shallow_minor_model G H r <-> @x139_shallow_minor_model G H r.
Proof. exact: (iff_sym (ambient_shallow_minor_nestedE G H r)). Qed.

Lemma x139_grad_at_most_compat (G : sgraph) (r d : nat) :
  @X139Legacy.x139_grad_at_most G r d <-> @x139_grad_at_most G r d.
Proof. rewrite /X139Legacy.x139_grad_at_most /x139_grad_at_most; setoid_rewrite x139_shallow_minor_model_compat; reflexivity. Qed.

Lemma x139_polynomial_expansion_class_compat (C : sgraph -> Prop) :
  @X139Legacy.x139_polynomial_expansion_class C <-> @x139_polynomial_expansion_class C.
Proof. rewrite /X139Legacy.x139_polynomial_expansion_class /x139_polynomial_expansion_class; setoid_rewrite x139_grad_at_most_compat; reflexivity. Qed.

Lemma esperet_raymond_polynomial_expansion_scol_statement_compat : X139Legacy.esperet_raymond_polynomial_expansion_scol_statement <-> esperet_raymond_polynomial_expansion_scol_statement.
Proof. rewrite /X139Legacy.esperet_raymond_polynomial_expansion_scol_statement /esperet_raymond_polynomial_expansion_scol_statement; setoid_rewrite x139_polynomial_expansion_class_compat; reflexivity. Qed.

Lemma x139_grad_at_most_original_compat (G : sgraph) (r d : nat) :
  @X139Original.x139_grad_at_most G r d <-> @x139_grad_at_most G r d.
Proof. rewrite /X139Original.x139_grad_at_most /x139_grad_at_most; setoid_rewrite x139_shallow_minor_model_compat; setoid_rewrite FG.fg_edge_count_compat; reflexivity. Qed.

Lemma x139_polynomial_expansion_class_original_compat (C : sgraph -> Prop) :
  @X139Original.x139_polynomial_expansion_class C <-> @x139_polynomial_expansion_class C.
Proof. rewrite /X139Original.x139_polynomial_expansion_class /x139_polynomial_expansion_class; setoid_rewrite x139_grad_at_most_original_compat; reflexivity. Qed.

Lemma esperet_raymond_polynomial_expansion_scol_statement_original_compat : X139Original.esperet_raymond_polynomial_expansion_scol_statement <-> esperet_raymond_polynomial_expansion_scol_statement.
Proof. rewrite /X139Original.esperet_raymond_polynomial_expansion_scol_statement /esperet_raymond_polynomial_expansion_scol_statement; setoid_rewrite x139_polynomial_expansion_class_original_compat; reflexivity. Qed.
