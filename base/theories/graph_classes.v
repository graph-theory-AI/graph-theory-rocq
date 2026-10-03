(** * Closure properties of finite simple graph classes

    Classes are arbitrary [sgraph -> Prop] predicates, including the empty
    class. [iso_closed] uses upstream [diso] witnesses; [induced_closed] closes
    only under the literal induced graph on each vertex subset. The strong
    [hereditary_class] contract explicitly requires BOTH properties.

    No inhabitance, properness or decidability is assumed. In particular,
    induced closure alone must not acquire an isomorphism-closure hypothesis.
    This is separate from GraphTheory.dom.hereditary on Boolean predicates of
    subsets of one fixed finite type. Registry: hereditary-class (C10). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries bij digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

Definition induced_closed (C : sgraph -> Prop) : Prop :=
  forall (G : sgraph) (S : {set G}), C G -> C (induced S).

Definition hereditary_class (C : sgraph -> Prop) : Prop :=
  iso_closed C /\ induced_closed C.

Lemma iso_closed_transport (C : sgraph -> Prop) (G H : sgraph) :
  iso_closed C -> diso G H -> (C G <-> C H).
Proof.
move=> closed iso; split=> member.
- exact: closed G H member iso.
- exact: closed H G member (diso_sym iso).
Qed.

Lemma iso_closed_ext (C D : sgraph -> Prop) :
  (forall G, C G <-> D G) -> (iso_closed C <-> iso_closed D).
Proof.
move=> same; split=> closed G H member iso.
- apply/(same H).1; apply: closed iso; by apply/(same G).2.
- apply/(same H).2; apply: closed iso; by apply/(same G).1.
Qed.

Lemma induced_closed_ext (C D : sgraph -> Prop) :
  (forall G, C G <-> D G) -> (induced_closed C <-> induced_closed D).
Proof.
move=> same; split=> closed G S member.
- apply/(same (induced S)).1; apply: closed; by apply/(same G).2.
- apply/(same (induced S)).2; apply: closed; by apply/(same G).1.
Qed.

Lemma hereditary_class_ext (C D : sgraph -> Prop) :
  (forall G, C G <-> D G) -> (hereditary_class C <-> hereditary_class D).
Proof.
move=> same; split=> -[iso sub]; split.
- by apply/(iso_closed_ext same).
- by apply/(induced_closed_ext same).
- by apply/(iso_closed_ext same).
- by apply/(induced_closed_ext same).
Qed.

Lemma hereditary_class_iso (C : sgraph -> Prop) :
  hereditary_class C -> iso_closed C.
Proof. by case. Qed.

Lemma hereditary_class_induced (C : sgraph -> Prop) :
  hereditary_class C -> induced_closed C.
Proof. by case. Qed.

Lemma hereditary_class_intro (C : sgraph -> Prop) :
  iso_closed C -> induced_closed C -> hereditary_class C.
Proof. by split. Qed.

Lemma induced_closed_empty : induced_closed (fun _ : sgraph => False).
Proof. by move=> G S []. Qed.

Lemma hereditary_class_empty : hereditary_class (fun _ : sgraph => False).
Proof. split; [by move=> G H []|exact: induced_closed_empty]. Qed.

Lemma hereditary_class_all : hereditary_class (fun _ : sgraph => True).
Proof. by split. Qed.

Lemma hereditary_class_inter (C D : sgraph -> Prop) :
  hereditary_class C -> hereditary_class D ->
  hereditary_class (fun G => C G /\ D G).
Proof.
move=> [isoC subC] [isoD subD]; split.
- move=> G H [CG DG] iso; split; [exact: isoC G H CG iso|exact: isoD G H DG iso].
- move=> G S [CG DG]; split; [exact: subC G S CG|exact: subD G S DG].
Qed.

Lemma hereditary_class_union (C D : sgraph -> Prop) :
  hereditary_class C -> hereditary_class D ->
  hereditary_class (fun G => C G \/ D G).
Proof.
move=> [isoC subC] [isoD subD]; split.
- move=> G H [CG|DG] iso; [left; exact: isoC G H CG iso|right; exact: isoD G H DG iso].
- move=> G S [CG|DG]; [left; exact: subC G S CG|right; exact: subD G S DG].
Qed.

Lemma hereditary_class_order_le n :
  hereditary_class (fun G : sgraph => #|G| <= n).
Proof.
split=> [G H|G S].
- move=> Gn iso; have cardGH := bij_card_eq (bij_bijective (diso_v iso)).
  by rewrite -cardGH.
- move=> Gn; have cardS : #|induced S| = #|S|.
    by rewrite card_sig; apply: eq_card => x; rewrite !inE.
  rewrite cardS; exact: leq_trans (max_card S) Gn.
Qed.

(** A real induced-closure obstruction, including the empty-subset corner. *)
Lemma not_induced_closed_positive_exact_order n :
  0 < n -> ~ induced_closed (fun G : sgraph => #|G| = n).
Proof.
move=> npos closed; have := closed 'K_n set0 (card_ord n).
have empty_order : #|induced (set0 : {set 'K_n})| = 0.
  rewrite card_sig; apply/eqP; rewrite cards_eq0; apply/eqP/setP => x.
  by rewrite !inE.
rewrite empty_order => zero; by move: npos; rewrite -zero.
Qed.
