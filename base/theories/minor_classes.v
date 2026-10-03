(** * Excluded minors and closure of finite simple graph classes

    Classes are arbitrary [sgraph -> Prop] predicates. [excludes_a_minor]
    supplies one forbidden minor for the whole class; it does NOT require
    closure. [minor_closed] is closure under the upstream relation [minor],
    whose first argument is the host. [proper_minor_closed_class] explicitly
    conjoins both contracts. No class or graph inhabitance guard is added.

    The witness-only and conjunction contracts must remain distinct: some
    legacy statements use only the former despite their helper names.
    Registry: proper-minor-closed-class (C11). *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph minor.
From GTBase Require Import graph_classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition excludes_a_minor (C : sgraph -> Prop) : Prop :=
  exists H : sgraph, forall G : sgraph, C G -> ~ minor G H.

Definition minor_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> minor G H -> C H.

Definition proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  excludes_a_minor C /\ minor_closed C.

(** Upstream [iso_strict_minor] reverses the supplied isomorphism. *)
Lemma minor_self (G : sgraph) : minor G G.
Proof. exact: strict_is_minor (iso_strict_minor (@diso_id G)). Qed.

Lemma excludes_a_minor_ext (C D : sgraph -> Prop) :
  (forall G, C G <-> D G) -> (excludes_a_minor C <-> excludes_a_minor D).
Proof.
move=> same; split=> -[H excluded]; exists H => G member.
- apply: excluded; by apply/(same G).2.
- apply: excluded; by apply/(same G).1.
Qed.

Lemma minor_closed_ext (C D : sgraph -> Prop) :
  (forall G, C G <-> D G) -> (minor_closed C <-> minor_closed D).
Proof.
move=> same; split=> cls G H member sub.
- apply/(same H).1; apply: cls sub; by apply/(same G).2.
- apply/(same H).2; apply: cls sub; by apply/(same G).1.
Qed.

Lemma proper_minor_closed_class_ext (C D : sgraph -> Prop) :
  (forall G, C G <-> D G) ->
  (proper_minor_closed_class C <-> proper_minor_closed_class D).
Proof.
move=> same; split=> -[excluded cls]; split.
- by apply/(excludes_a_minor_ext same).
- by apply/(minor_closed_ext same).
- by apply/(excludes_a_minor_ext same).
- by apply/(minor_closed_ext same).
Qed.

Lemma proper_minor_closed_class_excludes (C : sgraph -> Prop) :
  proper_minor_closed_class C -> excludes_a_minor C.
Proof. by case. Qed.

Lemma proper_minor_closed_class_closed (C : sgraph -> Prop) :
  proper_minor_closed_class C -> minor_closed C.
Proof. by case. Qed.

Lemma proper_minor_closed_class_intro (C : sgraph -> Prop) :
  excludes_a_minor C -> minor_closed C -> proper_minor_closed_class C.
Proof. by split. Qed.

Lemma minor_closed_induced (C : sgraph -> Prop) :
  minor_closed C -> induced_closed C.
Proof.
move=> cls G S member.
apply (cls G (induced S) member).
exact: induced_minor.
Qed.

Lemma minor_closed_iso (C : sgraph -> Prop) :
  minor_closed C -> iso_closed C.
Proof.
move=> cls G H member iso; apply (cls G H member).
exact: strict_is_minor (iso_strict_minor (diso_sym iso)).
Qed.

Lemma minor_closed_hereditary (C : sgraph -> Prop) :
  minor_closed C -> hereditary_class C.
Proof. move=> cls; split; [exact: minor_closed_iso cls|exact: minor_closed_induced cls]. Qed.

Lemma proper_minor_closed_class_empty :
  proper_minor_closed_class (fun _ : sgraph => False).
Proof. split; [exists 'K_0; by move=> G []|by move=> G H []]. Qed.

Lemma minor_closed_all : minor_closed (fun _ : sgraph => True).
Proof. by []. Qed.

Lemma not_excludes_a_minor_all : ~ excludes_a_minor (fun _ : sgraph => True).
Proof. move=> [H excluded]; exact: excluded H I (minor_self H). Qed.

Lemma excludes_a_minor_order_le n :
  excludes_a_minor (fun G : sgraph => #|G| <= n).
Proof. exists 'K_n.+1 => G bound; exact: small_K_free bound. Qed.

Lemma excludes_a_minor_exact_order n :
  excludes_a_minor (fun G : sgraph => #|G| = n).
Proof. exists 'K_n.+1 => G order; apply: small_K_free; by rewrite order. Qed.

Lemma not_minor_closed_positive_exact_order n :
  0 < n -> ~ minor_closed (fun G : sgraph => #|G| = n).
Proof. move=> positive /minor_closed_induced; exact: not_induced_closed_positive_exact_order positive. Qed.

Lemma excluded_minor_class_closed (H : sgraph) :
  minor_closed (fun G : sgraph => ~ minor G H).
Proof. move=> G K excluded sub obstruction; apply: excluded; exact: minor_trans sub obstruction. Qed.

Lemma excluded_minor_class_proper (H : sgraph) :
  proper_minor_closed_class (fun G : sgraph => ~ minor G H).
Proof. split; [by exists H|exact: excluded_minor_class_closed]. Qed.

(** Under minor closure, omitting a member is equivalent to excluding a minor. *)
Lemma minor_closed_omits_iff (C : sgraph -> Prop) :
  minor_closed C -> (excludes_a_minor C <-> exists H : sgraph, ~ C H).
Proof.
move=> cls; split=> -[H excluded]; exists H.
- move=> member; exact: excluded H member (minor_self H).
- move=> G member sub; apply: excluded; exact (cls G H member sub).
Qed.

Lemma excludes_a_minor_subclass (C D : sgraph -> Prop) :
  (forall G, C G -> D G) -> excludes_a_minor D -> excludes_a_minor C.
Proof. move=> sub [H excluded]; exists H => G /sub member; exact: excluded G member. Qed.
