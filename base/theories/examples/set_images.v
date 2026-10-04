(** Public-only client of the image of a supplied finite set ([f @: A], MathComp's [imset]) and
    of [GTBase.set_images].  No corpus module is imported.  Covered: the raw bounded-existential
    presentation, the empty set and the empty domain, a map into the empty ordinal codomain,
    singleton, identity, union and composition, the cardinality bound and the injective case
    with its premise, and a two-to-one collapse where the cardinality equality fails. *)
From GTBase Require Import base set_images.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Images.
Variables (aT bT cT : finType).

Example raw_image_presentation (f : aT -> bT) (A : {set aT}) :
  [set y | [exists x, (x \in A) && (y == f x)]] = f @: A.
Proof. exact: imset_existsE. Qed.

Example image_of_empty_set (f : aT -> bT) : f @: (set0 : {set aT}) = set0.
Proof. exact: imset0. Qed.

Example image_singleton (f : aT -> bT) (x : aT) : f @: [set x] = [set f x].
Proof. exact: imset_set1. Qed.

Example image_identity (A : {set aT}) : id @: A = A.
Proof. exact: imset_id. Qed.

Example image_union (f : aT -> bT) (A B : {set aT}) : f @: (A :|: B) = f @: A :|: f @: B.
Proof. exact: imsetU. Qed.

Example image_composition (f : aT -> bT) (g : bT -> cT) (A : {set aT}) :
  (g \o f) @: A = g @: (f @: A).
Proof. exact: imset_comp. Qed.

Example image_card_le (f : aT -> bT) (A : {set aT}) : #|f @: A| <= #|A|.
Proof. exact: leq_imset_card. Qed.

(** Under injectivity, cardinality is preserved. *)
Example image_card_injective (f : aT -> bT) (A : {set aT}) : injective f -> #|f @: A| = #|A|.
Proof. exact: card_imset. Qed.

End Images.

(** Empty domain: every set over ['I_0] is empty, and so is its image. *)
Example image_over_empty_domain (bT : finType) (f : 'I_0 -> bT) (A : {set 'I_0}) : f @: A = set0.
Proof. by apply/setP => y; rewrite inE; apply/imsetP => -[[]]. Qed.

(** A supplied map into the empty ordinal codomain forces an empty domain: images are empty. *)
Example image_into_empty_codomain (aT : finType) (f : aT -> 'I_0) (A : {set aT}) : f @: A = set0.
Proof. by apply/setP => y; case: y. Qed.

(** Two-to-one collapse: both vertices of a 2-set go to one point, so the image has fewer
    elements and the cardinality equality needs injectivity. *)
Example two_to_one_collapse :
  (fun _ : 'I_2 => (ord0 : 'I_1)) @: [set: 'I_2] = [set ord0] /\
  #|(fun _ : 'I_2 => (ord0 : 'I_1)) @: [set: 'I_2]| < #|[set: 'I_2]|.
Proof.
have E : (fun _ : 'I_2 => (ord0 : 'I_1)) @: [set: 'I_2] = [set ord0].
  apply/setP => y; rewrite !inE (ord1 y) eqxx; apply/imsetP.
  by exists ord0; rewrite ?inE.
by split=> //; rewrite E cards1 cardsT card_ord.
Qed.

Print Assumptions raw_image_presentation.
Print Assumptions image_into_empty_codomain.
Print Assumptions two_to_one_collapse.
