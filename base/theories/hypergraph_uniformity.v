(** * Uniform finite hypergraphs

    [uniform_family E k]: every member of the finite set family [E : {set {set T}}] has
    exactly [k] elements, over an ARBITRARY finite vertex type [T]; [uniform_familyb] is its
    Boolean view and [uniform_familyP] the reflection.  There is no nonempty-family,
    positive-rank, loopless, no-isolated-vertex or carrier-inhabitance guard: the empty
    family is k-uniform for every k, and the family {set0} is exactly 0-uniform.

    [uniform_incidence inc k] is the same contract for a supplied edge-INDEX type [I] with
    incidence map [inc : I -> {set T}] ("every label has an incidence set of size k").  Its
    image-family bridge [uniform_incidence_imageE] needs no injectivity: repeated labels and
    empty incidence sets are allowed, and uniformity says nothing about simplicity.

    Import explicitly; [GTBase.base] does not re-export this module. *)
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Uniformity.
Variable T : finType.
Implicit Types (E F : {set {set T}}) (e : {set T}).

Definition uniform_family E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

Definition uniform_familyb E (k : nat) : bool := [forall e in E, #|e| == k].

Lemma uniform_familyP E k : reflect (uniform_family E k) (uniform_familyb E k).
Proof.
apply: (iffP forallP) => [H e eE|H e].
  by apply/eqP; move: (H e); rewrite eE.
by apply/implyP => eE; apply/eqP; exact: H.
Qed.

(** The empty family is uniform at every rank. *)
Lemma uniform_family0 k : uniform_family set0 k.
Proof. by move=> e; rewrite inE. Qed.

(** The family whose only member is the empty set is uniform exactly at rank 0. *)
Lemma uniform_family_set0 k : uniform_family [set set0] k <-> k = 0.
Proof.
split=> [H|->]; first by rewrite -(H set0 (set11 _)) cards0.
by move=> e /set1P ->; rewrite cards0.
Qed.

Lemma uniform_family1 e : uniform_family [set e] #|e|.
Proof. by move=> f /set1P ->. Qed.

Lemma uniform_familyS E F k : F \subset E -> uniform_family E k -> uniform_family F k.
Proof. by move=> /subsetP FE H e /FE; exact: H. Qed.

(** The rank is determined only by a member. *)
Lemma uniform_family_rank E k l e :
  e \in E -> uniform_family E k -> uniform_family E l -> k = l.
Proof. by move=> eE Hk Hl; rewrite -(Hk e eE) (Hl e eE). Qed.

(** A member bounds the rank by the number of vertices. *)
Lemma uniform_family_rank_le E k e : e \in E -> uniform_family E k -> k <= #|T|.
Proof. by move=> eE H; rewrite -(H e eE) max_card. Qed.

End Uniformity.

Section Incidence.
Variables (I T : finType) (inc : I -> {set T}).

Definition uniform_incidence (k : nat) : Prop := forall i : I, #|inc i| = k.

Lemma uniform_incidence_imageE k :
  uniform_incidence k <-> uniform_family [set inc i | i in [set: I]] k.
Proof.
split=> [H e /imsetP [i _ ->]|H i]; first exact: H.
by apply: H; apply/imsetP; exists i.
Qed.

End Incidence.
