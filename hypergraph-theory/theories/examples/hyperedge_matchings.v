(** Public-only client of [Hypergraph.foundations.hypergraph_matchings] ([hg_matching M E]: [M] is a
    subfamily of the hyperedge family [E] whose distinct members are pairwise disjoint).  No
    conjecture module is imported.  Covered: the empty family, singletons (the empty hyperedge
    included), the empty carrier against the empty hyperedge family, overlapping members, subfamily
    and ambient-family monotonicity, and the explicit [trivIset] reflection. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph_matchings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The empty family and singletons *)

Example empty_matching (T : finType) (E : {set {set T}}) : hg_matching set0 E.
Proof. exact: hg_matching0. Qed.

Example singleton_matching (T : finType) (e : {set T}) (E : {set {set T}}) :
  hg_matching [set e] E <-> e \in E.
Proof. exact: hg_matching1. Qed.

(** The empty hyperedge is not excluded: on its own it is a matching exactly when it is a hyperedge. *)
Example empty_edge_singleton (T : finType) (E : {set {set T}}) :
  hg_matching [set set0] E <-> (set0 : {set T}) \in E.
Proof. exact: hg_matching1. Qed.

(** ** The empty carrier against the empty hyperedge family *)

(** On the empty carrier ['I_0], [[set set0]] is a matching of size one of [[set set0]]. *)
Example empty_carrier_size_one :
  hg_matching [set (set0 : {set 'I_0})] [set set0] /\ #|[set (set0 : {set 'I_0})]| = 1.
Proof. by split; [apply/hg_matching1; rewrite inE | rewrite cards1]. Qed.

(** The empty hyperedge family admits only the empty matching. *)
Example empty_family_matchings (T : finType) (M : {set {set T}}) :
  hg_matching M set0 <-> M = set0.
Proof. exact: hg_matching_set0E. Qed.

(** ** Overlapping members *)

(** [[set true]] and [[set: bool]] are distinct and share [true]: no family containing both is a
    matching, whatever the hyperedge family. *)
Example overlapping_rejected (E : {set {set bool}}) :
  ~ hg_matching [set [set true]; [set: bool]] E.
Proof.
have ne : [set true] != [set: bool].
  by apply/negP => /eqP /setP /(_ false); rewrite !inE.
have meet : ~~ [disjoint [set true] & [set: bool]].
  by rewrite -setI_eq0 setIT; apply/set0Pn; exists true; rewrite inE.
by apply: (hg_matching_overlap _ _ ne meet); rewrite !inE eqxx ?orbT.
Qed.

(** ** Monotonicity *)

Example matching_subfamily (T : finType) (N M E : {set {set T}}) :
  N \subset M -> hg_matching M E -> hg_matching N E.
Proof. exact: hg_matchingS. Qed.

Example matching_ambient (T : finType) (M E F : {set {set T}}) :
  E \subset F -> hg_matching M E -> hg_matching M F.
Proof. exact: hg_matching_ambient. Qed.

(** The empty hyperedge, when it is one, can join any matching. *)
Example matching_add_empty_edge (T : finType) (M E : {set {set T}}) :
  set0 \in E -> hg_matching M E -> hg_matching (set0 |: M) E.
Proof. exact: hg_matching_set0U. Qed.

(** ** Boolean reflection through MathComp's [trivIset] *)

Example matching_trivIset (T : finType) (M E : {set {set T}}) :
  hg_matching M E <-> (M \subset E) && trivIset M.
Proof. exact: (rwP (hg_matchingP M E)). Qed.

(** A concrete use: the two singletons of [bool] form a matching of the whole power set. *)
Example bool_singletons_matching : hg_matching [set [set true]; [set false]] [set: {set bool}].
Proof.
apply/hg_matchingP; rewrite subsetT /=; apply/trivIsetP => A B.
rewrite !inE => /orP[] /eqP-> /orP[] /eqP->; rewrite ?eqxx // => _;
  rewrite -setI_eq0; apply/eqP/setP => b; rewrite !inE; by case: b.
Qed.

Print Assumptions empty_carrier_size_one.
Print Assumptions overlapping_rejected.
Print Assumptions bool_singletons_matching.
