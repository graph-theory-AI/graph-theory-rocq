(** Public-only client of [Hypergraph.foundations.hypergraph_regularity] ([hg_regular E d]: every vertex
    of the finite carrier lies in exactly [d] members of the supplied family [E], counted by A10's
    [incidence_degree]).  No conjecture module is imported.  Covered: the empty carrier for every [d]
    (with an empty or a singleton-empty family), the empty family on an inhabited carrier (exactly
    [d = 0]), singleton and empty-edge incidence, invariance under adding an empty edge, the full-edge
    family of degree one, degree uniqueness with a supplied vertex (and its failure without one), and
    the Boolean universal-equality reflection. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph_regularity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The empty carrier: every degree *)

Lemma no_vertex0 (v : 'I_0) : False.
Proof. by case: v => m; rewrite ltn0. Qed.

Example void_regular (E : {set {set 'I_0}}) (d : nat) : hg_regular E d.
Proof. exact: hg_regular_void no_vertex0. Qed.

Example void_empty_families (d : nat) :
  hg_regular (set0 : {set {set 'I_0}}) d /\ hg_regular [set (set0 : {set 'I_0})] d.
Proof. by split; exact: void_regular. Qed.

(** Without a vertex the degree is not unique. *)
Example void_degree_not_unique : hg_regular (set0 : {set {set 'I_0}}) 0 /\ hg_regular (set0 : {set {set 'I_0}}) 1.
Proof. by split; exact: void_regular. Qed.

(** ** Supplied vertices *)

Example degree_unique (T : finType) (E : {set {set T}}) (v : T) (d1 d2 : nat) :
  hg_regular E d1 -> hg_regular E d2 -> d1 = d2.
Proof. exact: hg_regular_uniq. Qed.

Example empty_family_degree (T : finType) (v : T) (d : nat) : hg_regular (set0 : {set {set T}}) d <-> d = 0.
Proof. exact: hg_regular_set0E. Qed.

(** ** Singleton, empty and full edges *)

Example singleton_incidence (T : finType) (e : {set T}) (v : T) : incidence_degree [set e] v = (v \in e).
Proof. exact: incidence_degree_set1. Qed.

Example empty_edge_incidence (T : finType) (v : T) : incidence_degree [set (set0 : {set T})] v = 0.
Proof. by rewrite incidence_degree_set1 in_set0. Qed.

Example empty_edge_regular (T : finType) : hg_regular [set (set0 : {set T})] 0.
Proof. exact: hg_regular_set1_set0. Qed.

Example add_empty_edge (T : finType) (E : {set {set T}}) (d : nat) :
  hg_regular (set0 |: E) d <-> hg_regular E d.
Proof. exact: hg_regular_set0U. Qed.

Example full_edge_regular (T : finType) : hg_regular [set [set: T]] 1.
Proof. exact: hg_regular_setT. Qed.

(** ** Boolean reflection *)

Example regular_bool (T : finType) (E : {set {set T}}) (d : nat) :
  hg_regular E d <-> [forall v, incidence_degree E v == d].
Proof. exact: (rwP (hg_regularP E d)). Qed.

Example full_edge_bool (T : finType) : [forall v : T, incidence_degree [set [set: T]] v == 1].
Proof. exact/hg_regularP/hg_regular_setT. Qed.

Print Assumptions void_degree_not_unique.
Print Assumptions empty_family_degree.
Print Assumptions full_edge_bool.
