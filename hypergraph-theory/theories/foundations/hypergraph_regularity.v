(** * Hypergraph.foundations.hypergraph_regularity -- regular supplied hyperedge families

    Library migration D8 (registry entry [regularity], class [finite-incidence-regularity]; report
    meta/migration_reports/regularity.md; record meta/LIBRARY_MIGRATION_D8.md; public client
    theories/examples/regular_hypergraphs.v).

    [hg_regular E d]: every vertex of the finite carrier [T] lies in exactly [d] members of the supplied
    family [E : {set {set T}}], counted by A10's [GTBase.incidence.incidence_degree].  The carrier and
    the family are arbitrary, [E] comes before [d], and the equality is universal: no uniformity,
    positivity, inhabited-carrier, nonempty-edge, covering or attained-degree premise.  On an empty
    carrier every [d] is a regularity degree, so uniqueness of the degree needs a supplied vertex.
    Empty members contain no vertex and never change a degree.  [hg_regularP] reflects the predicate
    onto the Boolean [[forall v, incidence_degree E v == d]].  Simple-graph ([GTBase.base.regular]),
    multigraph ([mregular]), directed and infinite regularity are different interfaces.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Regularity.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e : {set T}) (v : T) (d : nat).

Definition hg_regular E d : Prop := forall v : T, incidence_degree E v = d.

(** Boolean view: universal equality of the incidence degrees. *)
Lemma hg_regularP E d : reflect (hg_regular E d) [forall v, incidence_degree E v == d].
Proof. by apply: (iffP forallP) => [H v | H v]; apply/eqP; exact: H. Qed.

(** An empty carrier is regular of every degree. *)
Lemma hg_regular_void E d : (T -> False) -> hg_regular E d.
Proof. by move=> T0 v; case: (T0 v). Qed.

(** With a supplied vertex the degree is unique. *)
Lemma hg_regular_uniq E d1 d2 (v : T) : hg_regular E d1 -> hg_regular E d2 -> d1 = d2.
Proof. by move=> r1 r2; rewrite -(r1 v) (r2 v). Qed.

(** The empty family is 0-regular, and on an inhabited carrier only 0-regular. *)
Lemma hg_regular_set0 : hg_regular set0 0.
Proof. by move=> v; rewrite incidence_degree_set0. Qed.

Lemma hg_regular_set0E d (v : T) : hg_regular set0 d <-> d = 0.
Proof.
split=> [r|->]; last exact: hg_regular_set0.
by rewrite -(r v) incidence_degree_set0.
Qed.

(** Empty members contain no vertex: adding one changes no degree. *)
Lemma incidence_degree_set0U E v : incidence_degree (set0 |: E) v = incidence_degree E v.
Proof. by apply: eq_card => e; rewrite !inE; case: eqP => [->|_]; rewrite ?in_set0 ?andbF. Qed.

Lemma hg_regular_set0U E d : hg_regular (set0 |: E) d <-> hg_regular E d.
Proof. by split=> r v; rewrite -(r v) incidence_degree_set0U. Qed.

(** The single empty edge is 0-regular; the single full edge is 1-regular. *)
Lemma hg_regular_set1_set0 : hg_regular [set set0] 0.
Proof. by move=> v; rewrite incidence_degree_set1 in_set0. Qed.

Lemma hg_regular_setT : hg_regular [set [set: T]] 1.
Proof. by move=> v; rewrite incidence_degree_set1 in_setT. Qed.

End Regularity.
