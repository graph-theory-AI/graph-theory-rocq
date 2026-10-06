(** A24 Petersen (cycle): the frozen D1 ordinal construction and U10 Kneser construction with their four constructor
    proofs, U10's edge interface [Pedge]/[psupp]/[Padj], the three complete current Props and the complete A13+A24
    Petersen-colouring row.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/petersen.spec.json.
    - [D1Legacy]: the literal ordered table of fifteen natural pairs, the natural relation (false outside [0..9] and on
      equal ends), the ordinal relation, the two constructor proofs with their original scripts, the graph, and the
      4-flow row (positive edge count, undirected bridgeless, no Petersen minor through internally connected,
      nonempty, disjoint branch sets, integer 4-flow bounds).
    - [U10Legacy]: the exact two-subset carrier of ['I_5], disjointness, the two constructor proofs, the graph, the
      ordered edge representatives [Pedge], their supports and support adjacency, and the colouring row (positive
      vertex count, loopless cubic bridgeless, the same edge-to-[Pedge] map and line-adjacent triples).
    - [ImplicationsU10Legacy]: the explicitly non-corpus BF-cover hypothesis (six [Pedge] sets, each meeting every
      claw once, each representative covered twice) over the frozen interface; it stays an explicit hypothesis.
    - [U10Original] (text at A13's baseline 58f2862): the colouring row over the frozen interface and A13's frozen
      [cubic_bridgeless] (and so its loopless degree-three [cubic]); A13's module is aliased, not imported.
    The frozen constructions differ from GTBase.petersen's only in their opaque proof fields: same carriers and
    convertible relations, so they are related by pointwise adjacency and identity isomorphisms, and the frozen
    chains and rows are convertible to the live ones. *)
From GraphTheory Require Import mgraph sgraph.
From GTBase Require Import base petersen.
From Cycle.conjectures Require Import D1 U10 implications_U10.
From Cycle.migration Require mregular.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A13's certificate module, aliased without Import: its module names coincide with this file's. *)
Module A13 := Cycle.migration.mregular.

(** D1's texts elaborate as in D1, whose [Open Scope ring_scope] the import of D1 brings here. *)
Module D1Legacy.

Definition pedges : seq (nat * nat) :=
  [:: (0,1); (1,2); (2,3); (3,4); (4,0);
      (0,5); (1,6); (2,7); (3,8); (4,9);
      (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.

Definition pconn (a b : nat) : bool := ((a, b) \in D1Legacy.pedges) || ((b, a) \in D1Legacy.pedges).

Definition padj (x y : 'I_10) : bool := (x != y) && D1Legacy.pconn (val x) (val y).

Lemma padj_sym : symmetric D1Legacy.padj.
Proof. by move=> x y; rewrite /D1Legacy.padj /D1Legacy.pconn eq_sym orbC. Qed.

Lemma padj_irrefl : irreflexive D1Legacy.padj.
Proof. by move=> x; rewrite /D1Legacy.padj eqxx. Qed.

Definition petersen : sgraph := SGraph D1Legacy.padj_sym D1Legacy.padj_irrefl.

Definition four_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G -> ~ mg_minor G D1Legacy.petersen ->
    has_nz_kflow G 4.

End D1Legacy.

(** U10's and implications_U10's texts elaborate, as in their files, without [ring_scope]. *)
Close Scope ring_scope.

Module U10Legacy.

Definition petersenV : finType := {x : {set 'I_5} | #|x| == 2}.

Definition padj (x y : U10Legacy.petersenV) : bool := [disjoint val x & val y].

Lemma padj_sym : symmetric U10Legacy.padj.
Proof. by move=> x y; rewrite /U10Legacy.padj disjoint_sym. Qed.

Lemma padj_irrefl : irreflexive U10Legacy.padj.
Proof.
move=> x; apply/negP; rewrite /U10Legacy.padj -setI_eq0 setIid => /eqP Hx.
by move: (valP x); rewrite Hx cards0.
Qed.

Definition petersen : sgraph := SGraph U10Legacy.padj_sym U10Legacy.padj_irrefl.

Definition Pedge : finType := {p : U10Legacy.petersenV * U10Legacy.petersenV | U10Legacy.padj p.1 p.2}.

Definition psupp (q : U10Legacy.Pedge) : {set U10Legacy.petersenV} := [set (val q).1; (val q).2].

Definition Padj (q r : U10Legacy.Pedge) : bool :=
  (U10Legacy.psupp q != U10Legacy.psupp r) && (U10Legacy.psupp q :&: U10Legacy.psupp r != set0).

Definition petersen_coloring_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists f : edge G -> U10Legacy.Pedge,
      forall e1 e2 e3 : edge G,
        mut_adj3 (@line_rel G) e1 e2 e3 ->
        mut_adj3 U10Legacy.Padj (f e1) (f e2) (f e3).

End U10Legacy.

Module ImplicationsU10Legacy.

Definition external_petersen_BF_cover_statement : Prop :=
  exists LP : seq {set U10Legacy.Pedge},
    [/\ size LP = 6,
        (forall (S : {set U10Legacy.Pedge}) (q1 q2 q3 : U10Legacy.Pedge),
           S \in LP -> mut_adj3 U10Legacy.Padj q1 q2 q3 ->
           ((q1 \in S) + (q2 \in S) + (q3 \in S))%N = 1)
      & (forall q : U10Legacy.Pedge, count (fun S : {set U10Legacy.Pedge} => q \in S) LP = 2)].

End ImplicationsU10Legacy.

Module U10Original.

Definition petersen_coloring_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> A13.U10Legacy.cubic_bridgeless G ->
    exists f : edge G -> U10Legacy.Pedge,
      forall e1 e2 e3 : edge G,
        mut_adj3 (@line_rel G) e1 e2 e3 ->
        mut_adj3 U10Legacy.Padj (f e1) (f e2) (f e3).

End U10Original.

(** D1: the literal table, the natural relation and the ordinal relation are the same terms. *)
Lemma pedges_compat :
  D1Legacy.pedges = Cycle.conjectures.D1.pedges.
Proof.
by [].
Qed.

Lemma pconn_compat (a b : nat) :
  D1Legacy.pconn a b = Cycle.conjectures.D1.pconn a b.
Proof.
by [].
Qed.

Lemma d1_padj_compat (x y : 'I_10) :
  D1Legacy.padj x y = Cycle.conjectures.D1.padj x y.
Proof.
by [].
Qed.

(** The frozen constructor proofs and the live ones build isomorphic graphs (identity on ['I_10]); the graph
    constructors agree pointwise and by the identity isomorphism -- not by an equation between proof fields. *)
Lemma d1_padj_proofs_compat :
  SGraph D1Legacy.padj_sym D1Legacy.padj_irrefl ≃
  SGraph Cycle.conjectures.D1.padj_sym Cycle.conjectures.D1.padj_irrefl.
Proof. by apply: eq_diso => x y. Qed.

Lemma d1_petersen_compat :
  @edge_rel D1Legacy.petersen =2 @edge_rel Cycle.conjectures.D1.petersen.
Proof.
by [].
Qed.

Lemma d1_petersen_diso : D1Legacy.petersen ≃ Cycle.conjectures.D1.petersen.
Proof. by rewrite /D1Legacy.petersen /Cycle.conjectures.D1.petersen /petersen_ord; apply: eq_diso => x y. Qed.

Lemma four_flow_statement_compat :
  D1Legacy.four_flow_statement <-> Cycle.conjectures.D1.four_flow_statement.
Proof.
rewrite /D1Legacy.four_flow_statement.
reflexivity.
Qed.

(** U10: the same two-subset carrier and disjointness; isomorphic constructions. *)
Lemma petersenV_compat :
  U10Legacy.petersenV = Cycle.conjectures.U10.petersenV.
Proof.
by [].
Qed.

Lemma u10_padj_compat (x y : U10Legacy.petersenV) :
  U10Legacy.padj x y = Cycle.conjectures.U10.padj x y.
Proof.
by [].
Qed.

Lemma u10_padj_proofs_compat :
  SGraph U10Legacy.padj_sym U10Legacy.padj_irrefl ≃
  SGraph Cycle.conjectures.U10.padj_sym Cycle.conjectures.U10.padj_irrefl.
Proof. by apply: eq_diso => x y. Qed.

Lemma u10_petersen_compat :
  @edge_rel U10Legacy.petersen =2 @edge_rel Cycle.conjectures.U10.petersen.
Proof.
by [].
Qed.

Lemma u10_petersen_diso : U10Legacy.petersen ≃ Cycle.conjectures.U10.petersen.
Proof. by rewrite /U10Legacy.petersen /Cycle.conjectures.U10.petersen /petersen_kneser; apply: eq_diso => x y. Qed.

(** The edge interface: the same ordered representatives, supports and support adjacency. *)
Lemma Pedge_compat :
  U10Legacy.Pedge = Cycle.conjectures.U10.Pedge.
Proof.
by [].
Qed.

Lemma psupp_compat (q : U10Legacy.Pedge) :
  U10Legacy.psupp q = Cycle.conjectures.U10.psupp q.
Proof.
by [].
Qed.

Lemma Padj_compat (q r : U10Legacy.Pedge) :
  U10Legacy.Padj q r = Cycle.conjectures.U10.Padj q r.
Proof.
by [].
Qed.

Lemma petersen_coloring_statement_compat :
  U10Legacy.petersen_coloring_statement <->
  Cycle.conjectures.U10.petersen_coloring_statement.
Proof.
rewrite /U10Legacy.petersen_coloring_statement.
reflexivity.
Qed.

Lemma external_petersen_BF_cover_statement_compat :
  ImplicationsU10Legacy.external_petersen_BF_cover_statement <->
  Cycle.conjectures.implications_U10.external_petersen_BF_cover_statement.
Proof.
rewrite /ImplicationsU10Legacy.external_petersen_BF_cover_statement.
reflexivity.
Qed.

(** The complete A13+A24 row: the frozen edge interface is convertible to the live one, then A13's whole-row
    certificate. *)
Lemma petersen_coloring_statement_original_compat :
  U10Original.petersen_coloring_statement <->
  Cycle.conjectures.U10.petersen_coloring_statement.
Proof.
rewrite /U10Original.petersen_coloring_statement.
exact: A13.petersen_coloring_statement_compat.
Qed.
