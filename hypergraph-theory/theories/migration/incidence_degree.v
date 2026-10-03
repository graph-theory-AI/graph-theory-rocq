(** A10 incidence degree (hypergraph): the frozen counts of the members of a supplied family
    containing a vertex, the public foundation's degeneracy chain, and the five rows (X6, XE2 #833,
    X73, X108 and X225).  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/incidence_degree.spec.json.  Every count is over an ARBITRARY finite
    family on an arbitrary [finType]; no uniformity, nonemptiness or edge premise is added.
    - [Legacy]: the X6/X73 counts and the public [hg_degree] (in its original Section context)
      convert to [GTBase.incidence.incidence_degree]; X108's count of the members containing [v]
      and lying inside [W] is the canonical count of the explicitly restricted family, a proved
      equality (the two conjunctions are ordered differently).
    - [FoundationLegacy]: [hg_degree]'s chain in [Hypergraph.foundations.hypergraph], in its
      original Section context: the degeneracy test, the opaque existence witness and its two
      support lemmas (copied verbatim, with frozen references, so that the witness proof is the
      original one and closed over the frozen degree), the least degeneracy, the skeletal
      degeneracy and [d_max].  The independent [hg_restrict] and [hg_skeleton] stay shared.  The
      two least naturals are compared through [eq_ex_minn]; no equality of proofs is claimed.
    - [X6Legacy], [XE2Legacy], [X73Legacy], [X108Legacy], [X225Legacy]: the rows over these frozen
      copies.  Every other helper stays live. *)
From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import X6 X73 X108 XE2 X225.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x6_hg_degree (T : finType) (E : {set {set T}}) (v : T) : nat :=
  #|[set e in E | v \in e]|.

Definition x73_hyperdegree (T : finType) (E : {set {set T}}) (v : T) : nat :=
  #|[set e in E | v \in e]|.

Definition x108_degree_in
    (T : finType) (E : {set {set T}}) (W : {set T}) (v : T) : nat :=
  #|[set e in E | (v \in e) && (e \subset W)]|.

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}) (v : T).

Definition hg_degree E v : nat := #|[set e in E | v \in e]|.

End Hypergraph.

End Legacy.

Module FoundationLegacy.

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}) (v : T).

Lemma degree_le E S v : Legacy.hg_degree (hg_restrict E S) v <= #|E|.
Proof.
rewrite /Legacy.hg_degree /hg_restrict; apply: subset_leq_card; apply/subsetP => e.
by rewrite !inE => /andP[/andP[eE _] _].
Qed.

Definition degenerate_leb E (d : nat) : bool :=
  [forall S : {set T}, (S != set0) ==> [exists v in S, Legacy.hg_degree (hg_restrict E S) v <= d]].

Lemma degenerate_card E : degenerate_leb E #|E|.
Proof.
apply/forallP => S; apply/implyP => /set0Pn[v vS].
by apply/existsP; exists v; rewrite vS degree_le.
Qed.

Lemma degenerate_ex E : exists d, degenerate_leb E d.
Proof. by exists #|E|; apply: degenerate_card. Qed.

Definition degeneracy E : nat := ex_minn (degenerate_ex E).

Definition skel_degeneracy E (i : nat) : nat := degeneracy (hg_skeleton E i).

Definition dmax E (k : nat) : nat := \max_(i < k | 0 < i) skel_degeneracy E i.

End Hypergraph.

End FoundationLegacy.

Module X6Legacy.

Definition critical_three_uniform_min_degree_seven_statement : Prop :=
  exists (T : finType) (E : {set {set T}}),
    x6_uniform E 3 /\
    x6_chromatic_edge_critical E 3 /\
    (forall v : T, 7 <= Legacy.x6_hg_degree E v).

End X6Legacy.

Module XE2Legacy.

Definition erdos_833_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (r : nat) (T : finType) (E : {set {set T}}),
      2 <= r ->
      x6_uniform E r ->
      x6_chromatic_number E 3 ->
      exists v : T,
        xe2_fractional_exponential_degree cnum cden r (Legacy.x6_hg_degree E v).

End XE2Legacy.

Module X73Legacy.

Definition hyperdegree_regular (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall v : T, Legacy.x73_hyperdegree E v = d.

Definition regular_tripartite_hypergraph_matching_lower_bound_statement : Prop :=
  forall (d n : nat) (T : finType) (part : T -> 'I_3) (E : {set {set T}}),
    1 <= d ->
    x73_balanced_tripartite part n ->
    @x6_r_partite_uniform T 3 part E ->
    hyperdegree_regular E d ->
    exists M : {set {set T}},
      x6_matching M E /\ ((d.-1 * n) %/ d <= #|M|).

End X73Legacy.

Module X108Legacy.

Definition d_degenerate (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall W : {set T},
    W != set0 ->
    exists v : T, v \in W /\ Legacy.x108_degree_in E W v <= d.

Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        x108_uniform E 3 ->
        d_degenerate E d ->
        x108_two_colour_ramsey_at_most E (c * #|T|).

End X108Legacy.

Module X225Legacy.

Definition kpartite_hypergraph_turan_exponent_dmax_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists ck : nat,
      0 < ck /\
      forall (S : finType) (F : {set {set S}}) (part : S -> 'I_k),
        F != set0 ->
        hg_uniform F k ->
        hg_partite_uniform part F ->
        exists K : nat,
          0 < K /\
          eventually (fun n =>
            (hg_turan F k n) ^ (FoundationLegacy.dmax F k) * n ^ ck <= K * n ^ (k * FoundationLegacy.dmax F k)).

End X225Legacy.

(** ** Sources *)

Lemma x6_hg_degree_compat (T : finType) (E : {set {set T}}) (v : T) :
  Legacy.x6_hg_degree E v = x6_hg_degree E v.
Proof. by []. Qed.

Lemma x73_hyperdegree_compat (T : finType) (E : {set {set T}}) (v : T) :
  Legacy.x73_hyperdegree E v = x73_hyperdegree E v.
Proof. by []. Qed.

(** Not a conversion: [(v \in e) && (e \subset W)] against the restricted family's
    [(e \in E) && (e \subset W)], then [v \in e]. *)
Lemma x108_degree_in_compat (T : finType) (E : {set {set T}}) (W : {set T}) (v : T) :
  Legacy.x108_degree_in E W v = x108_degree_in E W v.
Proof.
rewrite /Legacy.x108_degree_in /x108_degree_in /incidence_degree; apply: eq_card => e.
by rewrite !inE; case: (e \in E); case: (v \in e); case: (e \subset W).
Qed.

Lemma hg_degree_compat (T : finType) (E : {set {set T}}) (v : T) :
  Legacy.hg_degree E v = hg_degree E v.
Proof. by []. Qed.

(** ** The foundation's degeneracy chain *)

Lemma hg_degenerate_leb_compat (T : finType) (E : {set {set T}}) (d : nat) :
  FoundationLegacy.degenerate_leb E d = hg_degenerate_leb E d.
Proof. by []. Qed.

(** The two opaque witnesses select the same least natural ([eq_ex_minn] compares the minima of
    two pointwise-equal predicates); the proofs themselves are not compared. *)
Lemma hg_degenerate_ex_compat (T : finType) (E : {set {set T}}) :
  ex_minn (FoundationLegacy.degenerate_ex E) = ex_minn (hg_degenerate_ex E).
Proof. by apply: eq_ex_minn => d; apply: hg_degenerate_leb_compat. Qed.

Lemma hg_degeneracy_compat (T : finType) (E : {set {set T}}) :
  FoundationLegacy.degeneracy E = hg_degeneracy E.
Proof. exact: hg_degenerate_ex_compat. Qed.

Lemma hg_skel_degeneracy_compat (T : finType) (E : {set {set T}}) (i : nat) :
  FoundationLegacy.skel_degeneracy E i = hg_skel_degeneracy E i.
Proof. exact: hg_degeneracy_compat. Qed.

(** For every [k], including the empty ranges [k = 0] and [k = 1] (both maxima are then 0). *)
Lemma hg_dmax_compat (T : finType) (E : {set {set T}}) (k : nat) :
  FoundationLegacy.dmax E k = hg_dmax E k.
Proof.
rewrite /FoundationLegacy.dmax /hg_dmax; apply: eq_bigr => i _.
exact: hg_skel_degeneracy_compat.
Qed.

(** ** Chains and rows *)

Lemma critical_three_uniform_min_degree_seven_statement_compat :
  X6Legacy.critical_three_uniform_min_degree_seven_statement <->
  critical_three_uniform_min_degree_seven_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_833_statement_compat : XE2Legacy.erdos_833_statement <-> erdos_833_statement.
Proof. exact: iff_refl. Qed.

Lemma x73_regular_compat (T : finType) (E : {set {set T}}) (d : nat) :
  X73Legacy.hyperdegree_regular E d <-> x73_regular E d.
Proof. exact: iff_refl. Qed.

Lemma regular_tripartite_hypergraph_matching_lower_bound_statement_compat :
  X73Legacy.regular_tripartite_hypergraph_matching_lower_bound_statement <->
  regular_tripartite_hypergraph_matching_lower_bound_statement.
Proof. exact: iff_refl. Qed.

Lemma x108_d_degenerate_compat (T : finType) (E : {set {set T}}) (d : nat) :
  X108Legacy.d_degenerate E d <-> x108_d_degenerate E d.
Proof.
split=> h W W0; have [v [vW le]] := h W W0; exists v; split=> //.
  by rewrite -x108_degree_in_compat.
by rewrite x108_degree_in_compat.
Qed.

Lemma three_uniform_degenerate_hypergraph_ramsey_linear_statement_compat :
  X108Legacy.three_uniform_degenerate_hypergraph_ramsey_linear_statement <->
  three_uniform_degenerate_hypergraph_ramsey_linear_statement.
Proof.
split=> h d; have [c hc] := h d; exists c => T E u dd; apply: hc => //.
  by apply/x108_d_degenerate_compat.
by apply/x108_d_degenerate_compat.
Qed.

(** The constant [ck] is still chosen after [k] and before the pattern, [K] after the pattern and
    its three guards; both exponents and the eventual inequality are kept, with the same witnesses
    and threshold. *)
Lemma kpartite_hypergraph_turan_exponent_dmax_statement_compat :
  X225Legacy.kpartite_hypergraph_turan_exponent_dmax_statement <->
  kpartite_hypergraph_turan_exponent_dmax_statement.
Proof.
split=> h k k2; have [ck [ck0 hck]] := h k k2; exists ck; split=> // S F part F0 u pu;
  have [K [K0 ev]] := hck S F part F0 u pu; exists K; split=> //.
  by rewrite -hg_dmax_compat.
by rewrite hg_dmax_compat.
Qed.
