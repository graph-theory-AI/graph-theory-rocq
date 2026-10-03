(** A20 stable sets (graph-theory-misc): the frozen X163, X169, X208 and X29 stable sets, X163's Boolean normality,
    X169's token-sliding and polytime chain, X208's maximum-output and polytime chain, X29's stable cover and normality,
    the four rows, and the complete X169 and X29 rows.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/stable_sets.spec.json.
    - [Legacy]: X163's Boolean [[forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]]] is EQUAL to upstream
      [stable S] ([GTBase.stable_sets.stable_eqbE]); X169's and X208's distinct-vertex and X29's all-pairs
      nonadjacency are iffs with it ([stable_distinctP], [stable_nonadjP]).
    - [X163Legacy], [X169Legacy], [X208Legacy], [X29Legacy]: the chains and rows over the frozen helpers.  X163's event
      stays Boolean and its random-graph weights, [0 < p < q] and positive-mass semantics are verbatim; X169's known
      blocked encoding (intermediate token-sliding states are not required to be stable) is kept, not repaired; X208's
      [7 <= t] and numeric maximum-size output (not a witness set) are kept with the same program and cost witnesses;
      X29's covers are arbitrary lists.  C13's chordal and clique-tree classes and A6's complement stay live in these
      per-row copies.
    - [X169Original], [X29Original] (texts at the pre-migration 9e03072): X169's polytime chain over C13's frozen
      classes and the frozen token-sliding chain, and its row; X29 over A6's frozen complement and the frozen normality
      chain.
      C13's and A6's modules are aliased, not imported; the bridges reuse their certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base stable_sets.
From GTMisc.conjectures Require Import X163 X169 X208 X29.
From GTMisc.migration Require bag_decompositions complement.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** C13's and A6's certificate modules, aliased without Import: their module names coincide with this file's. *)
Module C13 := GTMisc.migration.bag_decompositions.
Module A6 := GTMisc.migration.complement.

Module Legacy.

Definition x163_stableb (G : sgraph) (S : {set G}) : bool :=
  [forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]].

Definition x169_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x208_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x29_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> ~~ (x -- y).

End Legacy.

Module X163Legacy.

Definition x163_normal_graphb (G : sgraph) : bool :=
  [exists K : {set {set G}},
    [exists A : {set {set G}},
      [forall C in K, cliqueb C] &&
      [forall S in A, Legacy.x163_stableb S] &&
      [forall v : G, [exists C in K, v \in C]] &&
      [forall v : G, [exists S in A, v \in S]] &&
      [forall C in K, [forall S in A, C :&: S != set0]]]].

Definition random_graphs_normal_whp_statement : Prop :=
  forall p q : nat,
    0 < p ->
    p < q ->
    x163_random_graph_whp p q
      (fun n E => X163Legacy.x163_normal_graphb (fg_labelled_sgraph E)).

End X163Legacy.

Module X169Legacy.

Definition x169_token_sliding_connected (G : sgraph) (k : nat) : Prop :=
  forall A B : {set G},
    Legacy.x169_stable_set A -> #|A| = k ->
    Legacy.x169_stable_set B -> #|B| = k ->
    exists p : seq {set G}, path (x169_ts_step k) A p /\ last A p = B.

Definition x169_polytime_decides_TS_connectivity (k D : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => x169_chordal G /\ x169_clique_tree_degree_at_most G D)
    (fun G : sgraph => X169Legacy.x169_token_sliding_connected G k).

Definition token_sliding_chordal_clique_tree_degree_polytime_statement : Prop :=
  forall k D : nat, X169Legacy.x169_polytime_decides_TS_connectivity k D.

End X169Legacy.

Module X208Legacy.

Definition x208_maximum_independent_set_output (G : sgraph) (out : data) : Prop :=
  exists S : {set G},
    Legacy.x208_stable_set S /\
    #|S| = data_nat_value out /\
    forall T : {set G}, Legacy.x208_stable_set T -> #|T| <= #|S|.

Definition x208_polytime_mis_on (P : sgraph -> Prop) : Prop :=
  polytime_outputs_graph_on P X208Legacy.x208_maximum_independent_set_output.

Definition Pt_free_maximum_independent_set_polytime_statement : Prop :=
  forall t : nat, 7 <= t -> X208Legacy.x208_polytime_mis_on (fun G => x208_Pt_free G t).

End X208Legacy.

Module X29Legacy.

Definition x29_stable_cover (G : sgraph) (S : seq {set G}) : Prop :=
  (forall I : {set G}, I \in S -> Legacy.x29_stable_set I) /\
  forall v : G, exists I : {set G}, I \in S /\ v \in I.

Definition x29_normal_graph (G : sgraph) : Prop :=
  exists (C S : seq {set G}),
    x29_clique_cover C /\
    X29Legacy.x29_stable_cover S /\
    forall (K I : {set G}), K \in C -> I \in S -> K :&: I != set0.

Definition no_c5_c7_complement_c7_normal_graph_statement : Prop :=
  forall G : sgraph,
    ~ x29_has_induced_cycle G 5 ->
    ~ x29_has_induced_cycle G 7 ->
    ~ x29_has_induced_cycle (x29_complement G) 7 ->
    X29Legacy.x29_normal_graph G.

End X29Legacy.

Module X169Original.

Definition x169_polytime_decides_TS_connectivity (k D : nat) : Prop :=
  polytime_decides_graph_on
    (fun G : sgraph => C13.Legacy.x169_chordal G /\ C13.Legacy.x169_clique_tree_degree_at_most G D)
    (fun G : sgraph => X169Legacy.x169_token_sliding_connected G k).

Definition token_sliding_chordal_clique_tree_degree_polytime_statement : Prop :=
  forall k D : nat, X169Original.x169_polytime_decides_TS_connectivity k D.

End X169Original.

Module X29Original.

Definition no_c5_c7_complement_c7_normal_graph_statement : Prop :=
  forall G : sgraph,
    ~ x29_has_induced_cycle G 5 ->
    ~ x29_has_induced_cycle G 7 ->
    ~ x29_has_induced_cycle (A6.Legacy.x29_complement G) 7 ->
    X29Legacy.x29_normal_graph G.

End X29Original.

(** A Boolean equality, not an iff: X163's bounded form with its equality disjunct is upstream [stable S]. *)
Lemma x163_stableb_compat (G : sgraph) (S : {set G}) :
  Legacy.x163_stableb S = x163_stableb S.
Proof.
exact: (esym (stable_eqbE S)).
Qed.

(** Not conversions: the raw Prop presentations against the upstream Boolean, by reflection. *)
Lemma x169_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x169_stable_set S <-> x169_stable_set S.
Proof.
exact: (rwP (stable_distinctP S)).
Qed.

Lemma x208_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x208_stable_set S <-> x208_stable_set S.
Proof.
exact: (rwP (stable_distinctP S)).
Qed.

Lemma x29_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x29_stable_set S <-> x29_stable_set S.
Proof.
exact: (rwP (stable_nonadjP S)).
Qed.

(** Boolean normality: the same covers, pointwise Boolean equality of the stable-cover clause. *)
Lemma x163_normal_graphb_compat (G : sgraph) :
  X163Legacy.x163_normal_graphb G = x163_normal_graphb G.
Proof.
rewrite /X163Legacy.x163_normal_graphb /x163_normal_graphb.
apply: eq_existsb => K; apply: eq_existsb => A; congr (_ && _ && _ && _ && _).
by apply: eq_forallb => S; rewrite x163_stableb_compat.
Qed.

Lemma x163_event_weight_compat (p q n : nat) :
  fg_event_weight (@fg_gnp_weight p q n) (fun E => X163Legacy.x163_normal_graphb (fg_labelled_sgraph E)) =
  fg_event_weight (@fg_gnp_weight p q n) (fun E => x163_normal_graphb (fg_labelled_sgraph E)).
Proof.
by apply: eq_bigl => E; exact: x163_normal_graphb_compat.
Qed.

(** The same thresholds and the same event weights in both directions. *)
Lemma random_graphs_normal_whp_statement_compat :
  X163Legacy.random_graphs_normal_whp_statement <-> random_graphs_normal_whp_statement.
Proof.
rewrite /X163Legacy.random_graphs_normal_whp_statement /random_graphs_normal_whp_statement
  /x163_random_graph_whp /fg_whp /eventually.
split=> h p q p0 pq a b a0 ab; have [N hn] := h p q p0 pq a b a0 ab; exists N => n Nn.
- by move: (hn n Nn); rewrite x163_event_weight_compat.
- by move: (hn n Nn); rewrite x163_event_weight_compat.
Qed.

Lemma x169_token_sliding_connected_compat (G : sgraph) (k : nat) :
  X169Legacy.x169_token_sliding_connected G k <-> x169_token_sliding_connected G k.
Proof.
rewrite /X169Legacy.x169_token_sliding_connected /x169_token_sliding_connected.
setoid_rewrite x169_stable_set_compat.
reflexivity.
Qed.

(** The same program and cost witnesses; only the decided predicate is rewritten. *)
Lemma x169_polytime_decides_TS_connectivity_compat (k D : nat) :
  X169Legacy.x169_polytime_decides_TS_connectivity k D <-> x169_polytime_decides_TS_connectivity k D.
Proof.
rewrite /X169Legacy.x169_polytime_decides_TS_connectivity /x169_polytime_decides_TS_connectivity
  /polytime_decides_graph_on /polytime_decides_on_class /decides_on_class.
setoid_rewrite x169_token_sliding_connected_compat.
reflexivity.
Qed.

Lemma token_sliding_chordal_clique_tree_degree_polytime_statement_compat :
  X169Legacy.token_sliding_chordal_clique_tree_degree_polytime_statement <->
  token_sliding_chordal_clique_tree_degree_polytime_statement.
Proof.
rewrite /X169Legacy.token_sliding_chordal_clique_tree_degree_polytime_statement
  /token_sliding_chordal_clique_tree_degree_polytime_statement.
setoid_rewrite x169_polytime_decides_TS_connectivity_compat.
reflexivity.
Qed.

Lemma x208_maximum_independent_set_output_compat (G : sgraph) (out : data) :
  X208Legacy.x208_maximum_independent_set_output G out <-> x208_maximum_independent_set_output G out.
Proof.
rewrite /X208Legacy.x208_maximum_independent_set_output /x208_maximum_independent_set_output.
setoid_rewrite x208_stable_set_compat.
reflexivity.
Qed.

(** The same program and cost witnesses; only the output specification is rewritten. *)
Lemma x208_polytime_mis_on_compat (P : sgraph -> Prop) :
  X208Legacy.x208_polytime_mis_on P <-> x208_polytime_mis_on P.
Proof.
rewrite /X208Legacy.x208_polytime_mis_on /x208_polytime_mis_on /polytime_outputs_graph_on /polytime_outputs_on_class.
setoid_rewrite x208_maximum_independent_set_output_compat.
reflexivity.
Qed.

Lemma Pt_free_maximum_independent_set_polytime_statement_compat :
  X208Legacy.Pt_free_maximum_independent_set_polytime_statement <->
  Pt_free_maximum_independent_set_polytime_statement.
Proof.
rewrite /X208Legacy.Pt_free_maximum_independent_set_polytime_statement
  /Pt_free_maximum_independent_set_polytime_statement.
setoid_rewrite x208_polytime_mis_on_compat.
reflexivity.
Qed.

Lemma x29_stable_cover_compat (G : sgraph) (S : seq {set G}) :
  X29Legacy.x29_stable_cover S <-> x29_stable_cover S.
Proof.
rewrite /X29Legacy.x29_stable_cover /x29_stable_cover.
setoid_rewrite x29_stable_set_compat.
reflexivity.
Qed.

Lemma x29_normal_graph_compat (G : sgraph) :
  X29Legacy.x29_normal_graph G <-> x29_normal_graph G.
Proof.
rewrite /X29Legacy.x29_normal_graph /x29_normal_graph.
setoid_rewrite x29_stable_cover_compat.
reflexivity.
Qed.

Lemma no_c5_c7_complement_c7_normal_graph_statement_compat :
  X29Legacy.no_c5_c7_complement_c7_normal_graph_statement <->
  no_c5_c7_complement_c7_normal_graph_statement.
Proof.
rewrite /X29Legacy.no_c5_c7_complement_c7_normal_graph_statement /no_c5_c7_complement_c7_normal_graph_statement.
setoid_rewrite x29_normal_graph_compat.
reflexivity.
Qed.

(** Complete X169: the frozen token-sliding chain is rewritten against C13's frozen polytime chain, then C13's
    certificate; the same program and cost witnesses throughout. *)
Lemma x169_polytime_decides_TS_connectivity_original_compat (k D : nat) :
  X169Original.x169_polytime_decides_TS_connectivity k D <-> x169_polytime_decides_TS_connectivity k D.
Proof.
apply: (iff_trans _ (C13.x169_polytime_decides_TS_connectivity_compat k D)).
rewrite /X169Original.x169_polytime_decides_TS_connectivity /C13.Legacy.x169_polytime_decides_TS_connectivity
  /polytime_decides_graph_on /polytime_decides_on_class /decides_on_class.
setoid_rewrite x169_token_sliding_connected_compat.
reflexivity.
Qed.

Lemma token_sliding_chordal_clique_tree_degree_polytime_statement_original_compat :
  X169Original.token_sliding_chordal_clique_tree_degree_polytime_statement <->
  token_sliding_chordal_clique_tree_degree_polytime_statement.
Proof.
rewrite /X169Original.token_sliding_chordal_clique_tree_degree_polytime_statement
  /token_sliding_chordal_clique_tree_degree_polytime_statement.
setoid_rewrite x169_polytime_decides_TS_connectivity_original_compat.
reflexivity.
Qed.

(** Complete X29: the frozen normality chain is rewritten, then A6's certificate for its frozen complement. *)
Lemma no_c5_c7_complement_c7_normal_graph_statement_original_compat :
  X29Original.no_c5_c7_complement_c7_normal_graph_statement <->
  no_c5_c7_complement_c7_normal_graph_statement.
Proof.
rewrite /X29Original.no_c5_c7_complement_c7_normal_graph_statement.
setoid_rewrite x29_normal_graph_compat.
exact: A6.no_c5_c7_complement_c7_normal_graph_statement_compat.
Qed.
