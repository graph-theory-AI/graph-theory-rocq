(** A20 stable sets (extremal): the frozen X56, X97 and XE1 stable sets, the X56 homogeneous set, X97's maximum and
    hitting chain, XE1's dormant fixed-size consumer, the X56, X97, XE1 #802 and XE2 #22/#73/#801 rows, and the complete
    X56, #802, #22 and #801 rows.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/stable_sets.spec.json.
    - [Legacy]: X56's and XE1's [x -- y -> False] and X97's distinct-vertex [x != y -> ~~ (x -- y)] are
      equivalent to upstream [stable S] by [GTBase.stable_sets.stable_noedgeP] and [stable_distinctP] (iffs, not
      conversions; the unequal-vertex guard is redundant by irreflexivity).
    - [X56Legacy], [X97Legacy], [XE1Legacy], [XE2Legacy]: the chains and rows over the frozen helpers.  X97's maximum is
      maximum cardinality, not inclusion maximality; all positivity guards, thresholds, the alpha and degree-sum
      hypotheses, natural subtraction, [trunc_log], the universal subset premises and the induced deletion are verbatim.
      [xe1_has_independent_set] reaches no row and is frozen as a dormant consumer.  A1's induced-freeness, A6's
      complement, A5's subgraph relation and A7's edge count stay live in these per-row copies.
    - [X56Original], [XE1Original], [XE2Original] (texts at the pre-migration 9e03072): X56 over A1's and A6's frozen
      helpers and the frozen homogeneous set; #802 over A5's frozen subgraph relation; #22 over A7's frozen edge count
      and A5's frozen subgraph relation; #801 over A7's frozen edge count; each over the frozen stable set.  A1's,
      A5's, A6's and A7's modules are aliased, not imported; the bridges reuse their certificates. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base stable_sets.
From Extremal.conjectures Require Import X4 X56 X97 XE1 XE2.
From Extremal.migration Require induced_free subgraph_of complement edge_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A1's, A5's, A6's and A7's certificate modules, aliased without Import: their module names coincide with this
    file's. *)
Module A1 := Extremal.migration.induced_free.
Module A5 := Extremal.migration.subgraph_of.
Module A6 := Extremal.migration.complement.
Module A7 := Extremal.migration.edge_count.

Module Legacy.

Definition x56_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition x97_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition xe1_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

End Legacy.

Module X56Legacy.

Definition x56_homogeneous_set (G : sgraph) (S : {set G}) : Prop :=
  clique S \/ Legacy.x56_stable_set S.

Definition c8_complement_c8_erdos_hajnal_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      x56_induced_free G (cycle_graph 8) ->
      x56_induced_free G (x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        X56Legacy.x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.

End X56Legacy.

Module X97Legacy.

Definition x97_maximum_independent_set (G : sgraph) (S : {set G}) : Prop :=
  Legacy.x97_stable_set S /\
  forall T : {set G}, Legacy.x97_stable_set T -> #|T| <= #|S|.

Definition x97_hits_all_maximum_independent_sets
    (G : sgraph) (X : {set G}) : Prop :=
  forall S : {set G},
    X97Legacy.x97_maximum_independent_set S ->
    ~~ [disjoint X & S].

Definition x97_hitting_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists X : {set G},
    #|X| <= k /\ X97Legacy.x97_hits_all_maximum_independent_sets X.

Definition bollobas_erdos_tuza_independent_set_hitting_statement : Prop :=
  forall delta_num delta_den eps_num eps_den : nat,
    0 < delta_num ->
    0 < delta_den ->
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        delta_den * α([set: G]) >= delta_num * n ->
        exists eta : nat,
          X97Legacy.x97_hitting_number_at_most G eta /\
          eps_den * eta <= eps_num * n.

End X97Legacy.

Module XE1Legacy.

Definition xe1_has_independent_set (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, Legacy.xe1_stable_set S /\ #|S| = k.

Definition erdos_802_statement : Prop :=
  forall r : nat, exists C : nat,
    0 < C /\
    forall (G : sgraph) (n t : nat),
      ~ xe1_subgraph_of 'K_r G ->
      #|G| = n ->
      \sum_(v in G) #|N(v)| <= t * #|G| ->
      exists A : {set G},
        Legacy.xe1_stable_set A /\ C * t * #|A| >= n * trunc_log 2 t.

End XE1Legacy.

Module XE2Legacy.

Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * x4_edge_count G >= n ^ 2 /\
          ~ xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, Legacy.xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

Definition erdos_73_statement : Prop :=
  forall k : nat, exists C : nat,
    forall G : sgraph,
      (forall S : {set G}, exists A : {set G},
          A \subset S /\ Legacy.xe1_stable_set A /\ 2 * #|A| + k >= #|S|) ->
      exists X : {set G}, #|X| <= C /\ bipartite (induced (~: X)).

Definition erdos_801_statement : Prop :=
  exists C N : nat,
    0 < C /\
    forall (G : sgraph) (n s : nat),
      N <= n ->
      #|G| = n ->
      xe1_sqrt_floor n s ->
      (forall A : {set G}, Legacy.xe1_stable_set A -> #|A| <= s) ->
      exists S : {set G},
        #|S| <= s /\ C * x4_edge_count (induced S) >= s * trunc_log 2 n.

End XE2Legacy.

Module X56Original.

Definition c8_complement_c8_erdos_hajnal_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      A1.Legacy.x56_induced_free G (cycle_graph 8) ->
      A1.Legacy.x56_induced_free G (A6.Legacy.x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        X56Legacy.x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.

End X56Original.

Module XE1Original.

Definition erdos_802_statement : Prop :=
  forall r : nat, exists C : nat,
    0 < C /\
    forall (G : sgraph) (n t : nat),
      ~ A5.Legacy.xe1_subgraph_of 'K_r G ->
      #|G| = n ->
      \sum_(v in G) #|N(v)| <= t * #|G| ->
      exists A : {set G},
        Legacy.xe1_stable_set A /\ C * t * #|A| >= n * trunc_log 2 t.

End XE1Original.

Module XE2Original.

Definition erdos_22_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num -> 0 < eps_den ->
    exists N : nat,
      forall n : nat, N <= n ->
        exists G : sgraph,
          #|G| = n /\
          8 * A7.Legacy.x4_edge_count G >= n ^ 2 /\
          ~ A5.Legacy.xe1_subgraph_of 'K_4 G /\
          forall A : {set G}, Legacy.xe1_stable_set A -> eps_den * #|A| <= eps_num * n.

Definition erdos_801_statement : Prop :=
  exists C N : nat,
    0 < C /\
    forall (G : sgraph) (n s : nat),
      N <= n ->
      #|G| = n ->
      xe1_sqrt_floor n s ->
      (forall A : {set G}, Legacy.xe1_stable_set A -> #|A| <= s) ->
      exists S : {set G},
        #|S| <= s /\ C * A7.Legacy.x4_edge_count (induced S) >= s * trunc_log 2 n.

End XE2Original.

(** Not conversions: the raw presentations against the upstream Boolean, by reflection. *)
Lemma x56_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x56_stable_set S <-> x56_stable_set S.
Proof.
exact: (rwP (stable_noedgeP S)).
Qed.

Lemma x97_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.x97_stable_set S <-> x97_stable_set S.
Proof.
exact: (rwP (stable_distinctP S)).
Qed.

Lemma xe1_stable_set_compat (G : sgraph) (S : {set G}) :
  Legacy.xe1_stable_set S <-> xe1_stable_set S.
Proof.
exact: (rwP (stable_noedgeP S)).
Qed.

Lemma x56_homogeneous_set_compat (G : sgraph) (S : {set G}) :
  X56Legacy.x56_homogeneous_set S <-> x56_homogeneous_set S.
Proof.
rewrite /X56Legacy.x56_homogeneous_set /x56_homogeneous_set.
setoid_rewrite x56_stable_set_compat.
reflexivity.
Qed.

Lemma c8_complement_c8_erdos_hajnal_statement_compat :
  X56Legacy.c8_complement_c8_erdos_hajnal_statement <->
  c8_complement_c8_erdos_hajnal_statement.
Proof.
rewrite /X56Legacy.c8_complement_c8_erdos_hajnal_statement /c8_complement_c8_erdos_hajnal_statement.
setoid_rewrite x56_homogeneous_set_compat.
reflexivity.
Qed.

Lemma x97_maximum_independent_set_compat (G : sgraph) (S : {set G}) :
  X97Legacy.x97_maximum_independent_set S <-> x97_maximum_independent_set S.
Proof.
rewrite /X97Legacy.x97_maximum_independent_set /x97_maximum_independent_set.
setoid_rewrite x97_stable_set_compat.
reflexivity.
Qed.

Lemma x97_hits_all_maximum_independent_sets_compat (G : sgraph) (X : {set G}) :
  X97Legacy.x97_hits_all_maximum_independent_sets X <-> x97_hits_all_maximum_independent_sets X.
Proof.
rewrite /X97Legacy.x97_hits_all_maximum_independent_sets /x97_hits_all_maximum_independent_sets.
setoid_rewrite x97_maximum_independent_set_compat.
reflexivity.
Qed.

Lemma x97_hitting_number_at_most_compat (G : sgraph) (k : nat) :
  X97Legacy.x97_hitting_number_at_most G k <-> x97_hitting_number_at_most G k.
Proof.
rewrite /X97Legacy.x97_hitting_number_at_most /x97_hitting_number_at_most.
setoid_rewrite x97_hits_all_maximum_independent_sets_compat.
reflexivity.
Qed.

Lemma bollobas_erdos_tuza_independent_set_hitting_statement_compat :
  X97Legacy.bollobas_erdos_tuza_independent_set_hitting_statement <->
  bollobas_erdos_tuza_independent_set_hitting_statement.
Proof.
rewrite /X97Legacy.bollobas_erdos_tuza_independent_set_hitting_statement
  /bollobas_erdos_tuza_independent_set_hitting_statement.
setoid_rewrite x97_hitting_number_at_most_compat.
reflexivity.
Qed.

(** The dormant fixed-size consumer: no row reaches it. *)
Lemma xe1_has_independent_set_compat (G : sgraph) (k : nat) :
  XE1Legacy.xe1_has_independent_set G k <-> xe1_has_independent_set G k.
Proof.
rewrite /XE1Legacy.xe1_has_independent_set /xe1_has_independent_set.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

Lemma erdos_802_statement_compat :
  XE1Legacy.erdos_802_statement <-> erdos_802_statement.
Proof.
rewrite /XE1Legacy.erdos_802_statement /erdos_802_statement.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

Lemma erdos_22_statement_compat :
  XE2Legacy.erdos_22_statement <-> erdos_22_statement.
Proof.
rewrite /XE2Legacy.erdos_22_statement /erdos_22_statement.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

Lemma erdos_73_statement_compat :
  XE2Legacy.erdos_73_statement <-> erdos_73_statement.
Proof.
rewrite /XE2Legacy.erdos_73_statement /erdos_73_statement.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

Lemma erdos_801_statement_compat :
  XE2Legacy.erdos_801_statement <-> erdos_801_statement.
Proof.
rewrite /XE2Legacy.erdos_801_statement /erdos_801_statement.
setoid_rewrite xe1_stable_set_compat.
reflexivity.
Qed.

(** Complete rows: the frozen stable-set pieces are rewritten, then the earlier certificates of A6 (X56, over A1 and
    A6), A5 (#802) and A7 (#22 over A5 and A7, #801). *)
Lemma c8_complement_c8_erdos_hajnal_statement_original_compat :
  X56Original.c8_complement_c8_erdos_hajnal_statement <->
  c8_complement_c8_erdos_hajnal_statement.
Proof.
rewrite /X56Original.c8_complement_c8_erdos_hajnal_statement.
setoid_rewrite x56_homogeneous_set_compat.
exact: A6.c8_complement_c8_erdos_hajnal_statement_original_compat.
Qed.

Lemma erdos_802_statement_original_compat :
  XE1Original.erdos_802_statement <-> erdos_802_statement.
Proof.
rewrite /XE1Original.erdos_802_statement.
setoid_rewrite xe1_stable_set_compat.
exact: A5.erdos_802_statement_compat.
Qed.

Lemma erdos_22_statement_original_compat :
  XE2Original.erdos_22_statement <-> erdos_22_statement.
Proof.
rewrite /XE2Original.erdos_22_statement.
setoid_rewrite xe1_stable_set_compat.
exact: A7.erdos_22_statement_original_compat.
Qed.

Lemma erdos_801_statement_original_compat :
  XE2Original.erdos_801_statement <-> erdos_801_statement.
Proof.
rewrite /XE2Original.erdos_801_statement.
setoid_rewrite xe1_stable_set_compat.
exact: A7.erdos_801_statement_compat.
Qed.
