(** A23 hypercubes (extremal): the frozen XE1 hypercube, Erdos #1035 and #567, and their complete rows.  Baseline,
    hashes and exact substitutions are recorded in meta/migration_reports/hypercubes.spec.json.
    - [Legacy]: the local Fixpoint ([Q_0 = 'K_1], [Q_(d+1) = 'K_2 □ Q_d]) equals [GTBase.hypercubes.product_hypercube d]
      as a graph, by induction on the dimension: the same record on the same nested carrier.
    - [XE1Legacy]: #1035 (c, d before n and G, 0 < c < d, the cleared degree bound, Q_n containment) and #567 (the
      literal equalities [G = Q_3] or [G = KB 3 3] or H_5, the uniform Ramsey bound, the no-isolated guard) over the
      frozen cube; A5's subgraph, A6's Ramsey, A7's edge count, A11's no-isolated and B4's H_5 stay live here.
    - [XE1Original] (texts at the pre-migration 9e03072): #1035 over A5's frozen subgraph, and #567 extending A11's
      complete row (A7's edge count, A11's no-isolated, A6's Ramsey/complement/A5 chain, B4's H_5 cycle), each with the
      frozen cube.  The earlier modules are aliased, not imported; their certificates are reused. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base hypercubes.
From Extremal.conjectures Require Import X4 XE1.
From Extremal.migration Require subgraph_of complement edge_count consecutive_in_cycle min_degree_at_least.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A5's, A6's, A7's, B4's and A11's certificate modules, aliased without Import: their module names coincide with
    this file's. *)
Module A5 := Extremal.migration.subgraph_of.
Module A6 := Extremal.migration.complement.
Module A7 := Extremal.migration.edge_count.
Module B4 := Extremal.migration.consecutive_in_cycle.
Module A11 := Extremal.migration.min_degree_at_least.

Module Legacy.

Fixpoint xe1_hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (xe1_hypercube d')
  end.

End Legacy.

Module XE1Legacy.

Definition erdos_1035_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall n : nat, forall G : sgraph,
      #|G| = 2 ^ n ->
      (forall v : G, d * #|N(v)| > (d - c) * 2 ^ n) ->
      xe1_subgraph_of (Legacy.xe1_hypercube n) G.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = Legacy.xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

End XE1Legacy.

Module XE1Original.

Definition erdos_1035_statement : Prop :=
  exists c d : nat,
    0 < c /\ c < d /\
    forall n : nat, forall G : sgraph,
      #|G| = 2 ^ n ->
      (forall v : G, d * #|N(v)| > (d - c) * 2 ^ n) ->
      A5.Legacy.xe1_subgraph_of (Legacy.xe1_hypercube n) G.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = Legacy.xe1_hypercube 3 \/ G = KB 3 3 \/ B4.XE1Legacy.h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        A7.Legacy.x4_edge_count H = m -> A11.Legacy.xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number G H R ->
        R <= C * m.

End XE1Original.

(** The same graph record: the frozen Fixpoint against [GTBase.hypercubes.product_hypercube], by induction. *)
Lemma xe1_hypercube_compat (d : nat) :
  Legacy.xe1_hypercube d = xe1_hypercube d.
Proof.
elim: d => [//|d IH].
by rewrite /= IH.
Qed.

Lemma erdos_1035_statement_compat :
  XE1Legacy.erdos_1035_statement <-> erdos_1035_statement.
Proof.
rewrite /XE1Legacy.erdos_1035_statement.
setoid_rewrite xe1_hypercube_compat.
reflexivity.
Qed.

Lemma erdos_567_statement_compat :
  XE1Legacy.erdos_567_statement <-> erdos_567_statement.
Proof.
rewrite /XE1Legacy.erdos_567_statement.
setoid_rewrite xe1_hypercube_compat.
reflexivity.
Qed.

(** Complete rows: the frozen cube is rewritten, then A5's row certificate and A11's complete-row certificate. *)
Lemma erdos_1035_statement_original_compat :
  XE1Original.erdos_1035_statement <-> erdos_1035_statement.
Proof.
rewrite /XE1Original.erdos_1035_statement.
setoid_rewrite xe1_hypercube_compat.
exact: A5.erdos_1035_statement_compat.
Qed.

Lemma erdos_567_statement_original_compat :
  XE1Original.erdos_567_statement <-> erdos_567_statement.
Proof.
rewrite /XE1Original.erdos_567_statement.
setoid_rewrite xe1_hypercube_compat.
exact: A11.erdos_567_statement_original_compat.
Qed.
