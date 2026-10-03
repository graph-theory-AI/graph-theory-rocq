(** A11 minimum-degree lower bounds (extremal): the frozen X13/X30/XE1 bounds, X13's induced
    adapter and XE1's no-isolated-vertices bound, the two chains, the nine rows and the complete Originals.
    - [Legacy]: the bounds convert to [GTBase.base.min_degree_at_least]; X13's induced bound is
      [min_degree_at_least (induced S) d] and no isolated vertices is the bound 1.
    - [X13Legacy], [X30Legacy], [XE1Legacy], [XE2Legacy]: the chains and rows over these frozen bounds;
      every other helper stays live there.
    - [XE1Original], [XE2Original]: the complete rows.  #85 composes the frozen bound with A5's frozen
      containment; #545/#566/#567/#568/#570 compose the frozen no-isolated bound with A7's frozen count
      and sparse-set chain, A6's frozen Ramsey number and B4's frozen h5 (aliased, not imported).  Each
      converts to the earlier family's certificate, whose bridge it reuses.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/min_degree_at_least.spec.json. *)
From GTBase Require Import base.
From Extremal.conjectures Require Import X4 X13 X30 XE1 XE2.
From Extremal.migration Require subgraph_of complement edge_count consecutive_in_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Earlier families' certificate modules, aliased without Import: their module names coincide
    with this file's. *)
Module A5 := Extremal.migration.subgraph_of.
Module A6 := Extremal.migration.complement.
Module A7 := Extremal.migration.edge_count.
Module B4 := Extremal.migration.consecutive_in_cycle.

Module Legacy.

Definition x13_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x13_induced_min_degree_at_least
    (G : sgraph) (S : {set G}) (d : nat) : Prop :=
  forall v : induced S, d <= #|N(v)|.

Definition x30_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition xe1_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition xe1_no_isolated_vertices (G : sgraph) : Prop :=
  forall v : G, 0 < #|N(v)|.

End Legacy.

Module X13Legacy.

Definition bipartite_induced_min_degree_at_least
    (G : sgraph) (d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\
    bipartite (induced S) /\
    Legacy.x13_induced_min_degree_at_least S d.

Definition large_girth_min_degree_bipartite_induced_statement : Prop :=
  exists d0 g0 : nat,
    0 < d0 /\ 0 < g0 /\
    forall G : sgraph,
      0 < #|G| ->
      girth_geq G g0 ->
      Legacy.x13_min_degree_at_least G d0 ->
      bipartite_induced_min_degree_at_least G 3.

Definition min_degree_forces_large_clique_or_bipartite_induced_statement : Prop :=
  exists x2 x3 : nat -> nat,
    x13_unbounded x2 /\ x13_unbounded x3 /\
    (forall d : nat, 0 < x2 d /\ 0 < x3 d) /\
    forall (d : nat) (G : sgraph),
      0 < d -> 0 < #|G| ->
      Legacy.x13_min_degree_at_least G d ->
      x13_complete_subgraph_size_at_least G (x2 d) \/
      bipartite_induced_min_degree_at_least G (x3 d).

End X13Legacy.

Module X30Legacy.

Definition triangle_free_min_degree_log_bipartite_induced_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (d : nat) (G : sgraph),
      2 <= d ->
      0 < #|G| ->
      triangle_free G ->
      Legacy.x30_min_degree_at_least G d ->
      x30_bipartite_induced_log_min_degree G cnum cden d.

End X30Legacy.

Module XE1Legacy.

Definition c4_forcing_min_degree (n f : nat) : Prop :=
  (forall G : sgraph, #|G| = n -> Legacy.xe1_min_degree_at_least G f -> xe1_subgraph_of (cycle_graph 4) G) /\
  forall f' : nat,
    (forall G : sgraph, #|G| = n -> Legacy.xe1_min_degree_at_least G f' -> xe1_subgraph_of (cycle_graph 4) G) ->
    f <= f'.

Definition erdos_85_statement : Prop :=
  exists N : nat,
    forall n fn fn1 : nat,
      N <= n -> 4 <= n ->
      c4_forcing_min_degree n fn ->
      c4_forcing_min_degree n.+1 fn1 ->
      fn <= fn1.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    x4_edge_count G = m -> Legacy.xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    xe1_graph_ramsey_number G G RG ->
    xe1_graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, xe1_every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> xe1_graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      xe1_graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
      xe1_graph_ramsey_number G H R ->
      R <= C * m.

End XE1Legacy.

Module XE2Legacy.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
        xe1_graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

End XE2Legacy.

Module XE1Original.

Definition c4_forcing_min_degree (n f : nat) : Prop :=
  (forall G : sgraph, #|G| = n -> Legacy.xe1_min_degree_at_least G f -> A5.Legacy.xe1_subgraph_of (cycle_graph 4) G) /\
  forall f' : nat,
    (forall G : sgraph, #|G| = n -> Legacy.xe1_min_degree_at_least G f' -> A5.Legacy.xe1_subgraph_of (cycle_graph 4) G) ->
    f <= f'.

Definition erdos_85_statement : Prop :=
  exists N : nat,
    forall n fn fn1 : nat,
      N <= n -> 4 <= n ->
      XE1Original.c4_forcing_min_degree n fn ->
      XE1Original.c4_forcing_min_degree n.+1 fn1 ->
      fn <= fn1.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    A7.Legacy.x4_edge_count G = m -> Legacy.xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    A6.XE1Original.graph_ramsey_number G G RG ->
    A6.XE1Original.graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, A7.XE1Legacy.every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        A7.Legacy.x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ B4.XE1Legacy.h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        A7.Legacy.x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> A6.XE1Original.graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      A6.XE1Original.graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      A7.Legacy.x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
      A6.XE1Original.graph_ramsey_number G H R ->
      R <= C * m.

End XE1Original.

Module XE2Original.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        A7.Legacy.x4_edge_count H = m -> Legacy.xe1_no_isolated_vertices H ->
        A6.XE1Original.graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

End XE2Original.

Lemma x13_min_degree_at_least_compat (G : sgraph) (d : nat) :
  Legacy.x13_min_degree_at_least G d <->
  x13_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma x13_induced_min_degree_at_least_compat (G : sgraph) (S : {set G}) (d : nat) :
  Legacy.x13_induced_min_degree_at_least S d <->
  x13_induced_min_degree_at_least S d.
Proof. exact: iff_refl. Qed.

Lemma x30_min_degree_at_least_compat (G : sgraph) (d : nat) :
  Legacy.x30_min_degree_at_least G d <->
  x30_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma xe1_min_degree_at_least_compat (G : sgraph) (d : nat) :
  Legacy.xe1_min_degree_at_least G d <->
  xe1_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma xe1_no_isolated_vertices_compat (G : sgraph) :
  Legacy.xe1_no_isolated_vertices G <->
  xe1_no_isolated_vertices G.
Proof. exact: iff_refl. Qed.

Lemma x13_bipartite_induced_min_degree_at_least_compat (G : sgraph) (d : nat) :
  X13Legacy.bipartite_induced_min_degree_at_least G d <->
  x13_bipartite_induced_min_degree_at_least G d.
Proof. exact: iff_refl. Qed.

Lemma large_girth_min_degree_bipartite_induced_statement_compat :
  X13Legacy.large_girth_min_degree_bipartite_induced_statement <->
  large_girth_min_degree_bipartite_induced_statement.
Proof. exact: iff_refl. Qed.

Lemma min_degree_forces_large_clique_or_bipartite_induced_statement_compat :
  X13Legacy.min_degree_forces_large_clique_or_bipartite_induced_statement <->
  min_degree_forces_large_clique_or_bipartite_induced_statement.
Proof. exact: iff_refl. Qed.

Lemma triangle_free_min_degree_log_bipartite_induced_statement_compat :
  X30Legacy.triangle_free_min_degree_log_bipartite_induced_statement <->
  triangle_free_min_degree_log_bipartite_induced_statement.
Proof. exact: iff_refl. Qed.

Lemma xe1_c4_forcing_min_degree_compat (n f : nat) :
  XE1Legacy.c4_forcing_min_degree n f <->
  xe1_c4_forcing_min_degree n f.
Proof. exact: iff_refl. Qed.

Lemma erdos_85_statement_compat :
  XE1Legacy.erdos_85_statement <->
  erdos_85_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_545_statement_compat :
  XE1Legacy.erdos_545_statement <->
  erdos_545_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_566_statement_compat :
  XE1Legacy.erdos_566_statement <->
  erdos_566_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_567_statement_compat :
  XE1Legacy.erdos_567_statement <->
  erdos_567_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_568_statement_compat :
  XE1Legacy.erdos_568_statement <->
  erdos_568_statement.
Proof. exact: iff_refl. Qed.

Lemma erdos_570_statement_compat :
  XE2Legacy.erdos_570_statement <->
  erdos_570_statement.
Proof. exact: iff_refl. Qed.

Lemma c4_forcing_min_degree_original_compat (n f : nat) :
  XE1Original.c4_forcing_min_degree n f <->
  xe1_c4_forcing_min_degree n f.
Proof. exact: A5.c4_forcing_min_degree_compat. Qed.

Lemma erdos_85_statement_original_compat :
  XE1Original.erdos_85_statement <->
  erdos_85_statement.
Proof. exact: A5.erdos_85_statement_compat. Qed.

Lemma erdos_545_statement_original_compat :
  XE1Original.erdos_545_statement <->
  erdos_545_statement.
Proof. exact: A7.erdos_545_statement_original_compat. Qed.

Lemma erdos_566_statement_original_compat :
  XE1Original.erdos_566_statement <->
  erdos_566_statement.
Proof. exact: A7.erdos_566_statement_original_compat. Qed.

Lemma erdos_567_statement_original_compat :
  XE1Original.erdos_567_statement <->
  erdos_567_statement.
Proof. exact: A7.erdos_567_statement_original_compat. Qed.

Lemma erdos_568_statement_original_compat :
  XE1Original.erdos_568_statement <->
  erdos_568_statement.
Proof. exact: A7.erdos_568_statement_original_compat. Qed.

Lemma erdos_570_statement_original_compat :
  XE2Original.erdos_570_statement <->
  erdos_570_statement.
Proof. exact: A7.erdos_570_statement_original_compat. Qed.
