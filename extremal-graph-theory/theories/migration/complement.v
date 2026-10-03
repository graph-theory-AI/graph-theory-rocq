(** * Extremal.migration.complement -- frozen ordinary graph-complement certificates

    Batch A, family A6 (ordinary complement), X56 and the extremal XE1/XE2 Ramsey rows.  [Legacy] freezes each relation
    [(x != y) && ~~ (x -- y)], its symmetry and irreflexivity proof scripts and the [SGraph]
    built from them, verbatim at 49ddc03 except that references to the frozen names are
    [Legacy.]-qualified.  The live helpers now unfold to upstream [compl_rel] and [compl]; the
    relations agree by conversion, and the graphs are related by the identity isomorphism
    ([compl_eq_diso]), which does not equate the opaque proof fields.  Row certificates move
    each statement along that isomorphism: as a pattern of [induced_free], as the host of an
    induced cycle or of an ordinary subgraph, or through the same witness of a class.
    The regeneration spec is meta/migration_reports/complement.spec.json. *)

From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Extremal.conjectures Require Import X4 X56 XE1 XE2.
From Extremal.migration Require induced_free subgraph_of consecutive_in_cycle.

(** A5's certificate module, aliased so that frozen references read [A5.Legacy.xe1_subgraph_of]. *)
Module A5 := Extremal.migration.subgraph_of.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

Module Legacy.

Definition x56_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma x56_complement_sym (G : sgraph) : symmetric (@Legacy.x56_complement_rel G).
Proof. by move=> x y; rewrite /Legacy.x56_complement_rel eq_sym sgP. Qed.

Lemma x56_complement_irrefl (G : sgraph) : irreflexive (@Legacy.x56_complement_rel G).
Proof. by move=> x; rewrite /Legacy.x56_complement_rel eqxx. Qed.

Definition x56_complement (G : sgraph) : sgraph :=
  SGraph (@Legacy.x56_complement_sym G) (@Legacy.x56_complement_irrefl G).

Definition xe1_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma xe1_complement_sym (G : sgraph) : symmetric (@Legacy.xe1_complement_rel G).
Proof. by move=> x y; rewrite /Legacy.xe1_complement_rel eq_sym sgP. Qed.

Lemma xe1_complement_irrefl (G : sgraph) : irreflexive (@Legacy.xe1_complement_rel G).
Proof. by move=> x; rewrite /Legacy.xe1_complement_rel eqxx. Qed.

Definition xe1_complement_graph (G : sgraph) : sgraph :=
  SGraph (@Legacy.xe1_complement_sym G) (@Legacy.xe1_complement_irrefl G).

End Legacy.

Module X56Legacy.

Definition c8_complement_c8_erdos_hajnal_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      x56_induced_free G (cycle_graph 8) ->
      x56_induced_free G (Legacy.x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.

End X56Legacy.

Module X56Original.

Definition c8_complement_c8_erdos_hajnal_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      Extremal.migration.induced_free.Legacy.x56_induced_free G (cycle_graph 8) ->
      Extremal.migration.induced_free.Legacy.x56_induced_free G (Legacy.x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.

End X56Original.

Module XE1Legacy.

Definition graph_ramsey (H K : sgraph) (R : nat) : Prop :=
  forall G : sgraph, #|G| = R ->
    xe1_subgraph_of H G \/ xe1_subgraph_of K (Legacy.xe1_complement_graph G).

Definition graph_ramsey_number (H K : sgraph) (R : nat) : Prop :=
  graph_ramsey H K R /\
  forall R' : nat, graph_ramsey H K R' -> R <= R'.

Definition diagonal_ramsey_number (H : sgraph) (R : nat) : Prop :=
  graph_ramsey_number H H R.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    graph_ramsey_number G G RG ->
    graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      graph_ramsey_number T (KB m1 m2) RTB ->
      graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

Definition erdos_552_statement : Prop :=
  forall c M : nat, exists n R s : nat,
    M <= n /\
    xe1_sqrt_floor n s /\
    graph_ramsey_number (cycle_graph 4) (KB 1 n) R /\
    R + c <= n + s.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, xe1_every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ xe1_h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      graph_ramsey_number G H R ->
      R <= C * m.

Definition erdos_812_statement : Prop :=
  (exists cnum cden N : nat, 0 < cnum /\ 0 < cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      graph_ramsey_number 'K_n 'K_n Rn ->
      graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      cden * Rn1 >= (cden + cnum) * Rn) /\
  (exists Cnum Cden N : nat, 0 < Cnum /\ 0 < Cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      graph_ramsey_number 'K_n 'K_n Rn ->
      graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      Cden * Rn + Cnum * n ^ 2 <= Cden * Rn1).

Definition erdos_87_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall (k RG RK : nat) (G : sgraph),
      N <= k ->
      χ([set: G]) = k ->
      diagonal_ramsey_number G RG ->
      graph_ramsey_number 'K_k 'K_k RK ->
      cden * RG >= cnum * RK.

End XE1Legacy.

Module XE2Legacy.

Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    xe1_tree T -> #|T| = n ->
    XE1Legacy.diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> xe2_bipartition_sizes T k (2 * k) ->
    XE1Legacy.diagonal_ramsey_number T R ->
    R = 4 * k - 1.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        XE1Legacy.graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

Definition erdos_800_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n R : nat),
      #|G| = n ->
      (forall x y : G, x -- y -> #|N(x)| < 3 \/ #|N(y)| < 3) ->
      XE1Legacy.diagonal_ramsey_number G R ->
      R <= C * n.

End XE2Legacy.

Module XE1Original.

Definition graph_ramsey (H K : sgraph) (R : nat) : Prop :=
  forall G : sgraph, #|G| = R ->
    A5.Legacy.xe1_subgraph_of H G \/ A5.Legacy.xe1_subgraph_of K (Legacy.xe1_complement_graph G).

Definition graph_ramsey_number (H K : sgraph) (R : nat) : Prop :=
  graph_ramsey H K R /\
  forall R' : nat, graph_ramsey H K R' -> R <= R'.

Definition diagonal_ramsey_number (H : sgraph) (R : nat) : Prop :=
  graph_ramsey_number H H R.

Definition erdos_545_statement : Prop :=
  forall (m n t RG RH : nat) (G H : sgraph),
    x4_edge_count G = m -> xe1_no_isolated_vertices G ->
    m = 'C(n, 2) + t -> t < n ->
    xe1_complete_plus_vertex H n t ->
    graph_ramsey_number G G RG ->
    graph_ramsey_number H H RH ->
    RG <= RH.

Definition erdos_550_statement : Prop :=
  forall (k : nat) (sizes : 'I_k -> nat) (m1 m2 : nat),
    2 <= k ->
    (forall i : 'I_k, 0 < sizes i) ->
    xe1_two_smallest_part_sizes sizes m1 m2 ->
    exists N : nat,
    forall (n RTB RTG : nat) (T G : sgraph),
      N <= n -> xe1_tree T -> #|T| = n ->
      xe1_complete_multipartite_with_sizes G sizes ->
      graph_ramsey_number T (KB m1 m2) RTB ->
      graph_ramsey_number T G RTG ->
      RTG <= (χ([set: G]) - 1) * (RTB - 1) + m1.

Definition erdos_552_statement : Prop :=
  forall c M : nat, exists n R s : nat,
    M <= n /\
    xe1_sqrt_floor n s /\
    graph_ramsey_number (cycle_graph 4) (KB 1 n) R /\
    R + c <= n + s.

Definition erdos_566_statement : Prop :=
  forall G : sgraph,
    (forall k : nat, xe1_every_k_set_sparse G k) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_567_statement : Prop :=
  forall G : sgraph,
    (G = xe1_hypercube 3 \/ G = KB 3 3 \/ Extremal.migration.consecutive_in_cycle.XE1Legacy.h5_graph G) ->
    exists C : nat,
      forall (H : sgraph) (m R : nat),
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        graph_ramsey_number G H R ->
        R <= C * m.

Definition erdos_568_statement : Prop :=
  forall G : sgraph,
    (exists C1 : nat, forall (n R : nat) (T : sgraph),
      xe1_tree T -> #|T| = n -> graph_ramsey_number G T R -> R <= C1 * n) ->
    (exists C2 : nat, forall (n R : nat),
      graph_ramsey_number G 'K_n R -> R <= C2 * n ^ 2) ->
    exists C : nat, forall (H : sgraph) (m R : nat),
      x4_edge_count H = m -> xe1_no_isolated_vertices H ->
      graph_ramsey_number G H R ->
      R <= C * m.

Definition erdos_812_statement : Prop :=
  (exists cnum cden N : nat, 0 < cnum /\ 0 < cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      graph_ramsey_number 'K_n 'K_n Rn ->
      graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      cden * Rn1 >= (cden + cnum) * Rn) /\
  (exists Cnum Cden N : nat, 0 < Cnum /\ 0 < Cden /\
    forall n Rn Rn1 : nat,
      N <= n ->
      graph_ramsey_number 'K_n 'K_n Rn ->
      graph_ramsey_number 'K_n.+1 'K_n.+1 Rn1 ->
      Cden * Rn + Cnum * n ^ 2 <= Cden * Rn1).

Definition erdos_87_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall (k RG RK : nat) (G : sgraph),
      N <= k ->
      χ([set: G]) = k ->
      diagonal_ramsey_number G RG ->
      graph_ramsey_number 'K_k 'K_k RK ->
      cden * RG >= cnum * RK.

End XE1Original.

Module XE2Original.

Definition erdos_547_statement : Prop :=
  forall (n R : nat) (T : sgraph),
    2 <= n ->
    xe1_tree T -> #|T| = n ->
    XE1Original.diagonal_ramsey_number T R ->
    R <= 2 * n - 2.

Definition erdos_549_statement : Prop :=
  forall (k R : nat) (T : sgraph),
    xe1_tree T -> xe2_bipartition_sizes T k (2 * k) ->
    XE1Original.diagonal_ramsey_number T R ->
    R = 4 * k - 1.

Definition erdos_570_statement : Prop :=
  forall k : nat, 3 <= k ->
    exists M : nat,
      forall (H : sgraph) (m R : nat),
        M <= m ->
        x4_edge_count H = m -> xe1_no_isolated_vertices H ->
        XE1Original.graph_ramsey_number (cycle_graph k) H R ->
        R <= 2 * m + ((k - 1) %/ 2).

Definition erdos_800_statement : Prop :=
  exists C : nat,
    forall (G : sgraph) (n R : nat),
      #|G| = n ->
      (forall x y : G, x -- y -> #|N(x)| < 3 \/ #|N(y)| < 3) ->
      XE1Original.diagonal_ramsey_number G R ->
      R <= C * n.

End XE2Original.

(** ** Helper certificates *)

Lemma x56_complement_rel_compat (G : sgraph) : @Legacy.x56_complement_rel G =2 @x56_complement_rel G.
Proof. by move=> x y. Qed.

Lemma x56_complement_compat (G : sgraph) :
  @edge_rel (Legacy.x56_complement G) =2 @edge_rel (x56_complement G).
Proof. by move=> x y. Qed.

(** The identity is an isomorphism of the frozen and live complements. *)
Lemma x56_complement_diso (G : sgraph) : Legacy.x56_complement G ≃ x56_complement G.
Proof. by rewrite /Legacy.x56_complement; apply: compl_eq_diso => x y. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen proofs is isomorphic,
    through the identity, to the one built from the retained live lemmas (no proof-term claim). *)
Lemma x56_complement_proofs_compat (G : sgraph) :
  SGraph (@Legacy.x56_complement_sym G) (@Legacy.x56_complement_irrefl G) ≃ SGraph (@x56_complement_sym G) (@x56_complement_irrefl G).
Proof. by apply: eq_diso => x y. Qed.

Lemma xe1_complement_rel_compat (G : sgraph) : @Legacy.xe1_complement_rel G =2 @xe1_complement_rel G.
Proof. by move=> x y. Qed.

Lemma xe1_complement_graph_compat (G : sgraph) :
  @edge_rel (Legacy.xe1_complement_graph G) =2 @edge_rel (xe1_complement_graph G).
Proof. by move=> x y. Qed.

(** The identity is an isomorphism of the frozen and live complements. *)
Lemma xe1_complement_diso (G : sgraph) : Legacy.xe1_complement_graph G ≃ xe1_complement_graph G.
Proof. by rewrite /Legacy.xe1_complement_graph; apply: compl_eq_diso => x y. Qed.

(** Graph-construction certificate: the [SGraph] built from the frozen proofs is isomorphic,
    through the identity, to the one built from the retained live lemmas (no proof-term claim). *)
Lemma xe1_complement_proofs_compat (G : sgraph) :
  SGraph (@Legacy.xe1_complement_sym G) (@Legacy.xe1_complement_irrefl G) ≃ SGraph (@xe1_complement_sym G) (@xe1_complement_irrefl G).
Proof. by apply: eq_diso => x y. Qed.


(** ** X56: the complement is the forbidden PATTERN of induced_free *)

Lemma c8_complement_c8_erdos_hajnal_statement_compat :
  X56Legacy.c8_complement_c8_erdos_hajnal_statement <-> c8_complement_c8_erdos_hajnal_statement.
Proof.
split=> -[c [c0 h]]; exists c; split=> [//|G G0 f8 fc8]; apply: (h G G0 f8).
- exact: induced_free_diso (diso_sym (x56_complement_diso _)) fc8.
- exact: induced_free_diso (x56_complement_diso _) fc8.
Qed.

(** Before A1 and A6: A1's frozen induced-free helper and the frozen complement. *)
Lemma c8_complement_c8_erdos_hajnal_statement_original_compat :
  X56Original.c8_complement_c8_erdos_hajnal_statement <-> c8_complement_c8_erdos_hajnal_statement.
Proof.
rewrite -c8_complement_c8_erdos_hajnal_statement_compat.
rewrite /X56Original.c8_complement_c8_erdos_hajnal_statement /X56Legacy.c8_complement_c8_erdos_hajnal_statement.
by setoid_rewrite Extremal.migration.induced_free.x56_induced_free_compat; reflexivity.
Qed.

(** ** XE1 Ramsey chain: the complement is the HOST of the second subgraph alternative *)

Lemma xe1_complement_subgraph_compat (K G : sgraph) :
  xe1_subgraph_of K (Legacy.xe1_complement_graph G) <-> xe1_subgraph_of K (xe1_complement_graph G).
Proof.
split; apply: has_subgraph_host_diso; first exact: xe1_complement_diso.
exact: diso_sym (xe1_complement_diso G).
Qed.

Lemma graph_ramsey_compat (H K : sgraph) (R : nat) :
  XE1Legacy.graph_ramsey H K R <-> xe1_graph_ramsey H K R.
Proof. by rewrite /XE1Legacy.graph_ramsey /xe1_graph_ramsey; setoid_rewrite xe1_complement_subgraph_compat; reflexivity. Qed.

Lemma graph_ramsey_number_compat (H K : sgraph) (R : nat) :
  XE1Legacy.graph_ramsey_number H K R <-> xe1_graph_ramsey_number H K R.
Proof. by rewrite /XE1Legacy.graph_ramsey_number /xe1_graph_ramsey_number; setoid_rewrite graph_ramsey_compat; reflexivity. Qed.

Lemma diagonal_ramsey_number_compat (H : sgraph) (R : nat) :
  XE1Legacy.diagonal_ramsey_number H R <-> xe1_diagonal_ramsey_number H R.
Proof. by rewrite /XE1Legacy.diagonal_ramsey_number /xe1_diagonal_ramsey_number; setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

(** Before A5 and A6: A5's frozen subgraph helper and A6's frozen complement. *)
Lemma graph_ramsey_original_compat (H K : sgraph) (R : nat) :
  XE1Original.graph_ramsey H K R <-> xe1_graph_ramsey H K R.
Proof.
rewrite -graph_ramsey_compat /XE1Original.graph_ramsey /XE1Legacy.graph_ramsey.
by setoid_rewrite A5.xe1_subgraph_of_compat; reflexivity.
Qed.

Lemma graph_ramsey_number_original_compat (H K : sgraph) (R : nat) :
  XE1Original.graph_ramsey_number H K R <-> xe1_graph_ramsey_number H K R.
Proof. by rewrite /XE1Original.graph_ramsey_number /xe1_graph_ramsey_number; setoid_rewrite graph_ramsey_original_compat; reflexivity. Qed.

Lemma diagonal_ramsey_number_original_compat (H : sgraph) (R : nat) :
  XE1Original.diagonal_ramsey_number H R <-> xe1_diagonal_ramsey_number H R.
Proof. by rewrite /XE1Original.diagonal_ramsey_number /xe1_diagonal_ramsey_number; setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_545_statement_compat :
  XE1Legacy.erdos_545_statement <-> erdos_545_statement.
Proof. rewrite /XE1Legacy.erdos_545_statement /erdos_545_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_550_statement_compat :
  XE1Legacy.erdos_550_statement <-> erdos_550_statement.
Proof. rewrite /XE1Legacy.erdos_550_statement /erdos_550_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_552_statement_compat :
  XE1Legacy.erdos_552_statement <-> erdos_552_statement.
Proof. rewrite /XE1Legacy.erdos_552_statement /erdos_552_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_566_statement_compat :
  XE1Legacy.erdos_566_statement <-> erdos_566_statement.
Proof. rewrite /XE1Legacy.erdos_566_statement /erdos_566_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_567_statement_compat :
  XE1Legacy.erdos_567_statement <-> erdos_567_statement.
Proof. rewrite /XE1Legacy.erdos_567_statement /erdos_567_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_568_statement_compat :
  XE1Legacy.erdos_568_statement <-> erdos_568_statement.
Proof. rewrite /XE1Legacy.erdos_568_statement /erdos_568_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_812_statement_compat :
  XE1Legacy.erdos_812_statement <-> erdos_812_statement.
Proof. rewrite /XE1Legacy.erdos_812_statement /erdos_812_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_87_statement_compat :
  XE1Legacy.erdos_87_statement <-> erdos_87_statement.
Proof. rewrite /XE1Legacy.erdos_87_statement /erdos_87_statement; try setoid_rewrite graph_ramsey_number_compat; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_547_statement_compat :
  XE2Legacy.erdos_547_statement <-> erdos_547_statement.
Proof. rewrite /XE2Legacy.erdos_547_statement /erdos_547_statement; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_549_statement_compat :
  XE2Legacy.erdos_549_statement <-> erdos_549_statement.
Proof. rewrite /XE2Legacy.erdos_549_statement /erdos_549_statement; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_570_statement_compat :
  XE2Legacy.erdos_570_statement <-> erdos_570_statement.
Proof. rewrite /XE2Legacy.erdos_570_statement /erdos_570_statement; try setoid_rewrite graph_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_800_statement_compat :
  XE2Legacy.erdos_800_statement <-> erdos_800_statement.
Proof. rewrite /XE2Legacy.erdos_800_statement /erdos_800_statement; try setoid_rewrite diagonal_ramsey_number_compat; reflexivity. Qed.

Lemma erdos_545_statement_original_compat :
  XE1Original.erdos_545_statement <-> erdos_545_statement.
Proof. rewrite /XE1Original.erdos_545_statement /erdos_545_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_550_statement_original_compat :
  XE1Original.erdos_550_statement <-> erdos_550_statement.
Proof. rewrite /XE1Original.erdos_550_statement /erdos_550_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_552_statement_original_compat :
  XE1Original.erdos_552_statement <-> erdos_552_statement.
Proof. rewrite /XE1Original.erdos_552_statement /erdos_552_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_566_statement_original_compat :
  XE1Original.erdos_566_statement <-> erdos_566_statement.
Proof. rewrite /XE1Original.erdos_566_statement /erdos_566_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_567_statement_original_compat :
  XE1Original.erdos_567_statement <-> erdos_567_statement.
Proof. rewrite /XE1Original.erdos_567_statement /erdos_567_statement; try setoid_rewrite graph_ramsey_number_original_compat; try setoid_rewrite Extremal.migration.consecutive_in_cycle.xe1_h5_graph_compat; reflexivity. Qed.

Lemma erdos_568_statement_original_compat :
  XE1Original.erdos_568_statement <-> erdos_568_statement.
Proof. rewrite /XE1Original.erdos_568_statement /erdos_568_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_812_statement_original_compat :
  XE1Original.erdos_812_statement <-> erdos_812_statement.
Proof. rewrite /XE1Original.erdos_812_statement /erdos_812_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_87_statement_original_compat :
  XE1Original.erdos_87_statement <-> erdos_87_statement.
Proof. rewrite /XE1Original.erdos_87_statement /erdos_87_statement; try setoid_rewrite graph_ramsey_number_original_compat; try setoid_rewrite diagonal_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_547_statement_original_compat :
  XE2Original.erdos_547_statement <-> erdos_547_statement.
Proof. rewrite /XE2Original.erdos_547_statement /erdos_547_statement; try setoid_rewrite diagonal_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_549_statement_original_compat :
  XE2Original.erdos_549_statement <-> erdos_549_statement.
Proof. rewrite /XE2Original.erdos_549_statement /erdos_549_statement; try setoid_rewrite diagonal_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_570_statement_original_compat :
  XE2Original.erdos_570_statement <-> erdos_570_statement.
Proof. rewrite /XE2Original.erdos_570_statement /erdos_570_statement; try setoid_rewrite graph_ramsey_number_original_compat; reflexivity. Qed.

Lemma erdos_800_statement_original_compat :
  XE2Original.erdos_800_statement <-> erdos_800_statement.
Proof. rewrite /XE2Original.erdos_800_statement /erdos_800_statement; try setoid_rewrite diagonal_ramsey_number_original_compat; reflexivity. Qed.

Print Assumptions x56_complement_rel_compat.
Print Assumptions x56_complement_compat.
Print Assumptions x56_complement_diso.
Print Assumptions x56_complement_proofs_compat.
Print Assumptions xe1_complement_rel_compat.
Print Assumptions xe1_complement_graph_compat.
Print Assumptions xe1_complement_diso.
Print Assumptions xe1_complement_proofs_compat.
Print Assumptions c8_complement_c8_erdos_hajnal_statement_compat.
Print Assumptions c8_complement_c8_erdos_hajnal_statement_original_compat.
Print Assumptions xe1_complement_subgraph_compat.
Print Assumptions graph_ramsey_compat.
Print Assumptions graph_ramsey_number_compat.
Print Assumptions diagonal_ramsey_number_compat.
Print Assumptions graph_ramsey_original_compat.
Print Assumptions graph_ramsey_number_original_compat.
Print Assumptions diagonal_ramsey_number_original_compat.
Print Assumptions erdos_545_statement_compat.
Print Assumptions erdos_550_statement_compat.
Print Assumptions erdos_552_statement_compat.
Print Assumptions erdos_566_statement_compat.
Print Assumptions erdos_567_statement_compat.
Print Assumptions erdos_568_statement_compat.
Print Assumptions erdos_812_statement_compat.
Print Assumptions erdos_87_statement_compat.
Print Assumptions erdos_547_statement_compat.
Print Assumptions erdos_549_statement_compat.
Print Assumptions erdos_570_statement_compat.
Print Assumptions erdos_800_statement_compat.
Print Assumptions erdos_545_statement_original_compat.
Print Assumptions erdos_550_statement_original_compat.
Print Assumptions erdos_552_statement_original_compat.
Print Assumptions erdos_566_statement_original_compat.
Print Assumptions erdos_567_statement_original_compat.
Print Assumptions erdos_568_statement_original_compat.
Print Assumptions erdos_812_statement_original_compat.
Print Assumptions erdos_87_statement_original_compat.
Print Assumptions erdos_547_statement_original_compat.
Print Assumptions erdos_549_statement_original_compat.
Print Assumptions erdos_570_statement_original_compat.
Print Assumptions erdos_800_statement_original_compat.
