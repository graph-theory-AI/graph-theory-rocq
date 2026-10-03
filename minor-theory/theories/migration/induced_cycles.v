(** * Minor.migration.induced_cycles — B23 certificates: X27's hole and the X27 / X42 / X220 rows

    Frozen verbatim at the fixed B22 baseline 7d8cc47: X27's hole [x27_hole] ([ucycle],
    [3 < size c], and a chord clause with a redundant [x != y] premise after the edge premise and
    B4's live Boolean [x27_consecutive_in_cycle]), the chains [x27_even_hole_free] and
    [x220_even_wheel_free] (spoke parity of a vertex outside a hole), and the five complete rows
    [bounded_degree_even_hole_free_bounded_treewidth_statement] (X27, uniform [f], [Delta G <= d]),
    [even_hole_k4_diamond_free_bounded_treewidth_statement] (X42),
    [theta_prism_even_wheel_free_bounded_treewidth_statement],
    [even_hole_kt_free_logarithmic_treewidth_statement] and
    [even_hole_diamond_free_bounded_tree_alpha_statement] (X220), with every guard, quantifier,
    status and limitation unchanged.  Since B23 the live [x27_hole] is a transparent alias of
    [GTBase.induced_cycles.hole]; the chord clauses are not convertible (distinctness premise), so
    [x27_hole_compat] is an explicit iff through [cyclic_chordless_edge_neq].  The copies keep the
    other families' live helpers: C13's [x27_treewidth_at_most], A1's [x42_induced_free], C19's
    [x220_theta] / [x220_prism], [x220_spokes], [x220_clique_free], [tw_le], [tree_alpha_le].

    The complete earlier rows are reused with their owners' certificates: C13's
    [X27Original.bounded_degree_even_hole_free_bounded_treewidth_statement] and
    [X42Original.even_hole_k4_diamond_free_bounded_treewidth_statement] (B4's raw holes, C13's frozen
    bags, A1's frozen induced-freeness), C19's
    [X220Original.theta_prism_even_wheel_free_bounded_treewidth_statement] (B4's raw even-wheel-free
    chain, C19's frozen model support), and B4's
    [X220Legacy.even_hole_kt_free_logarithmic_treewidth_statement] and
    [X220Legacy.even_hole_diamond_free_bounded_tree_alpha_statement] (raw holes). *)

From GTBase Require Import base induced_cycles.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.
From Minor.migration Require consecutive_in_cycle bag_decompositions model_support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B4 := Minor.migration.consecutive_in_cycle.
Module C13 := Minor.migration.bag_decompositions.
Module C19 := Minor.migration.model_support.

Module Legacy.

Definition x27_hole (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 3 < size c /\
  forall x y : G,
    x \in c -> y \in c -> x -- y -> x != y ->
    x27_consecutive_in_cycle c x y.

End Legacy.

Module X27Legacy.

Definition x27_even_hole_free (G : sgraph) : Prop :=
  forall c : seq G,
    Legacy.x27_hole c ->
    ~~ odd (size c) ->
    False.

Definition bounded_degree_even_hole_free_bounded_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (d : nat) (G : sgraph),
      Delta G <= d ->
      X27Legacy.x27_even_hole_free G ->
      x27_treewidth_at_most G (f d).

End X27Legacy.

Module X42Legacy.

Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      X27Legacy.x27_even_hole_free G ->
      x42_induced_free G 'K_4 ->
      x42_induced_free G x42_diamond ->
      x27_treewidth_at_most G c.

End X42Legacy.

Module X220Legacy.

Definition x220_even_wheel_free (G : sgraph) : Prop :=
  forall (v : G) (c : seq G),
    Legacy.x27_hole c -> v \notin c -> 3 <= #|x220_spokes c v| -> odd #|x220_spokes c v|.

Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, x220_prism H -> ~ has_induced_copy G H) ->
      X220Legacy.x220_even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

Definition even_hole_kt_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      X27Legacy.x27_even_hole_free G -> x220_clique_free G t ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

Definition even_hole_diamond_free_bounded_tree_alpha_statement : Prop :=
  exists k : nat,
    forall G : sgraph,
      X27Legacy.x27_even_hole_free G -> ~ has_induced_copy G x42_diamond -> tree_alpha_le G k.

End X220Legacy.

(** ** The hole: an explicit iff with the canonical view *)

Lemma x27_hole_compat (G : sgraph) (c : seq G) : Legacy.x27_hole c <-> x27_hole c.
Proof.
rewrite /x27_hole; split=> -[uc [sz ch]].
- split=> //; split=> //; apply/cyclic_chordless_edge_neq.
  move=> x y xc yc xy nxy; exact: (ch x y xc yc xy nxy).
- split=> //; split=> // x y xc yc xy nxy.
  exact: (proj2 (cyclic_chordless_edge_neq c) ch x y xc yc xy nxy).
Qed.

(** ** Chains *)

Lemma x27_even_hole_free_compat (G : sgraph) :
  X27Legacy.x27_even_hole_free G <-> x27_even_hole_free G.
Proof. by split=> h c hc ev; apply: (h c _ ev); apply/x27_hole_compat. Qed.

Lemma x220_even_wheel_free_compat (G : sgraph) :
  X220Legacy.x220_even_wheel_free G <-> x220_even_wheel_free G.
Proof. by split=> h v c hc vc s3; apply: (h v c _ vc s3); apply/x27_hole_compat. Qed.

(** ** The five complete current rows *)

Lemma bounded_degree_even_hole_free_bounded_treewidth_statement_compat :
  X27Legacy.bounded_degree_even_hole_free_bounded_treewidth_statement <->
  bounded_degree_even_hole_free_bounded_treewidth_statement.
Proof.
by split=> -[f h]; exists f => d G dG eh; apply: (h d G dG); apply/x27_even_hole_free_compat.
Qed.

Lemma even_hole_k4_diamond_free_bounded_treewidth_statement_compat :
  X42Legacy.even_hole_k4_diamond_free_bounded_treewidth_statement <->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
by split=> -[c h]; exists c => G eh k4 dia; apply: (h G _ k4 dia); apply/x27_even_hole_free_compat.
Qed.

Lemma theta_prism_even_wheel_free_bounded_treewidth_statement_compat :
  X220Legacy.theta_prism_even_wheel_free_bounded_treewidth_statement <->
  theta_prism_even_wheel_free_bounded_treewidth_statement.
Proof.
split=> h t; have [c hc] := h t; exists c => G c4 dia th pr ew cf;
  by apply: (hc G c4 dia th pr _ cf); apply/x220_even_wheel_free_compat.
Qed.

Lemma even_hole_kt_free_logarithmic_treewidth_statement_compat :
  X220Legacy.even_hole_kt_free_logarithmic_treewidth_statement <->
  even_hole_kt_free_logarithmic_treewidth_statement.
Proof.
split=> h t; have [c hc] := h t; exists c => G eh cf;
  by apply: (hc G _ cf); apply/x27_even_hole_free_compat.
Qed.

Lemma even_hole_diamond_free_bounded_tree_alpha_statement_compat :
  X220Legacy.even_hole_diamond_free_bounded_tree_alpha_statement <->
  even_hole_diamond_free_bounded_tree_alpha_statement.
Proof.
by split=> -[k h]; exists k => G eh dia; apply: (h G _ dia); apply/x27_even_hole_free_compat.
Qed.

(** ** The five complete earlier rows, reused with their owners' certificates *)

Lemma bounded_degree_even_hole_free_bounded_treewidth_statement_original_compat :
  Minor.migration.bag_decompositions.X27Original.bounded_degree_even_hole_free_bounded_treewidth_statement <->
  bounded_degree_even_hole_free_bounded_treewidth_statement.
Proof. exact: C13.bounded_degree_even_hole_free_bounded_treewidth_statement_original_compat. Qed.

Lemma even_hole_k4_diamond_free_bounded_treewidth_statement_original_compat :
  Minor.migration.bag_decompositions.X42Original.even_hole_k4_diamond_free_bounded_treewidth_statement <->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof. exact: C13.even_hole_k4_diamond_free_bounded_treewidth_statement_original_compat. Qed.

Lemma theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat :
  Minor.migration.model_support.X220Original.theta_prism_even_wheel_free_bounded_treewidth_statement <->
  theta_prism_even_wheel_free_bounded_treewidth_statement.
Proof. exact: C19.theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat. Qed.

Lemma even_hole_kt_free_logarithmic_treewidth_statement_original_compat :
  Minor.migration.consecutive_in_cycle.X220Legacy.even_hole_kt_free_logarithmic_treewidth_statement <->
  even_hole_kt_free_logarithmic_treewidth_statement.
Proof. exact: B4.even_hole_kt_free_logarithmic_treewidth_statement_compat. Qed.

Lemma even_hole_diamond_free_bounded_tree_alpha_statement_original_compat :
  Minor.migration.consecutive_in_cycle.X220Legacy.even_hole_diamond_free_bounded_tree_alpha_statement <->
  even_hole_diamond_free_bounded_tree_alpha_statement.
Proof. exact: B4.even_hole_diamond_free_bounded_tree_alpha_statement_compat. Qed.

Print Assumptions x27_hole_compat.
Print Assumptions x27_even_hole_free_compat.
Print Assumptions x220_even_wheel_free_compat.
Print Assumptions bounded_degree_even_hole_free_bounded_treewidth_statement_compat.
Print Assumptions even_hole_k4_diamond_free_bounded_treewidth_statement_compat.
Print Assumptions theta_prism_even_wheel_free_bounded_treewidth_statement_compat.
Print Assumptions even_hole_kt_free_logarithmic_treewidth_statement_compat.
Print Assumptions even_hole_diamond_free_bounded_tree_alpha_statement_compat.
Print Assumptions bounded_degree_even_hole_free_bounded_treewidth_statement_original_compat.
Print Assumptions even_hole_k4_diamond_free_bounded_treewidth_statement_original_compat.
Print Assumptions theta_prism_even_wheel_free_bounded_treewidth_statement_original_compat.
Print Assumptions even_hole_kt_free_logarithmic_treewidth_statement_original_compat.
Print Assumptions even_hole_diamond_free_bounded_tree_alpha_statement_original_compat.
