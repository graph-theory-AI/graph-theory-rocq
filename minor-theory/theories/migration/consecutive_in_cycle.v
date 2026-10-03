(** * Minor.migration.consecutive_in_cycle — frozen cyclic-adjacency chains (library migration B4)

    Batch B, family [consecutive-in-cycle]
    (meta/library_primitives/consecutive-in-cycle.json).  [Legacy] freezes the
    boolean helper [x27_consecutive_in_cycle] verbatim as it stood at 49ddc03,
    before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_cyclic_consecutiveb c x y], whose body is the same
    disjunction.

    [X27Legacy] freezes the hole ([3 < size c]), the even-hole-free predicate and
    the X27 statement; [X42Legacy] the cross-module X42 row; [X220Legacy] the
    even-wheel-free predicate (spoke parity on a hole) and the three cross-module
    X220 rows.  The copies drop the wave prefix and refer to the frozen helper as
    [Legacy.x27_consecutive_in_cycle]; definitions that do not reach the helper are
    the live ones, in particular [x42_induced_free], migrated by family induced-free
    (A1).  These certificates are kernel-checked conversions.

    A1's snapshot [Minor.migration.induced_free.X42Legacy.statement] calls the live
    [x27_even_hole_free], which now reaches this family's canonical; it is kept
    unchanged.  [X42Original] freezes the X42 row end to end, over A1's frozen
    [x42_induced_free] and this family's frozen even-hole chain; its certificate
    goes through A1's [x42_induced_free_compat].  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_cycle.md. *)

From GTBase Require Import base.
From GTBase Require induced_cycles.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.
From Minor.migration Require induced_free.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x27_consecutive_in_cycle (G : sgraph) (c : seq G) (x y : G) : bool :=
  ((x, y) \in zip c (rot 1 c)) || ((y, x) \in zip c (rot 1 c)).

End Legacy.

Module X27Legacy.

Definition hole (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 3 < size c /\
  forall x y : G,
    x \in c -> y \in c -> x -- y -> x != y ->
    Legacy.x27_consecutive_in_cycle c x y.

Definition even_hole_free (G : sgraph) : Prop :=
  forall c : seq G,
    hole c ->
    ~~ odd (size c) ->
    False.

Definition bounded_degree_even_hole_free_bounded_treewidth_statement : Prop :=
  exists f : nat -> nat,
    forall (d : nat) (G : sgraph),
      Delta G <= d ->
      even_hole_free G ->
      x27_treewidth_at_most G (f d).

End X27Legacy.

Module X42Legacy.

Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      X27Legacy.even_hole_free G ->
      x42_induced_free G 'K_4 ->
      x42_induced_free G x42_diamond ->
      x27_treewidth_at_most G c.

End X42Legacy.

Module X220Legacy.

Definition even_wheel_free (G : sgraph) : Prop :=
  forall (v : G) (c : seq G),
    X27Legacy.hole c -> v \notin c -> 3 <= #|x220_spokes c v| -> odd #|x220_spokes c v|.

Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, x220_prism H -> ~ has_induced_copy G H) ->
      even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

Definition even_hole_kt_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      X27Legacy.even_hole_free G -> x220_clique_free G t ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

Definition even_hole_diamond_free_bounded_tree_alpha_statement : Prop :=
  exists k : nat,
    forall G : sgraph,
      X27Legacy.even_hole_free G -> ~ has_induced_copy G x42_diamond -> tree_alpha_le G k.

End X220Legacy.

Module X42Original.

Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      X27Legacy.even_hole_free G ->
      induced_free.Legacy.x42_induced_free G 'K_4 ->
      induced_free.Legacy.x42_induced_free G x42_diamond ->
      x27_treewidth_at_most G c.

End X42Original.

(** ** Certificates *)

(** B23 (2026-10-03): the live holes / induced cycles are now aliases of GTBase.induced_cycles, which
    states chordlessness without a distinctness premise and with the Boolean cyclic consecutiveness.
    The certificates below that reach them are therefore proved through its bridges instead of by
    conversion; their statements and every frozen body are unchanged. *)

Lemma x27_consecutive_in_cycle_compat (G : sgraph) (c : seq G) (x y : G) :
  Legacy.x27_consecutive_in_cycle c x y = x27_consecutive_in_cycle c x y.
Proof. by []. Qed.

Lemma x27_hole_compat (G : sgraph) (c : seq G) : X27Legacy.hole c <-> x27_hole c.
Proof.
rewrite /x27_hole; split=> -[uc [sz ch]].
- split=> //; split=> //; apply/induced_cycles.cyclic_chordless_edge_neq.
  move=> x y xc yc xy nxy; exact: (ch x y xc yc xy nxy).
- split=> //; split=> // x y xc yc xy nxy.
  exact: (proj2 (induced_cycles.cyclic_chordless_edge_neq c) ch x y xc yc xy nxy).
Qed.

Lemma x27_even_hole_free_compat (G : sgraph) :
  X27Legacy.even_hole_free G <-> x27_even_hole_free G.
Proof.
by split=> h c hc ev; apply: (h c _ ev); apply/x27_hole_compat.
Qed.

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

Lemma x220_even_wheel_free_compat (G : sgraph) :
  X220Legacy.even_wheel_free G <-> x220_even_wheel_free G.
Proof.
by split=> h v c hc vc s3; apply: (h v c _ vc s3); apply/x27_hole_compat.
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

Lemma even_hole_k4_diamond_free_bounded_treewidth_statement_original_compat :
  X42Original.even_hole_k4_diamond_free_bounded_treewidth_statement <->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
split=> -[c bound]; exists c => G eh k4 diamond; apply: bound;
  first [by apply/x27_even_hole_free_compat | by apply/induced_free.x42_induced_free_compat].
Qed.
