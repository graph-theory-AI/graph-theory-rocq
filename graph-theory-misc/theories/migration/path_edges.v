(** * GTMisc.migration.path_edges — frozen path-edge list and set of X14, X62 and X172
    (library migration B8)

    Batch B, family [path-edges] (meta/library_primitives/path-edges.json).
    [Legacy] freezes, verbatim as they stood at the B8 baseline 048c768, X14's
    [x14_path_edges] (raw-list class: the ORDERED list of the two-element sets of
    consecutive entries, with repetitions, one-vertex sets from repeated entries and
    non-edges kept) and X172's [x172_path_edges] (finite-support class: the set of
    those two-element sets).  The live helpers now unfold to
    [GTBase.walks_paths.seq_edge_list p] and [GTBase.walks_paths.seq_edge_set s],
    whose bodies are these terms, so the helper certificates are kernel-checked
    conversions.  [X14Legacy] / [X62Legacy] freeze the rainbow-path chain, X62's
    cross-file cover predicate and both rows; [X172Legacy] freezes the bridge
    replacement, its complete [Inductive] closure (both constructors, renamed
    [generated_refl] / [generated_step]) and the row.  Only this family's helpers
    are frozen in those per-row copies.

    History.  The complete X14 / X62 rows before every migration are family C6's
    [X14Original] / [X62Original] (GTMisc.migration.edge_colourings, history
    7b04105): they already freeze the raw path-edge list and the cover predicate
    with C6's properness over pre-M1 edges and B6's genuine path, and their
    certificates stay valid by conversion; this family reuses them and does not
    copy them.  [X172Original] composes B2's frozen [x172_path_internal]
    (GTMisc.migration.internal_vertices.Legacy) with this family's frozen edge set,
    the complete pre-B2, pre-B8 chain and row.  Earlier partial snapshots (B2's
    X172Legacy, B6's X14Legacy/X62Legacy, C6's X14Legacy/X62Legacy) are unchanged;
    their reliance on the live helpers is recorded in the reports.  Source hashes,
    substitutions and the per-row theorem names are in
    meta/migration_reports/path_edges.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X14 X62 X172.
From GTMisc.migration Require internal_vertices.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x14_path_edges (G : sgraph) (p : seq G) : seq {set G} :=
  map (fun e : G * G => [set e.1; e.2]) (zip p (behead p)).

Definition x172_path_edges (G : sgraph) (s : seq G) : {set {set G}} :=
  [set e in [seq [set p.1; p.2] | p <- zip s (behead s)]].

End Legacy.

Module X14Legacy.

Definition rainbow_path
    (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) : Prop :=
  @x14_genuine_path G p /\ uniq (map col (@Legacy.x14_path_edges G p)).

Definition andersen_rainbow_path_statement : Prop :=
  forall (n : nat) (C : finType) (col : {set complete n} -> C),
    2 <= n ->
    @x14_proper_edge_colouring (complete n) C col ->
    exists p : seq (complete n),
      @rainbow_path (complete n) C col p /\ size p = n.-1.

End X14Legacy.

Module X62Legacy.

Definition edges_covered_by_paths
    (G : sgraph) (paths : seq (seq G)) : Prop :=
  forall e : {set G},
    e \in x14_edge_set G ->
    exists p : seq G, p \in paths /\ e \in Legacy.x14_path_edges p.

Definition rainbow_paths_linear_edge_cover_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (C : finType) (col : {set G} -> C),
      x14_proper_edge_colouring col ->
      exists paths : seq (seq G),
        size paths <= c * #|G| /\
        (forall p : seq G, p \in paths -> X14Legacy.rainbow_path col p) /\
        edges_covered_by_paths paths.

End X62Legacy.

Module X172Legacy.

Definition one_bridge_replacement (G H : sgraph) : Prop :=
  exists (a b : G) (f : G -> H) (p : seq H),
    a != b /\
    graph_bridge [set a; b] /\
    injective f /\
    path (--) (f a) p /\
    last (f a) p = f b /\
    uniq (f a :: p) /\
    [disjoint x172_path_internal (f a :: p)
     & [set y : H | [exists x : G, f x == y]]] /\
    (forall x y : G,
      [set x; y] != [set a; b] ->
      (x -- y <-> f x -- f y)) /\
    forall u v : H,
      u -- v ->
      ([set u; v] \in Legacy.x172_path_edges (f a :: p)) \/
      (exists x y : G,
        [set x; y] != [set a; b] /\
        x -- y /\
        u = f x /\
        v = f y).

Inductive generated_by_bridge_replacement : sgraph -> sgraph -> Prop :=
| generated_refl G :
    generated_by_bridge_replacement G G
| generated_step G H K :
    one_bridge_replacement G H ->
    generated_by_bridge_replacement H K ->
    generated_by_bridge_replacement G K.

Definition metric_lines_bridges_counterexamples_finitely_generated_statement : Prop :=
  exists finite_seed_bound : nat,
    forall G : sgraph,
      x172_counterexample_to_lines_bridges_bound G ->
      exists seed : sgraph,
        #|seed| <= finite_seed_bound /\
        generated_by_bridge_replacement seed G.

End X172Legacy.

Module X172Original.

Definition one_bridge_replacement (G H : sgraph) : Prop :=
  exists (a b : G) (f : G -> H) (p : seq H),
    a != b /\
    graph_bridge [set a; b] /\
    injective f /\
    path (--) (f a) p /\
    last (f a) p = f b /\
    uniq (f a :: p) /\
    [disjoint GTMisc.migration.internal_vertices.Legacy.x172_path_internal (f a :: p)
     & [set y : H | [exists x : G, f x == y]]] /\
    (forall x y : G,
      [set x; y] != [set a; b] ->
      (x -- y <-> f x -- f y)) /\
    forall u v : H,
      u -- v ->
      ([set u; v] \in Legacy.x172_path_edges (f a :: p)) \/
      (exists x y : G,
        [set x; y] != [set a; b] /\
        x -- y /\
        u = f x /\
        v = f y).

Inductive generated_by_bridge_replacement : sgraph -> sgraph -> Prop :=
| generated_refl G :
    generated_by_bridge_replacement G G
| generated_step G H K :
    one_bridge_replacement G H ->
    generated_by_bridge_replacement H K ->
    generated_by_bridge_replacement G K.

Definition metric_lines_bridges_counterexamples_finitely_generated_statement : Prop :=
  exists finite_seed_bound : nat,
    forall G : sgraph,
      x172_counterexample_to_lines_bridges_bound G ->
      exists seed : sgraph,
        #|seed| <= finite_seed_bound /\
        generated_by_bridge_replacement seed G.

End X172Original.

(** ** Certificates *)

Lemma x14_path_edges_compat (G : sgraph) (p : seq G) : Legacy.x14_path_edges p = x14_path_edges p.
Proof. by []. Qed.

Lemma x172_path_edges_compat (G : sgraph) (s : seq G) : Legacy.x172_path_edges s = x172_path_edges s.
Proof. by []. Qed.

Lemma x14_rainbow_path_compat (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) :
  @X14Legacy.rainbow_path G C col p <-> @x14_rainbow_path G C col p.
Proof. exact: iff_refl. Qed.

Lemma andersen_rainbow_path_statement_compat :
  X14Legacy.andersen_rainbow_path_statement <-> andersen_rainbow_path_statement.
Proof. exact: iff_refl. Qed.

Lemma x62_edges_covered_by_paths_compat (G : sgraph) (paths : seq (seq G)) :
  X62Legacy.edges_covered_by_paths paths <-> x62_edges_covered_by_paths paths.
Proof. exact: iff_refl. Qed.

Lemma rainbow_paths_linear_edge_cover_statement_compat :
  X62Legacy.rainbow_paths_linear_edge_cover_statement <->
  rainbow_paths_linear_edge_cover_statement.
Proof. exact: iff_refl. Qed.

Lemma x172_one_bridge_replacement_compat (G H : sgraph) :
  X172Legacy.one_bridge_replacement G H <-> x172_one_bridge_replacement G H.
Proof. exact: iff_refl. Qed.

(** Two distinct inductive types: by induction on the closure, both ways. *)
Lemma x172_generated_by_bridge_replacement_compat (G H : sgraph) :
  X172Legacy.generated_by_bridge_replacement G H <-> x172_generated_by_bridge_replacement G H.
Proof.
split.
- elim=> {G H} [G|G H K step _ IH]; first exact: x172_generated_refl.
  exact: x172_generated_step (iffLR (x172_one_bridge_replacement_compat G H) step) IH.
- elim=> {G H} [G|G H K step _ IH]; first exact: X172Legacy.generated_refl.
  exact: X172Legacy.generated_step (iffRL (x172_one_bridge_replacement_compat G H) step) IH.
Qed.

Lemma metric_lines_bridges_counterexamples_finitely_generated_statement_compat :
  X172Legacy.metric_lines_bridges_counterexamples_finitely_generated_statement <->
  metric_lines_bridges_counterexamples_finitely_generated_statement.
Proof.
rewrite /X172Legacy.metric_lines_bridges_counterexamples_finitely_generated_statement
  /metric_lines_bridges_counterexamples_finitely_generated_statement.
split=> -[B hB]; exists B => G cG; have [seed [card gen]] := hB G cG;
  exists seed; split=> //; exact/x172_generated_by_bridge_replacement_compat.
Qed.

(** Before B2 and B8: B2's frozen internal vertices and this family's frozen edge set. *)
Lemma x172_one_bridge_replacement_original_compat (G H : sgraph) :
  X172Original.one_bridge_replacement G H <-> x172_one_bridge_replacement G H.
Proof.
rewrite /X172Original.one_bridge_replacement /x172_one_bridge_replacement.
by split=> -[a [b [f [p [ab [br [inj [pth [lst [un [dis [iso cov]]]]]]]]]]]];
  exists a, b, f, p; do !split=> //; move: dis;
  rewrite GTMisc.migration.internal_vertices.x172_path_internal_compat.
Qed.

Lemma x172_generated_by_bridge_replacement_original_compat (G H : sgraph) :
  X172Original.generated_by_bridge_replacement G H <-> x172_generated_by_bridge_replacement G H.
Proof.
split.
- elim=> {G H} [G|G H K step _ IH]; first exact: x172_generated_refl.
  exact: x172_generated_step (iffLR (x172_one_bridge_replacement_original_compat G H) step) IH.
- elim=> {G H} [G|G H K step _ IH]; first exact: X172Original.generated_refl.
  exact: X172Original.generated_step (iffRL (x172_one_bridge_replacement_original_compat G H) step) IH.
Qed.

Lemma metric_lines_bridges_counterexamples_finitely_generated_statement_original_compat :
  X172Original.metric_lines_bridges_counterexamples_finitely_generated_statement <->
  metric_lines_bridges_counterexamples_finitely_generated_statement.
Proof.
rewrite /X172Original.metric_lines_bridges_counterexamples_finitely_generated_statement
  /metric_lines_bridges_counterexamples_finitely_generated_statement.
split=> -[B hB]; exists B => G cG; have [seed [card gen]] := hB G cG;
  exists seed; split=> //; exact/x172_generated_by_bridge_replacement_original_compat.
Qed.

Print Assumptions x14_path_edges_compat.
Print Assumptions x172_path_edges_compat.
Print Assumptions x14_rainbow_path_compat.
Print Assumptions andersen_rainbow_path_statement_compat.
Print Assumptions x62_edges_covered_by_paths_compat.
Print Assumptions rainbow_paths_linear_edge_cover_statement_compat.
Print Assumptions x172_one_bridge_replacement_compat.
Print Assumptions x172_generated_by_bridge_replacement_compat.
Print Assumptions metric_lines_bridges_counterexamples_finitely_generated_statement_compat.
Print Assumptions x172_one_bridge_replacement_original_compat.
Print Assumptions x172_generated_by_bridge_replacement_original_compat.
Print Assumptions metric_lines_bridges_counterexamples_finitely_generated_statement_original_compat.
