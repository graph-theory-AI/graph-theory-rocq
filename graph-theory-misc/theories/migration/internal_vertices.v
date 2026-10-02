(** * GTMisc.migration.internal_vertices — frozen internal-vertex chain (library migration B2)

    Batch B, family [internal-vertices] (meta/library_primitives/internal-vertices.json).  [Legacy]
    freezes the conjecture-local helper [x172_path_internal] verbatim as it stood
    at 9e03072, before the migration: the values of a sequence other than its
    first and its last entry, [set0] on the empty sequence.  The live helper now
    unfolds to [GTBase.walks_paths.seq_inner s].  [X172Legacy] freezes the
    affected chain of row
    [metric_lines_bridges_counterexamples_finitely_generated_statement], the
    statement included: [one_bridge_replacement], the inductive closure
    [generated_by_bridge_replacement] with its two constructors, and the
    statement, with the wave prefix dropped from their names and the frozen
    helper referred to as [Legacy.x172_path_internal].  Definitions that do not
    reach the helper (path edges, the counterexample predicate) are the live,
    unchanged ones.

    The frozen helper reads the endpoints with the candidate itself as default
    ([head x s], [last x s]); [seq_inner] matches on the sequence instead.  The two
    are extensionally equal, not convertible: [x172_path_internal_compat] proves
    the equality by membership ([in_seq_inner]), and the chain certificates
    transport it through the existentials and by induction on the closure.
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/internal_vertices.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X172.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x172_path_internal (G : sgraph) (s : seq G) : {set G} :=
  [set x : G | (x \in s) && (x != head x s) && (x != last x s)].

End Legacy.

Module X172Legacy.

Definition one_bridge_replacement (G H : sgraph) : Prop :=
  exists (a b : G) (f : G -> H) (p : seq H),
    a != b /\
    graph_bridge [set a; b] /\
    injective f /\
    path (--) (f a) p /\
    last (f a) p = f b /\
    uniq (f a :: p) /\
    [disjoint Legacy.x172_path_internal (f a :: p)
     & [set y : H | [exists x : G, f x == y]]] /\
    (forall x y : G,
      [set x; y] != [set a; b] ->
      (x -- y <-> f x -- f y)) /\
    forall u v : H,
      u -- v ->
      ([set u; v] \in x172_path_edges (f a :: p)) \/
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

Definition statement : Prop :=
  exists finite_seed_bound : nat,
    forall G : sgraph,
      x172_counterexample_to_lines_bridges_bound G ->
      exists seed : sgraph,
        #|seed| <= finite_seed_bound /\
        generated_by_bridge_replacement seed G.

End X172Legacy.

(** ** Certificates *)

Lemma x172_path_internal_compat (G : sgraph) (s : seq G) :
  Legacy.x172_path_internal s = x172_path_internal s.
Proof. by apply/setP => z; rewrite /x172_path_internal in_seq_inner inE andbA. Qed.

Lemma x172_one_bridge_replacement_compat (G H : sgraph) :
  X172Legacy.one_bridge_replacement G H <-> x172_one_bridge_replacement G H.
Proof.
rewrite /X172Legacy.one_bridge_replacement /x172_one_bridge_replacement.
by split=> -[a [b [f [p [ab [br [inj [pth [lst [un [dis [iso cov]]]]]]]]]]]];
  exists a, b, f, p; do !split=> //; move: dis; rewrite x172_path_internal_compat.
Qed.

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
  X172Legacy.statement <-> metric_lines_bridges_counterexamples_finitely_generated_statement.
Proof.
rewrite /X172Legacy.statement /metric_lines_bridges_counterexamples_finitely_generated_statement.
split=> -[B hB]; exists B => G cG; have [seed [card gen]] := hB G cG;
  exists seed; split=> //; exact/x172_generated_by_bridge_replacement_compat.
Qed.
