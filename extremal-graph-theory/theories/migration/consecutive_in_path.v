(** * Extremal.migration.consecutive_in_path — frozen consecutive-entry chain (library migration B3)

    Batch B, family [consecutive-in-path]
    (meta/library_primitives/consecutive-in-path.json).  [Legacy] freezes the
    conjecture-local helper [x98_consecutive_in_path] verbatim as it stood at
    787a996, before the migration; the live helper now unfolds to
    [GTBase.walks_paths.seq_consecutive p u v], whose body is the same
    disjunction.

    [X98Legacy] freezes the affected chain of row
    [polynomial_kuhn_osthus_induced_subdivision_statement]:
    [induced_path_between], the whole induced-subdivision record (type,
    constructor [X98Model] and its seven fields), the [inhabited] wrapper
    [induced_subdivision] and the statement.  The copies drop the wave prefix of
    the record type, of its fields and of the chain definitions, and refer to the
    frozen helper as [Legacy.x98_consecutive_in_path]; [x98_internal] and
    [x98_model_vertex], which do not reach the helper, are the live ones.

    The frozen record is a different inductive type from the live one even
    though their fields agree, so no conversion relates them.  The maps
    [x98_model_of_legacy] and [x98_model_to_legacy] repackage a model field by
    field (each field type is convertible to its counterpart) and are mutually
    inverse ([x98_induced_subdivision_model_compat]); the [inhabited] wrappers
    and the statements are related through them.  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_path.md. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X59 X98.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x98_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

End Legacy.

Module X98Legacy.

Definition induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        Legacy.x98_consecutive_in_path p u v
  end.

Record induced_subdivision_model (H G : sgraph) := X98Model {
  branch : H -> G;
  branch_injective : injective branch;
  edge_path : H -> H -> seq G;
  edge_path_valid :
    forall u v : H,
      u -- v ->
      induced_path_between
        (branch u) (branch v) (edge_path u v);
  (** internal path vertices avoid every branch vertex *)
  internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x98_internal (edge_path u v) (branch u) (branch v) x ->
      x != branch w;
  (** edge-paths are pairwise internally vertex-disjoint (a shared internal
      vertex forces the two undirected edges to coincide) *)
  paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x98_internal (edge_path u v) (branch u) (branch v) x ->
      x98_internal (edge_path u' v') (branch u') (branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  (** global inducedness: the only G-edges among model vertices join two
      consecutive vertices of a single subdivision path *)
  global_induced :
    forall x y : G,
      x98_model_vertex branch edge_path x ->
      x98_model_vertex branch edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ Legacy.x98_consecutive_in_path (edge_path u v) x y
}.

Definition induced_subdivision (H G : sgraph) : Prop :=
  inhabited (induced_subdivision_model H G).

Definition statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        induced_subdivision H G.

End X98Legacy.

(** ** Certificates *)

Lemma x98_consecutive_in_path_compat (G : sgraph) (p : seq G) (u v : G) :
  Legacy.x98_consecutive_in_path p u v = x98_consecutive_in_path p u v.
Proof. by []. Qed.

Lemma x98_induced_path_between_compat (G : sgraph) (a b : G) (p : seq G) :
  X98Legacy.induced_path_between a b p <-> x98_induced_path_between a b p.
Proof. exact: iff_refl. Qed.

(** Field-by-field repackagings between the frozen and the live model records. *)
Definition x98_model_of_legacy (H G : sgraph)
    (m : X98Legacy.induced_subdivision_model H G) : x98_induced_subdivision_model H G :=
  @X98Model H G (@X98Legacy.branch H G m) (@X98Legacy.branch_injective H G m)
    (@X98Legacy.edge_path H G m) (@X98Legacy.edge_path_valid H G m)
    (@X98Legacy.internal_avoids_branch H G m) (@X98Legacy.paths_internally_disjoint H G m)
    (@X98Legacy.global_induced H G m).

Definition x98_model_to_legacy (H G : sgraph)
    (m : x98_induced_subdivision_model H G) : X98Legacy.induced_subdivision_model H G :=
  @X98Legacy.X98Model H G (@x98_branch H G m) (@x98_branch_injective H G m)
    (@x98_edge_path H G m) (@x98_edge_path_valid H G m)
    (@x98_internal_avoids_branch H G m) (@x98_paths_internally_disjoint H G m)
    (@x98_global_induced H G m).

(** The frozen and the live record types are isomorphic. *)
Lemma x98_induced_subdivision_model_compat (H G : sgraph) :
  {f : X98Legacy.induced_subdivision_model H G -> x98_induced_subdivision_model H G &
   {g : x98_induced_subdivision_model H G -> X98Legacy.induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x98_model_of_legacy H G), (@x98_model_to_legacy H G); split; case. Qed.

Lemma x98_induced_subdivision_compat (H G : sgraph) :
  X98Legacy.induced_subdivision H G <-> x98_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x98_model_of_legacy m.
exact: x98_model_to_legacy m.
Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_compat :
  X98Legacy.statement <-> polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
split=> st H; have [p hp] := st H; exists p => s G s1 free avg.
- exact/x98_induced_subdivision_compat/(hp s G s1 free avg).
- exact/x98_induced_subdivision_compat/(hp s G s1 free avg).
Qed.
