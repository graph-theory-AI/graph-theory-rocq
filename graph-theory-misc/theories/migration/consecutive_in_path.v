(** * GTMisc.migration.consecutive_in_path — frozen consecutive-entry chains (library migration B3)

    Batch B, family [consecutive-in-path]
    (meta/library_primitives/consecutive-in-path.json).  [Legacy] freezes the
    conjecture-local helpers [x91_consecutive_in_path] and
    [x114_consecutive_in_path] verbatim as they stood at 787a996, before the
    migration; the live helpers now unfold to
    [GTBase.walks_paths.seq_consecutive p u v], whose body is the same
    disjunction.

    [X91Legacy] freezes the affected chain of row
    [avoidable_path_or_pk_free_statement]: [induced_path], [avoidable_path],
    [Pk_free] and the statement; [x91_induced_cycle] and
    [x91_sequence_contained] do not reach the helper and are the live ones.  Its
    certificates are kernel-checked conversions.

    [X114Legacy] freezes the affected chain of row
    [subcubic_induced_subdivision_np_complete_statement]:
    [induced_path_between], the whole induced-subdivision record (type,
    constructor [X114Model] and its seven fields), the [inhabited] wrapper
    [induced_subdivision], the decision problem [hisc_problem] built on it, and
    the statement; [x114_internal], [x114_model_vertex], [x114_np_complete] and
    [x114_subcubic] do not reach the helper and are the live ones.  The frozen
    record is a different inductive type from the live one, so
    [x114_model_of_legacy] and [x114_model_to_legacy] repackage a model field by
    field and are mutually inverse ([x114_induced_subdivision_model_compat]).
    The frozen and the live problems have the same instances and sizes and
    equivalent memberships, and [in_NP] and [NP_hard] of the D7 complexity layer
    transfer between them ([x114_hisc_problem_compat]).  Source hashes, the exact
    substitutions and the per-row theorem names are recorded in
    meta/migration_reports/consecutive_in_path.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import D7 X91 X114.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x91_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x114_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

End Legacy.

Module X91Legacy.

Definition induced_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        Legacy.x91_consecutive_in_path p u v
  end.

Definition avoidable_path (G : sgraph) (p : seq G) : Prop :=
  induced_path p /\
  forall u v : G,
    induced_path (u :: rcons p v) ->
    exists c : seq G,
      x91_induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition Pk_free (G : sgraph) (k : nat) : Prop :=
  forall p : seq G, size p = k -> ~ induced_path p.

Definition statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      Pk_free G k \/
      exists p : seq G, size p = k /\ avoidable_path p.

End X91Legacy.

Module X114Legacy.

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
        Legacy.x114_consecutive_in_path p u v
  end.

Record induced_subdivision_model (H G : sgraph) := X114Model {
  branch : H -> G;
  branch_injective : injective branch;
  edge_path : H -> H -> seq G;
  edge_path_valid :
    forall u v : H,
      u -- v ->
      induced_path_between
        (branch u) (branch v) (edge_path u v);
  internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x114_internal (edge_path u v) (branch u) (branch v) x ->
      x != branch w;
  paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x114_internal (edge_path u v) (branch u) (branch v) x ->
      x114_internal (edge_path u' v') (branch u') (branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  global_induced :
    forall x y : G,
      x114_model_vertex branch edge_path x ->
      x114_model_vertex branch edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ Legacy.x114_consecutive_in_path (edge_path u v) x y
}.

Definition induced_subdivision (H G : sgraph) : Prop :=
  inhabited (induced_subdivision_model H G).

Definition hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => induced_subdivision H G |}.

Definition statement : Prop :=
  exists H : sgraph,
    x114_subcubic H /\ x114_np_complete (hisc_problem H).

End X114Legacy.

(** ** X91 certificates *)

Lemma x91_consecutive_in_path_compat (G : sgraph) (p : seq G) (u v : G) :
  Legacy.x91_consecutive_in_path p u v = x91_consecutive_in_path p u v.
Proof. by []. Qed.

Lemma x91_induced_path_compat (G : sgraph) (p : seq G) :
  X91Legacy.induced_path p <-> x91_induced_path p.
Proof. exact: iff_refl. Qed.

Lemma x91_avoidable_path_compat (G : sgraph) (p : seq G) :
  X91Legacy.avoidable_path p <-> x91_avoidable_path p.
Proof. exact: iff_refl. Qed.

Lemma x91_Pk_free_compat (G : sgraph) (k : nat) :
  X91Legacy.Pk_free G k <-> x91_Pk_free G k.
Proof. exact: iff_refl. Qed.

Lemma avoidable_path_or_pk_free_statement_compat :
  X91Legacy.statement <-> avoidable_path_or_pk_free_statement.
Proof. exact: iff_refl. Qed.

(** ** X114 certificates *)

Lemma x114_consecutive_in_path_compat (G : sgraph) (p : seq G) (u v : G) :
  Legacy.x114_consecutive_in_path p u v = x114_consecutive_in_path p u v.
Proof. by []. Qed.

Lemma x114_induced_path_between_compat (G : sgraph) (a b : G) (p : seq G) :
  X114Legacy.induced_path_between a b p <-> x114_induced_path_between a b p.
Proof. exact: iff_refl. Qed.

(** Field-by-field repackagings between the frozen and the live model records. *)
Definition x114_model_of_legacy (H G : sgraph)
    (m : X114Legacy.induced_subdivision_model H G) : x114_induced_subdivision_model H G :=
  @X114Model H G (@X114Legacy.branch H G m) (@X114Legacy.branch_injective H G m)
    (@X114Legacy.edge_path H G m) (@X114Legacy.edge_path_valid H G m)
    (@X114Legacy.internal_avoids_branch H G m) (@X114Legacy.paths_internally_disjoint H G m)
    (@X114Legacy.global_induced H G m).

Definition x114_model_to_legacy (H G : sgraph)
    (m : x114_induced_subdivision_model H G) : X114Legacy.induced_subdivision_model H G :=
  @X114Legacy.X114Model H G (@x114_branch H G m) (@x114_branch_injective H G m)
    (@x114_edge_path H G m) (@x114_edge_path_valid H G m)
    (@x114_internal_avoids_branch H G m) (@x114_paths_internally_disjoint H G m)
    (@x114_global_induced H G m).

(** The frozen and the live record types are isomorphic. *)
Lemma x114_induced_subdivision_model_compat (H G : sgraph) :
  {f : X114Legacy.induced_subdivision_model H G -> x114_induced_subdivision_model H G &
   {g : x114_induced_subdivision_model H G -> X114Legacy.induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x114_model_of_legacy H G), (@x114_model_to_legacy H G); split; case. Qed.

Lemma x114_induced_subdivision_compat (H G : sgraph) :
  X114Legacy.induced_subdivision H G <-> x114_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x114_model_of_legacy m.
exact: x114_model_to_legacy m.
Qed.

(** Both problems take a graph with size its order; their memberships are
    equivalent, so NP membership and NP-hardness transfer. *)
Lemma x114_hisc_problem_compat (H : sgraph) :
  [/\ forall G : sgraph,
        @pmem (X114Legacy.hisc_problem H) G <-> @pmem (x114_hisc_problem H) G,
      in_NP (X114Legacy.hisc_problem H) <-> in_NP (x114_hisc_problem H) &
      NP_hard (X114Legacy.hisc_problem H) <-> NP_hard (x114_hisc_problem H)].
Proof.
have mem G : @pmem (X114Legacy.hisc_problem H) G <-> @pmem (x114_hisc_problem H) G.
  exact: x114_induced_subdivision_compat.
split=> //.
- split=> -[verify [vcost [a [d [b [vmem vbound]]]]]];
    exists verify, vcost, a, d, b; split=> // G.
  + exact: iff_trans (iff_sym (mem G)) (vmem G).
  + exact: iff_trans (mem G) (vmem G).
- split=> hard A /hard[f [cost [a [d [b [fmem fcost fsize]]]]]];
    exists f, cost, a, d, b; split=> // x.
  + exact: iff_trans (fmem x) (mem (f x)).
  + exact: iff_trans (fmem x) (iff_sym (mem (f x))).
Qed.

Lemma x114_np_complete_hisc_problem_compat (H : sgraph) :
  x114_np_complete (X114Legacy.hisc_problem H) <-> x114_np_complete (x114_hisc_problem H).
Proof.
have [_ np hard] := x114_hisc_problem_compat H.
by split=> -[inNP isHard]; split; [exact/np | exact/hard | exact/np | exact/hard].
Qed.

Lemma subcubic_induced_subdivision_np_complete_statement_compat :
  X114Legacy.statement <-> subcubic_induced_subdivision_np_complete_statement.
Proof.
split=> -[H [sub np]]; exists H; split=> //.
- exact/x114_np_complete_hisc_problem_compat.
- exact/x114_np_complete_hisc_problem_compat.
Qed.
