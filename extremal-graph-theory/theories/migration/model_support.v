(** C19 (Extremal): X98 raw model support, frozen at the private union
    bb0bf3cd7c1d14e014704ebd5e24b03e4c475cb8 (exact C18 15a5a5c + reviewed A14
    f52251a).
    - [Legacy]: the raw support [x98_model_vertex] verbatim; the live helper now
      unfolds to [GTBase.model_support.model_support br ep x], the same disjunction.
    - [X98Legacy]: the current chain over the frozen support: the whole seven-field
      Record (type, constructor [X98Model], fields), its [inhabited] wrapper and the
      row.  Every other helper stays live here (B3's path helpers, A5's
      [x59_subgraph_of]).
    - [X98Original]: the complete row.  Its Record combines B3's frozen
      [induced_path_between] and consecutive-entry helper with this family's frozen
      support; its row uses A5's frozen [x59_subgraph_of].  The older B3 Record
      and A5 rows remain unchanged as documented snapshots.
    Frozen and live Records are different inductive types; the transports below
    repackage a model field by field (each field type is convertible to its
    counterpart) and are mutually inverse.  Earlier certificate modules are
    aliased, not imported. *)
From GTBase Require Import base model_support.
From Extremal.conjectures Require Import X59 X98.
From Extremal.migration Require consecutive_in_path subgraph_of.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module B3 := Extremal.migration.consecutive_in_path.
Module A5 := Extremal.migration.subgraph_of.

Module Legacy.

Definition x98_model_vertex (H G : sgraph)
    (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop :=
  (exists h : H, br h = x) \/ (exists u v : H, u -- v /\ x \in ep u v).

End Legacy.

Module X98Legacy.

Record x98_induced_subdivision_model (H G : sgraph) := X98Model {
  x98_branch : H -> G;
  x98_branch_injective : injective x98_branch;
  x98_edge_path : H -> H -> seq G;
  x98_edge_path_valid :
    forall u v : H,
      u -- v ->
      x98_induced_path_between
        (x98_branch u) (x98_branch v) (x98_edge_path u v);
  x98_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x != x98_branch w;
  x98_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x98_internal (x98_edge_path u' v') (x98_branch u') (x98_branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  x98_global_induced :
    forall x y : G,
      Legacy.x98_model_vertex x98_branch x98_edge_path x ->
      Legacy.x98_model_vertex x98_branch x98_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ x98_consecutive_in_path (x98_edge_path u v) x y
}.

Definition x98_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (X98Legacy.x98_induced_subdivision_model H G).

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        X98Legacy.x98_induced_subdivision H G.

End X98Legacy.

Module X98Original.

Record x98_induced_subdivision_model (H G : sgraph) := X98Model {
  x98_branch : H -> G;
  x98_branch_injective : injective x98_branch;
  x98_edge_path : H -> H -> seq G;
  x98_edge_path_valid :
    forall u v : H,
      u -- v ->
      B3.X98Legacy.induced_path_between
        (x98_branch u) (x98_branch v) (x98_edge_path u v);
  x98_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x != x98_branch w;
  x98_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x98_internal (x98_edge_path u' v') (x98_branch u') (x98_branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  x98_global_induced :
    forall x y : G,
      Legacy.x98_model_vertex x98_branch x98_edge_path x ->
      Legacy.x98_model_vertex x98_branch x98_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ B3.Legacy.x98_consecutive_in_path (x98_edge_path u v) x y
}.

Definition x98_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (X98Original.x98_induced_subdivision_model H G).

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ A5.Legacy.x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        X98Original.x98_induced_subdivision H G.

End X98Original.

(** ** Certificates *)

Lemma x98_model_vertex_compat (H G : sgraph) (br : H -> G) (ep : H -> H -> seq G) (x : G) :
  Legacy.x98_model_vertex br ep x <-> x98_model_vertex br ep x.
Proof. exact: iff_refl. Qed.

Definition x98_model_of_legacy (H G : sgraph)
    (m : X98Legacy.x98_induced_subdivision_model H G) : x98_induced_subdivision_model H G :=
  @X98Model H G (@X98Legacy.x98_branch H G m) (@X98Legacy.x98_branch_injective H G m)
    (@X98Legacy.x98_edge_path H G m) (@X98Legacy.x98_edge_path_valid H G m)
    (@X98Legacy.x98_internal_avoids_branch H G m)
    (@X98Legacy.x98_paths_internally_disjoint H G m)
    (@X98Legacy.x98_global_induced H G m).

Definition x98_model_to_legacy (H G : sgraph)
    (m : x98_induced_subdivision_model H G) : X98Legacy.x98_induced_subdivision_model H G :=
  @X98Legacy.X98Model H G (@x98_branch H G m) (@x98_branch_injective H G m)
    (@x98_edge_path H G m) (@x98_edge_path_valid H G m)
    (@x98_internal_avoids_branch H G m) (@x98_paths_internally_disjoint H G m)
    (@x98_global_induced H G m).

Lemma x98_induced_subdivision_model_compat (H G : sgraph) :
  {f : X98Legacy.x98_induced_subdivision_model H G -> x98_induced_subdivision_model H G &
   {g : x98_induced_subdivision_model H G -> X98Legacy.x98_induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x98_model_of_legacy H G), (@x98_model_to_legacy H G); split; case. Qed.

Lemma x98_induced_subdivision_compat (H G : sgraph) :
  X98Legacy.x98_induced_subdivision H G <-> x98_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x98_model_of_legacy m.
exact: x98_model_to_legacy m.
Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_compat :
  X98Legacy.polynomial_kuhn_osthus_induced_subdivision_statement <->
  polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
split=> st H; have [p hp] := st H; exists p => s G s1 free avg.
- exact/x98_induced_subdivision_compat/(hp s G s1 free avg).
- exact/x98_induced_subdivision_compat/(hp s G s1 free avg).
Qed.

Definition x98_model_of_original (H G : sgraph)
    (m : X98Original.x98_induced_subdivision_model H G) : x98_induced_subdivision_model H G :=
  @X98Model H G (@X98Original.x98_branch H G m) (@X98Original.x98_branch_injective H G m)
    (@X98Original.x98_edge_path H G m) (@X98Original.x98_edge_path_valid H G m)
    (@X98Original.x98_internal_avoids_branch H G m)
    (@X98Original.x98_paths_internally_disjoint H G m)
    (@X98Original.x98_global_induced H G m).

Definition x98_model_to_original (H G : sgraph)
    (m : x98_induced_subdivision_model H G) : X98Original.x98_induced_subdivision_model H G :=
  @X98Original.X98Model H G (@x98_branch H G m) (@x98_branch_injective H G m)
    (@x98_edge_path H G m) (@x98_edge_path_valid H G m)
    (@x98_internal_avoids_branch H G m) (@x98_paths_internally_disjoint H G m)
    (@x98_global_induced H G m).

Lemma x98_induced_subdivision_model_original_compat (H G : sgraph) :
  {f : X98Original.x98_induced_subdivision_model H G -> x98_induced_subdivision_model H G &
   {g : x98_induced_subdivision_model H G -> X98Original.x98_induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x98_model_of_original H G), (@x98_model_to_original H G); split; case. Qed.

Lemma x98_induced_subdivision_original_compat (H G : sgraph) :
  X98Original.x98_induced_subdivision H G <-> x98_induced_subdivision H G.
Proof.
split=> -[m]; constructor; first exact: x98_model_of_original m.
exact: x98_model_to_original m.
Qed.

Lemma polynomial_kuhn_osthus_induced_subdivision_statement_original_compat :
  X98Original.polynomial_kuhn_osthus_induced_subdivision_statement <->
  polynomial_kuhn_osthus_induced_subdivision_statement.
Proof.
split=> st H; have [p hp] := st H; exists p => s G s1 free avg.
- apply/x98_induced_subdivision_original_compat; apply: (hp s G s1 _ avg).
  by move/A5.x59_subgraph_of_compat.
- apply/x98_induced_subdivision_original_compat; apply: (hp s G s1 _ avg).
  by move/A5.x59_subgraph_of_compat.
Qed.
