(** C20 (Extremal): the strong X98 induced-subdivision model, frozen at the fixed C19 pin
    952a89bdecf65bed9be3a1393eabc91ca091d26c.
    - [Legacy]: the whole seven-field Record [x98_induced_subdivision_model] (type,
      constructor [X98Model], fields) and its [inhabited] wrapper, verbatim.  The live
      Record is now an alias of [GTBase.induced_subdivisions.induced_subdivision_model],
      with constructor and projection wrappers of the same types and implicit arguments;
      its helpers stay live here (B3's path helpers, C19's raw support).
    - [X98Legacy]: the current row over the frozen wrapper.
    The complete row is C19's [Extremal.migration.model_support.X98Original] (B3 path
    helpers, A5 subgraph relation and C19 raw support over a fully frozen Record); its
    certificates stay valid through the wrappers and are reused.  Frozen and live model
    types are different; the transports below repackage a model field by field (each
    field type is convertible) and are mutually inverse. *)
From GTBase Require Import base model_support induced_subdivisions.
From Extremal.conjectures Require Import X59 X98.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Record x98_induced_subdivision_model (H G : sgraph) := X98Model {
  x98_branch : H -> G;
  x98_branch_injective : injective x98_branch;
  x98_edge_path : H -> H -> seq G;
  x98_edge_path_valid :
    forall u v : H,
      u -- v ->
      x98_induced_path_between
        (x98_branch u) (x98_branch v) (x98_edge_path u v);
  (** internal path vertices avoid every branch vertex *)
  x98_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x != x98_branch w;
  (** edge-paths are pairwise internally vertex-disjoint (a shared internal
      vertex forces the two undirected edges to coincide) *)
  x98_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
      x98_internal (x98_edge_path u' v') (x98_branch u') (x98_branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  (** global inducedness: the only G-edges among model vertices join two
      consecutive vertices of a single subdivision path *)
  x98_global_induced :
    forall x y : G,
      x98_model_vertex x98_branch x98_edge_path x ->
      x98_model_vertex x98_branch x98_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ x98_consecutive_in_path (x98_edge_path u v) x y
}.

Definition x98_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (Legacy.x98_induced_subdivision_model H G).

End Legacy.

Module X98Legacy.

Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        Legacy.x98_induced_subdivision H G.

End X98Legacy.

(** ** Certificates *)

Definition x98_model_of_legacy (H G : sgraph)
    (m : Legacy.x98_induced_subdivision_model H G) : x98_induced_subdivision_model H G :=
  @X98Model H G (@Legacy.x98_branch H G m) (@Legacy.x98_branch_injective H G m)
    (@Legacy.x98_edge_path H G m) (@Legacy.x98_edge_path_valid H G m)
    (@Legacy.x98_internal_avoids_branch H G m)
    (@Legacy.x98_paths_internally_disjoint H G m)
    (@Legacy.x98_global_induced H G m).

Definition x98_model_to_legacy (H G : sgraph)
    (m : x98_induced_subdivision_model H G) : Legacy.x98_induced_subdivision_model H G :=
  @Legacy.X98Model H G (@x98_branch H G m) (@x98_branch_injective H G m)
    (@x98_edge_path H G m) (@x98_edge_path_valid H G m)
    (@x98_internal_avoids_branch H G m) (@x98_paths_internally_disjoint H G m)
    (@x98_global_induced H G m).

Lemma x98_induced_subdivision_model_compat (H G : sgraph) :
  {f : Legacy.x98_induced_subdivision_model H G -> x98_induced_subdivision_model H G &
   {g : x98_induced_subdivision_model H G -> Legacy.x98_induced_subdivision_model H G |
    cancel f g /\ cancel g f}}.
Proof. by exists (@x98_model_of_legacy H G), (@x98_model_to_legacy H G); split; case. Qed.

Lemma x98_induced_subdivision_compat (H G : sgraph) :
  Legacy.x98_induced_subdivision H G <-> x98_induced_subdivision H G.
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
