(** * Extremal.conjectures.X98 -- v2 polynomial Kuhn-Osthus row *)

From GTBase Require Export base.
From GTBase Require Import model_support induced_subdivisions.
From Extremal.conjectures Require Import X59.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X98 vocabulary ************************************************)

Definition x98_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  seq_consecutive p u v.

Definition x98_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x98_consecutive_in_path p u v
  end.

(** An internal (non-endpoint) vertex of a candidate edge-path [p] whose
    endpoints are [a] and [b]. *)
Definition x98_internal (G : sgraph) (p : seq G) (a b x : G) : Prop :=
  x \in p /\ x != a /\ x != b.

(** A vertex of the whole subdivision model: a branch vertex, or a vertex
    lying on some edge-path. *)
Definition x98_model_vertex (H G : sgraph)
    (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop := model_support br ep x.

(** The strong induced-subdivision model is the canonical
    [GTBase.induced_subdivisions.induced_subdivision_model] (pattern before host).  The
    definitions below keep the local constructor and projection names with their exact
    types and implicit arguments; every field formula is convertible to the canonical one. *)
Definition x98_induced_subdivision_model (H G : sgraph) : Type := induced_subdivision_model H G.

Definition X98Model (H G : sgraph) (x98_branch : H -> G) (x98_branch_injective : injective x98_branch)
    (x98_edge_path : H -> H -> seq G)
    (x98_edge_path_valid :
       forall u v : H,
         u -- v ->
         x98_induced_path_between
           (x98_branch u) (x98_branch v) (x98_edge_path u v))
    (x98_internal_avoids_branch :
       forall (u v w : H) (x : G),
         u -- v ->
         x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
         x != x98_branch w)
    (x98_paths_internally_disjoint :
       forall (u v u' v' : H) (x : G),
         u -- v -> u' -- v' ->
         x98_internal (x98_edge_path u v) (x98_branch u) (x98_branch v) x ->
         x98_internal (x98_edge_path u' v') (x98_branch u') (x98_branch v') x ->
         (u = u' /\ v = v') \/ (u = v' /\ v = u'))
    (x98_global_induced :
       forall x y : G,
         x98_model_vertex x98_branch x98_edge_path x ->
         x98_model_vertex x98_branch x98_edge_path y ->
         x -- y ->
         exists u v : H, u -- v /\ x98_consecutive_in_path (x98_edge_path u v) x y) :
    x98_induced_subdivision_model H G :=
  @InducedSubdivisionModel H G x98_branch x98_branch_injective x98_edge_path x98_edge_path_valid
    x98_internal_avoids_branch x98_paths_internally_disjoint x98_global_induced.

Definition x98_branch (H G : sgraph) (x0 : x98_induced_subdivision_model H G) : H -> G :=
  isd_branch x0.

Definition x98_branch_injective (H G : sgraph) (x0 : x98_induced_subdivision_model H G) :
    injective (x98_branch x0) :=
  @isd_branch_injective H G x0.

Definition x98_edge_path (H G : sgraph) (x0 : x98_induced_subdivision_model H G) : H -> H -> seq G :=
  isd_edge_path x0.

Definition x98_edge_path_valid (H G : sgraph) (x0 : x98_induced_subdivision_model H G) :
    forall u v : H,
      u -- v ->
      x98_induced_path_between (x98_branch x0 u) (x98_branch x0 v) (x98_edge_path x0 u v) :=
  @isd_edge_path_valid H G x0.

Definition x98_internal_avoids_branch (H G : sgraph) (x0 : x98_induced_subdivision_model H G) :
    forall (u v w : H) (x : G),
      u -- v ->
      x98_internal (x98_edge_path x0 u v) (x98_branch x0 u) (x98_branch x0 v) x ->
      x != x98_branch x0 w :=
  @isd_internal_avoids_branch H G x0.

Definition x98_paths_internally_disjoint (H G : sgraph) (x0 : x98_induced_subdivision_model H G) :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x98_internal (x98_edge_path x0 u v) (x98_branch x0 u) (x98_branch x0 v) x ->
      x98_internal (x98_edge_path x0 u' v') (x98_branch x0 u') (x98_branch x0 v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u') :=
  @isd_paths_internally_disjoint H G x0.

Definition x98_global_induced (H G : sgraph) (x0 : x98_induced_subdivision_model H G) :
    forall x y : G,
      x98_model_vertex (x98_branch x0) (x98_edge_path x0) x ->
      x98_model_vertex (x98_branch x0) (x98_edge_path x0) y ->
      x -- y ->
      exists u v : H, u -- v /\ x98_consecutive_in_path (x98_edge_path x0 u v) x y :=
  @isd_global_induced H G x0.

Arguments X98Model [H G] [x98_branch] x98_branch_injective [x98_edge_path]
  x98_edge_path_valid x98_internal_avoids_branch x98_paths_internally_disjoint x98_global_induced.
Arguments x98_branch [H G] x0 _.
Arguments x98_branch_injective [H G x0 x1 x2] _.
Arguments x98_edge_path [H G] x0 _ _.
Arguments x98_edge_path_valid [H G] x0 [u v] _.
Arguments x98_internal_avoids_branch [H G x0 u v] w [x] _ _.
Arguments x98_paths_internally_disjoint [H G x0 u v u' v' x] _ _ _ _.
Arguments x98_global_induced [H G x0 x y] _ _ _.

Definition x98_induced_subdivision (H G : sgraph) : Prop := induced_subdivision H G.

(** Corpus row: studies:std_bonamy_et_al_polynomial_k_hn_osthus_conjecture
    Site: none
    Review: none
    English statement: (Bonamy, Bousquet, Pilipczuk, Rzazewski, Thomasse and Walczak, "Bonamy et al. polynomial Kuhn-Osthus conjecture")
      For every graph H there is a polynomial p such that for every s >= 1, every graph G with
      no K_{s,s} subgraph whose average degree is at least p(s) contains an induced subdivision
      of H; that is, the Kuhn-Osthus threshold p(s,H) can be taken polynomial in s.
    Definitions: [x98_consecutive_in_path p u v] - u and v are consecutive in the list p (X98.v);
      [x98_induced_path_between G a b p] - p is a duplicate-free path from a to b whose only
      internal edges are the consecutive ones, i.e. an induced path (X98.v); [x98_internal p a b
      x] - x is a non-endpoint vertex of p (X98.v); [x98_model_vertex br ep x] - x is a branch
      vertex or lies on some edge-path (X98.v); [x98_induced_subdivision_model H G] - a record
      with injective branch vertices, induced edge-paths for the edges of H, internal vertices
      avoiding branch vertices, pairwise internally disjoint paths, and global inducedness (the
      only edges of G among model vertices are consecutive pairs on a single path) (X98.v);
      [x98_induced_subdivision H G] - inhabitation of that record (X98.v);
      [x59_subgraph_of], [x59_poly_eval] (X59.v); [KB s s] - the complete bipartite graph
      K_{s,s} (GTBase); [average_degree_geq G d 1] - average degree at least d (GTBase).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      The polynomial is a coefficient list, so only non-negative integer coefficients are
      available, which suffices for a threshold. K_{s,s}-freeness is subgraph-freeness, as in
      the Kuhn-Osthus theorem. The polynomial may depend on H but not on s or G, as the source
      requires. *)
Definition polynomial_kuhn_osthus_induced_subdivision_statement : Prop :=
  forall H : sgraph,
    exists p : seq nat,
      forall (s : nat) (G : sgraph),
        1 <= s ->
        ~ x59_subgraph_of (KB s s) G ->
        average_degree_geq G (x59_poly_eval p s) 1 ->
        x98_induced_subdivision H G.
