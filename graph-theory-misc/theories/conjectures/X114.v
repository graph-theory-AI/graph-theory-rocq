(** * GTMisc.conjectures.X114 -- v2 subcubic induced-subdivision NP-completeness row *)

From GTBase Require Export base.
From GTBase Require Import model_support induced_paths induced_subdivisions.
From GTMisc.conjectures Require Import D7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X114 vocabulary ***********************************************)

(** Induced-subdivision model, replicated from Extremal.conjectures.X98
    (self-contained: graph-theory-misc does not import extremal-graph-theory).
    [x114_induced_subdivision H G] holds iff G contains a subdivision of H as an
    INDUCED subgraph: injective branch vertices, internally-disjoint induced
    edge-paths, and global inducedness (the only G-edges among model vertices join
    consecutive path vertices). *)

Definition x114_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  seq_consecutive p u v.

(** Since the B22 library migration (2026-10-03) a transparent alias of
    [GTBase.induced_paths.induced_path_between] (the same body by conversion); the original body
    is frozen and certified in theories/migration/induced_paths.v. *)
Definition x114_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  induced_path_between a b p.

Definition x114_internal (G : sgraph) (p : seq G) (a b x : G) : Prop :=
  x \in p /\ x != a /\ x != b.

Definition x114_model_vertex (H G : sgraph)
    (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop := model_support br ep x.

(** The strong induced-subdivision model is the canonical
    [GTBase.induced_subdivisions.induced_subdivision_model] (pattern before host).  The
    definitions below keep the local constructor and projection names with their exact
    types and implicit arguments; every field formula is convertible to the canonical one. *)
Definition x114_induced_subdivision_model (H G : sgraph) : Type := induced_subdivision_model H G.

Definition X114Model (H G : sgraph) (x114_branch : H -> G) (x114_branch_injective : injective x114_branch)
    (x114_edge_path : H -> H -> seq G)
    (x114_edge_path_valid :
       forall u v : H,
         u -- v ->
         x114_induced_path_between
           (x114_branch u) (x114_branch v) (x114_edge_path u v))
    (x114_internal_avoids_branch :
       forall (u v w : H) (x : G),
         u -- v ->
         x114_internal (x114_edge_path u v) (x114_branch u) (x114_branch v) x ->
         x != x114_branch w)
    (x114_paths_internally_disjoint :
       forall (u v u' v' : H) (x : G),
         u -- v -> u' -- v' ->
         x114_internal (x114_edge_path u v) (x114_branch u) (x114_branch v) x ->
         x114_internal (x114_edge_path u' v') (x114_branch u') (x114_branch v') x ->
         (u = u' /\ v = v') \/ (u = v' /\ v = u'))
    (x114_global_induced :
       forall x y : G,
         x114_model_vertex x114_branch x114_edge_path x ->
         x114_model_vertex x114_branch x114_edge_path y ->
         x -- y ->
         exists u v : H, u -- v /\ x114_consecutive_in_path (x114_edge_path u v) x y) :
    x114_induced_subdivision_model H G :=
  @InducedSubdivisionModel H G x114_branch x114_branch_injective x114_edge_path x114_edge_path_valid
    x114_internal_avoids_branch x114_paths_internally_disjoint x114_global_induced.

Definition x114_branch (H G : sgraph) (x0 : x114_induced_subdivision_model H G) : H -> G :=
  isd_branch x0.

Definition x114_branch_injective (H G : sgraph) (x0 : x114_induced_subdivision_model H G) :
    injective (x114_branch x0) :=
  @isd_branch_injective H G x0.

Definition x114_edge_path (H G : sgraph) (x0 : x114_induced_subdivision_model H G) : H -> H -> seq G :=
  isd_edge_path x0.

Definition x114_edge_path_valid (H G : sgraph) (x0 : x114_induced_subdivision_model H G) :
    forall u v : H,
      u -- v ->
      x114_induced_path_between (x114_branch x0 u) (x114_branch x0 v) (x114_edge_path x0 u v) :=
  @isd_edge_path_valid H G x0.

Definition x114_internal_avoids_branch (H G : sgraph) (x0 : x114_induced_subdivision_model H G) :
    forall (u v w : H) (x : G),
      u -- v ->
      x114_internal (x114_edge_path x0 u v) (x114_branch x0 u) (x114_branch x0 v) x ->
      x != x114_branch x0 w :=
  @isd_internal_avoids_branch H G x0.

Definition x114_paths_internally_disjoint (H G : sgraph) (x0 : x114_induced_subdivision_model H G) :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x114_internal (x114_edge_path x0 u v) (x114_branch x0 u) (x114_branch x0 v) x ->
      x114_internal (x114_edge_path x0 u' v') (x114_branch x0 u') (x114_branch x0 v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u') :=
  @isd_paths_internally_disjoint H G x0.

Definition x114_global_induced (H G : sgraph) (x0 : x114_induced_subdivision_model H G) :
    forall x y : G,
      x114_model_vertex (x114_branch x0) (x114_edge_path x0) x ->
      x114_model_vertex (x114_branch x0) (x114_edge_path x0) y ->
      x -- y ->
      exists u v : H, u -- v /\ x114_consecutive_in_path (x114_edge_path x0 u v) x y :=
  @isd_global_induced H G x0.

Arguments X114Model [H G] [x114_branch] x114_branch_injective [x114_edge_path]
  x114_edge_path_valid x114_internal_avoids_branch x114_paths_internally_disjoint x114_global_induced.
Arguments x114_branch [H G] x0 _.
Arguments x114_branch_injective [H G x0 x1 x2] _.
Arguments x114_edge_path [H G] x0 _ _.
Arguments x114_edge_path_valid [H G] x0 [u v] _.
Arguments x114_internal_avoids_branch [H G x0 u v] w [x] _ _.
Arguments x114_paths_internally_disjoint [H G x0 u v u' v' x] _ _ _ _.
Arguments x114_global_induced [H G x0 x y] _ _ _.

Definition x114_induced_subdivision (H G : sgraph) : Prop := induced_subdivision H G.

(** The H-INDUCED-SUBDIVISION-CONTAINMENT decision problem ([H]-ISC), packaged
    as a [D7.problem]: input a graph G (size = #|G|), YES iff G contains an
    induced subdivision of H. *)
Definition x114_hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => x114_induced_subdivision H G |}.

(** NP-completeness on the D7 complexity layer: in NP AND NP-hard. *)
Definition x114_np_complete (P : problem) : Prop := in_NP P /\ NP_hard P.

(** Subcubic = maximum degree at most three. *)
Definition x114_subcubic (H : sgraph) : Prop := subcubic H.

(** ** X114 statements *****************************************************)

(** Corpus row: studies:std_chudnovsky_seymour_trotignon_question_on_subcubi
    Site: none
    Review: none
    English statement: (Chudnovsky, Seymour and Trotignon, question on subcubic induced
      subdivisions)
      There is a finite simple graph H of maximum degree at most 3 such that the decision
      problem "does the input graph G contain an induced subdivision of H?" is both in NP and
      NP-hard.
    Definitions: [x114_consecutive_in_path], [x114_induced_path_between a b p] - p is an
      induced path from a to b, i.e. a simple adjacency-path whose only edges are consecutive
      pairs (this file); [x114_internal], [x114_model_vertex] - the internal vertices of a path
      and the vertices used by a subdivision model (this file);
      [x114_induced_subdivision_model H G] - injective branch vertices, internally disjoint
      induced edge-paths avoiding the other branch vertices, and global inducedness: the only
      edges of G among model vertices join consecutive path vertices (this file);
      [x114_induced_subdivision H G] - such a model exists (this file);
      [x114_hisc_problem H] - that containment problem packaged as a [problem], instances being
      graphs with size |V(G)| (this file); [x114_np_complete P] - [in_NP P] and [NP_hard P]
      (this file); [x114_subcubic H] - [Delta H <= 3] (this file); [problem], [in_NP],
      [NP_hard], [poly_reduces] - the machine-free relational complexity layer of
      graph-theory-misc/theories/conjectures/D7.v, where "polynomial time" is an abstract cost
      bound a*n^d+b rather than a machine model; [Delta] - maximum degree (GTBase).
    Notes: the induced-subdivision model is replicated byte for byte from
      extremal-graph-theory/theories/conjectures/X98.v because graph-theory-misc does not
      import that package.  The graph content is faithful; the complexity wrapper is the
      corpus-standard relational proxy also used by the done row
      opg:complexity_of_the_h_factor_problem, and is weaker than a machine-model NP-completeness
      claim. *)
Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    x114_subcubic H /\ x114_np_complete (x114_hisc_problem H).
