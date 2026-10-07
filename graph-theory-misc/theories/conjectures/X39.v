(** * GTMisc.conjectures.X39 -- v2 coarse Menger row *)

From GTBase Require Export base.
From GTBase Require Import balls distant_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X39 vocabulary ************************************************)

Definition x39_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  ball r x.

Definition x39_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  set_ball r S.

Definition x39_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  seq_vertices p.

Definition x39_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  seq_set_path X Y p.

(** Since the B27 library migration (2026-10-03) a transparent alias of
    [GTBase.distant_paths.pairwise_distant_seqs]: for unequal sequence values of the family, the closed
    [d.-1]-set-ball around one support misses the other (so [d] = 0 and 1 mean disjoint supports).  The former
    vertex-disjointness conjunct is redundant and dropped ([pairwise_distant_seqsP]).  The former body is
    frozen and certified equivalent in theories/migration/distant_paths.v. *)
Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  pairwise_distant_seqs d paths.

(** Since the B27 library migration (2026-10-03) a transparent alias of
    [GTBase.distant_paths.has_k_distant_set_paths]: exactly [k] distinct set-to-set paths whose unequal values
    satisfy [pairwise_distant_seqs d].  The former body is frozen and certified equivalent in
    theories/migration/distant_paths.v. *)
Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  has_k_distant_set_paths d k X Y.

(** Since the B26 library migration (2026-10-03) a transparent alias of upstream
    [GraphTheory.core.connectivity.separator G X Y A]: every packaged path from X to Y meets A, the
    endpoints may lie in A and one-vertex paths count.  The former sequence body is frozen and
    certified equivalent, through [GTBase.set_separators.seq_separatorP], in
    theories/migration/set_separators.v. *)
Definition x39_separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  separator G X Y A.

(** ** X39 statements ******************************************************)

(** Corpus row: studies:std_coarse_menger_conjecture_georgakopoulos_papasogl
    Site: none
    Review: none
    English statement: (Georgakopoulos and Papasoglu; also Albrechtsen et al., coarse Menger
      conjecture)
      For every k there is a c such that for every d, every finite simple graph G and all
      vertex sets X and Y, either G contains k distinct X-Y paths pairwise at distance at
      least d, or there is a vertex set Z with |Z| < k such that the closed (c*d)-ball around
      Z meets every X-Y path.
    Definitions: [x39_ball r x] / [x39_set_ball r S] - the closed r-ball around a vertex and
      around a vertex set (this file); [x39_path_vertices p] - the vertex set of a walk (this
      file); [x39_xy_path X Y p] - a simple path from X to Y (this file);
      [x39_pairwise_distant_paths d ps] - distinct paths of ps are vertex-disjoint and the
      closed (d-1)-ball around one avoids the other (this file);
      [x39_has_k_distant_xy_paths G d k X Y] - k distinct such paths exist (this file);
      [x39_separates_xy X Y A] - no X-Y path avoids A, i.e. A separates X from Y (this file).
    Notes: the constant c depends only on k and the separator radius is c*d, which is what
      distinguishes this row from graph-theory-misc/theories/conjectures/X116.v, where the
      radius is an arbitrary function of both k and d.  "Distance at least d" is rendered as
      vertex-disjointness together with the (d-1)-ball condition, so d = 1 means exactly
      vertex-disjoint. *)
Definition coarse_menger_ball_separator_statement : Prop :=
  forall k : nat, exists c : nat,
    forall (d : nat) (G : sgraph) (X Y : {set G}),
      x39_has_k_distant_xy_paths d k X Y \/
      exists Z : {set G},
        #|Z| < k /\
        x39_separates_xy X Y (x39_set_ball (c * d) Z).
