(** * GTMisc.conjectures.X116 -- v2 coarse Menger (bounded-separator) row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X116 vocabulary ***********************************************

    Coarse metric / path vocabulary, mirroring
    [GTMisc.conjectures.X39] so this file is self-contained.
    [x116_ball r x] / [x116_set_ball r S] are the closed [r]-ball around a
    vertex / vertex set; [x116_path_vertices p] is the vertex set of a walk;
    [x116_ST_path S T p] is a simple path from [S] to [T]. *)

Fixpoint x116_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x116_ball r' x :|: \bigcup_(z in x116_ball r' x) N(z)
  else [set x].

Definition x116_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x116_ball r x.

Definition x116_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x116_ST_path (G : sgraph) (S T : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in S /\ last x q \in T /\ uniq p /\ path (--) x q
  end.

(** Two paths are at distance at least [d] iff, in addition to being
    vertex-disjoint, the closed [d.-1]-ball around one avoids the vertex set of
    the other (no vertex of one lies within distance [d-1] of the other). *)
Definition x116_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x116_path_vertices p & x116_path_vertices q] /\
    [disjoint x116_set_ball (d.-1) (x116_path_vertices p) & x116_path_vertices q].

(** [k] distinct [S]-[T] paths that are pairwise at distance at least [d]. *)
Definition x116_has_k_distant_ST_paths
    (G : sgraph) (d k : nat) (S T : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x116_ST_path S T p) /\
    x116_pairwise_distant_paths d paths.

(** ** X116 statement *****************************************************)

(** Corpus row: studies:std_coarse_menger_conjecture
    Site: none
    Review: none
    English statement: (Albrechtsen, Huynh, Jacobs, Knappe and Wollan; independently
      Georgakopoulos and Papasoglu, coarse Menger conjecture)
      For all integers k, d >= 1 there is an integer l > 0 such that for every finite simple
      graph G and all vertex sets S and T, either G contains k distinct S-T paths that are
      pairwise at distance at least d, or there is a vertex set X with |X| <= k-1 such that
      every S-T path contains a vertex lying in the closed l-ball around X.
    Definitions: [x116_ball r x] / [x116_set_ball r S] - the closed r-ball around a vertex, and
      around a vertex set (this file); [x116_path_vertices p] - the vertex set of a walk (this
      file); [x116_ST_path S T p] - p is a simple path whose first vertex is in S and whose last
      vertex is in T (this file); [x116_pairwise_distant_paths d ps] - distinct paths of ps are
      vertex-disjoint and the closed (d-1)-ball around one avoids the other (this file);
      [x116_has_k_distant_ST_paths G d k S T] - k distinct such paths exist (this file).
    Notes: l is allowed to depend on both k and d (the quantifier shape is "for all k, d there
      is l"), which is what distinguishes this row from
      graph-theory-misc/theories/conjectures/X39.v, where a single constant c is chosen for each
      k and the separator radius is c*d.  "Pairwise at distance at least d" is rendered as
      vertex-disjointness together with the (d-1)-ball condition, so that d = 1 means exactly
      vertex-disjoint. *)
Definition coarse_menger_paths_bounded_separator_statement : Prop :=
  forall (k d : nat),
    1 <= k -> 1 <= d ->
    exists l : nat,
      0 < l /\
      forall (G : sgraph) (S T : {set G}),
        x116_has_k_distant_ST_paths d k S T \/
        exists X : {set G},
          #|X| <= k - 1 /\
          forall p : seq G,
            x116_ST_path S T p ->
            exists v : G,
              v \in x116_path_vertices p /\ v \in x116_set_ball l X.
