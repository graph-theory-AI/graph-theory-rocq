(** * GTMisc.conjectures.X39 -- v2 coarse Menger row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X39 vocabulary ************************************************)

Fixpoint x39_ball (G : sgraph) (r : nat) (x : G) : {set G} :=
  if r is r'.+1 then x39_ball r' x :|: \bigcup_(z in x39_ball r' x) N(z)
  else [set x].

Definition x39_set_ball (G : sgraph) (r : nat) (S : {set G}) : {set G} :=
  \bigcup_(x in S) x39_ball r x.

Definition x39_path_vertices (G : sgraph) (p : seq G) : {set G} :=
  [set v | v \in p].

Definition x39_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Definition x39_pairwise_distant_paths
    (G : sgraph) (d : nat) (paths : seq (seq G)) : Prop :=
  forall p q : seq G,
    p \in paths -> q \in paths -> p != q ->
    [disjoint x39_path_vertices p & x39_path_vertices q] /\
    [disjoint x39_set_ball (d.-1) (x39_path_vertices p) & x39_path_vertices q].

Definition x39_has_k_distant_xy_paths
    (G : sgraph) (d k : nat) (X Y : {set G}) : Prop :=
  exists paths : seq (seq G),
    size paths = k /\
    uniq paths /\
    (forall p : seq G, p \in paths -> x39_xy_path X Y p) /\
    x39_pairwise_distant_paths d paths.

Definition x39_separates_xy
    (G : sgraph) (X Y A : {set G}) : Prop :=
  forall p : seq G,
    x39_xy_path X Y p ->
    [disjoint x39_path_vertices p & A] ->
    False.

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
