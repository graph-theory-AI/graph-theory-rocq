(** * GTMisc.conjectures.X14 -- v2 matching and rainbow-path rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X14 vocabulary ************************************************)

Definition x14_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x14_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset x14_edge_set G /\
  forall e f : {set G},
    e \in M -> f \in M -> e != f -> [disjoint e & f].

Definition x14_subcubic (G : sgraph) : Prop :=
  forall v : G, #|N(v)| <= 3.

Definition x14_degree_two_count (G : sgraph) : nat :=
  #|[set v : G | #|N(v)| == 2]|.

Definition x14_path_edges (G : sgraph) (p : seq G) : seq {set G} :=
  map (fun e : G * G => [set e.1; e.2]) (zip p (behead p)).

Definition x14_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

Definition x14_proper_edge_colouring
    (G : sgraph) (C : finType) (col : {set G} -> C) : Prop :=
  forall e f : {set G},
    e \in x14_edge_set G ->
    f \in x14_edge_set G ->
    e != f ->
    ~~ [disjoint e & f] ->
    col e != col f.

Definition x14_rainbow_path
    (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) : Prop :=
  @x14_genuine_path G p /\ uniq (map col (@x14_path_edges G p)).

(** ** X14 statements ******************************************************)

(** Corpus row: studies:std_biedl_demaine_duncan_fleischer_kobourov_subcubic
    Site: none
    Review: none
    English statement: (Biedl, Demaine, Duncan, Fleischer and Kobourov, subcubic matching
      conjecture)
      Every finite simple graph G with at least one vertex and maximum degree at most 3
      contains a matching M with 9 * |M| >= 3 * |V(G)| + n2, where n2 is the number of vertices
      of degree exactly two.
    Definitions: [x14_edge_set G] - the edges of G as two-element vertex sets (this file);
      [x14_matching G M] - M is a set of edges that are pairwise disjoint (this file);
      [x14_subcubic G] - every vertex has degree at most 3 (this file);
      [x14_degree_two_count G] - the number of vertices of degree exactly 2 (this file).
    Notes: the source inequality nu(G) >= (3n + n2)/9 is stated fraction-free as
      9 * |M| >= 3n + n2 for an explicitly exhibited matching M, which is equivalent since the
      matching number is the maximum size of a matching.  The empty graph is excluded by the
      guard [0 < #|G|]. *)
Definition subcubic_matching_lower_bound_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    x14_subcubic G ->
    exists M : {set {set G}},
      @x14_matching G M /\
      9 * #|M| >= 3 * #|G| + x14_degree_two_count G.

(** Corpus row: studies:std_andersen_s_conjecture
    Site: none
    Review: none
    English statement: (Andersen, Andersen's conjecture)
      For every n >= 2 and every proper edge colouring of the complete graph on n vertices,
      there is a rainbow path with n-1 vertices, i.e. a simple path whose n-2 edges all receive
      distinct colours.
    Definitions: [x14_edge_set G] - the edges of G as two-element vertex sets (this file);
      [x14_path_edges p] - the edges of a vertex sequence, as consecutive pairs (this file);
      [x14_genuine_path p] - p is a non-empty sequence of distinct vertices consecutive ones of
      which are adjacent (this file); [x14_proper_edge_colouring G col] - distinct edges that
      meet receive distinct colours (this file); [x14_rainbow_path col p] - p is a genuine path
      whose edge colours are pairwise distinct (this file); [complete n] - the complete graph on
      n vertices (coq-graph-theory).
    Notes: "a rainbow path of length n-2" is rendered by its vertex count, [size p = n.-1],
      the path having one more vertex than edges.  Colours range over an arbitrary [finType],
      so no bound on the number of colours is imposed. *)
Definition andersen_rainbow_path_statement : Prop :=
  forall (n : nat) (C : finType) (col : {set complete n} -> C),
    2 <= n ->
    @x14_proper_edge_colouring (complete n) C col ->
    exists p : seq (complete n),
      @x14_rainbow_path (complete n) C col p /\ size p = n.-1.
