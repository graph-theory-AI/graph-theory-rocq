(** * GTMisc.conjectures.X14 -- v2 matching and rainbow-path rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X14 vocabulary ************************************************)

Definition x14_edge_set (G : sgraph) : {set {set G}} :=
  simple_edge_set G.

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

(** Studies slice: Biedl-Demaine-Duncan-Fleischer-Kobourov subcubic matching
    conjecture. *)
Definition subcubic_matching_lower_bound_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    x14_subcubic G ->
    exists M : {set {set G}},
      @x14_matching G M /\
      9 * #|M| >= 3 * #|G| + x14_degree_two_count G.

(** Studies slice: Andersen's rainbow path conjecture. *)
Definition andersen_rainbow_path_statement : Prop :=
  forall (n : nat) (C : finType) (col : {set complete n} -> C),
    2 <= n ->
    @x14_proper_edge_colouring (complete n) C col ->
    exists p : seq (complete n),
      @x14_rainbow_path (complete n) C col p /\ size p = n.-1.
