(** * Chromatic.migration.proper_colouring -- C5 frozen supplied colourings

    Frozen at a6db537. Supplied function carriers and palettes are unchanged.
    Boolean source bridges are equalities; Prop source bridges are iff. Counts
    still enumerate labelled finite functions. No surjectivity or positivity
    guard is added. The ten full statements retain their existing readings and
    statuses, including the unrelated blocked X162 Kempe-step defect.
    X64Original combines the pre-M1/A3 graph chain with frozen colouring;
    X83Original combines the B3 induced-path chain with frozen colouring.
    Historical migration bodies are imported unchanged. *)

From GTBase Require Import base colourings.
From Chromatic.conjectures Require Import X3 X63 X64 X68 X83 X109 X162 X187.
From Chromatic.migration Require delete_edge consecutive_in_path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x3_proper_colouring (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall u v : G, u -- v -> col u != col v.

Definition x63_proper_colouring
    (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x68_proper_three_colouring (G : sgraph) (col : G -> 'I_3) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x109_proper_colouring
    (G : sgraph) (q : nat) (col : {ffun G -> 'I_q}) : bool :=
  [forall x : G, [forall y : G, (x -- y) ==> (col x != col y)]].

Definition x162_proper_colouring (G : sgraph) (q : nat) (col : G -> 'I_q) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x187_proper_3_colouring (G : sgraph) (col : G -> 'I_3) : Prop :=
  forall x y : G, x -- y -> col x != col y.

End Legacy.

Module X3Legacy.

Definition rainbow_consecutive_vertices_in_hole_statement : Prop :=
  forall s kappa : nat, exists n : nat,
    forall (G : sgraph) (C : finType) (col : G -> C),
      ω([set: G]) <= kappa ->
      n <= χ([set: G]) ->
      Legacy.x3_proper_colouring col ->
      x3_rainbow_hole_run col s.

End X3Legacy.

Module X63Legacy.

Definition x63_k_homogeneous_colouring (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (col : G -> C),
    Legacy.x63_proper_colouring col /\
    forall v : G, #|x63_neighbour_colours col v| = k.

Definition x63_k_homogeneous_with
    (G : sgraph) (C : finType) (col : G -> C) (k : nat) : Prop :=
  Legacy.x63_proper_colouring col /\
  forall v : G, #|x63_neighbour_colours col v| = k.

Definition cubic_two_homogeneous_four_colour_statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    X63Legacy.x63_k_homogeneous_colouring G 2 ->
    exists col : G -> 'I_4,
      X63Legacy.x63_k_homogeneous_with col 2.

End X63Legacy.

Module X64Original.

Definition finite_bridgeless_cubic_two_homogeneous_exceptions_statement : Prop :=
  exists N : nat,
    forall G : sgraph,
      connected [set: G] ->
      regular G 3 ->
      delete_edge.X64Original.bridgeless G ->
      N <= #|G| ->
      X63Legacy.x63_k_homogeneous_colouring G 2.

End X64Original.

Module X68Legacy.

Definition triangle_free_planar_distant_precolouring_extension_statement : Prop :=
  exists d : nat,
    2 <= d /\
    forall (G : sgraph) (S : {set G}) (psi : G -> 'I_3),
      wagner_planar G ->
      triangle_free G ->
      x68_pairwise_distance_at_least d S ->
      exists col : G -> 'I_3,
        Legacy.x68_proper_three_colouring col /\
        forall v : G, v \in S -> col v = psi v.

End X68Legacy.

Module X83Original.

Definition aravind_rainbow_induced_chromatic_path_statement : Prop :=
  forall (G : sgraph) (C : finType) (col : G -> C),
    0 < #|G| ->
    triangle_free G ->
    Legacy.x3_proper_colouring col ->
    exists p : seq G,
      size p = χ([set: G]) /\
      consecutive_in_path.X83Legacy.rainbow_induced_path col p.

End X83Original.

Module X109Legacy.

Definition x109_recolour_walk
    (G : sgraph) (q : nat)
    (c d : {ffun G -> 'I_q}) (w : seq {ffun G -> 'I_q}) : Prop :=
  path (x109_recolour_step (G := G) (q := q)) c w /\
  last c w = d /\
  all (Legacy.x109_proper_colouring (G := G) (q := q)) (c :: w).

Definition x109_recolour_diameter_at_most
    (G : sgraph) (q bound : nat) : Prop :=
  forall c d : {ffun G -> 'I_q},
    Legacy.x109_proper_colouring c ->
    Legacy.x109_proper_colouring d ->
    exists w : seq {ffun G -> 'I_q},
      size w <= bound /\ X109Legacy.x109_recolour_walk c d w.

Definition cereceda_degenerate_recolouring_quadratic_diameter_statement : Prop :=
  exists C : nat,
    forall (k n : nat) (G : sgraph),
      #|G| = n ->
      k_degenerate G k ->
      X109Legacy.x109_recolour_diameter_at_most G (k + 2) (C * n ^ 2).

End X109Legacy.

Module X162Legacy.

Definition x162_kempe_class_for_q (G : sgraph) (q : nat) : Prop :=
  forall col1 col2 : G -> 'I_q,
    Legacy.x162_proper_colouring col1 ->
    Legacy.x162_proper_colouring col2 ->
    @x162_kempe_reachable G q col1 col2.

Definition wsk_triangular_lattice_q5_kempe_class_statement : Prop :=
  forall m n : nat,
    0 < m -> 0 < n ->
    X162Legacy.x162_kempe_class_for_q (x162_periodic_triangular_lattice m n) 5.

End X162Legacy.

Module X187Legacy.

Definition planar_triangle_free_request_graph_fraction_statement : Prop :=
  exists p q : nat,
    [/\ 0 < p, p <= q &
      forall (G : sgraph) (ReqEq ReqNeq : {set G}) (w : G -> nat),
        wagner_planar G ->
        x187_triangle_free G ->
        x187_request_graph ReqEq ReqNeq w ->
        exists col : G -> 'I_3,
          Legacy.x187_proper_3_colouring col /\
          x187_satisfies_fraction ReqEq ReqNeq w p q col].

End X187Legacy.

(** ** Unconditional source, chain and full-statement certificates. *)

Lemma x3_proper_colouring_compat (G : sgraph) (C : finType) (col : G -> C) :
  Legacy.x3_proper_colouring col <-> x3_proper_colouring col.
Proof. split=> h; first by apply/proper_colouringP.
exact: (elimT (proper_colouringP col) h). Qed.

Lemma x63_proper_colouring_compat (G : sgraph) (C : finType) (col : G -> C) :
  Legacy.x63_proper_colouring col <-> x63_proper_colouring col.
Proof. split=> h; first by apply/proper_colouringP.
exact: (elimT (proper_colouringP col) h). Qed.

Lemma x68_proper_three_colouring_compat (G : sgraph) (col : G -> 'I_3) :
  Legacy.x68_proper_three_colouring col <-> x68_proper_three_colouring col.
Proof. split=> h; first by apply/proper_colouringP.
exact: (elimT (proper_colouringP col) h). Qed.

Lemma x109_proper_colouring_compat (G : sgraph) (q : nat) (col : {ffun G -> 'I_q}) :
  Legacy.x109_proper_colouring col = x109_proper_colouring col.
Proof. by rewrite /Legacy.x109_proper_colouring /x109_proper_colouring proper_colouringE. Qed.

Lemma x162_proper_colouring_compat (G : sgraph) (q : nat) (col : G -> 'I_q) :
  Legacy.x162_proper_colouring col <-> x162_proper_colouring col.
Proof. split=> h; first by apply/proper_colouringP.
exact: (elimT (proper_colouringP col) h). Qed.

Lemma x187_proper_3_colouring_compat (G : sgraph) (col : G -> 'I_3) :
  Legacy.x187_proper_3_colouring col <-> x187_proper_3_colouring col.
Proof. split=> h; first by apply/proper_colouringP.
exact: (elimT (proper_colouringP col) h). Qed.

Lemma x63_k_homogeneous_colouring_compat (G : sgraph) (k : nat) :
  X63Legacy.x63_k_homogeneous_colouring G k <-> x63_k_homogeneous_colouring G k.
Proof.
rewrite /X63Legacy.x63_k_homogeneous_colouring /x63_k_homogeneous_colouring.
setoid_rewrite x63_proper_colouring_compat.
reflexivity.
Qed.

Lemma x63_k_homogeneous_with_compat (G : sgraph) (C : finType) (col : G -> C) (k : nat) :
  X63Legacy.x63_k_homogeneous_with col k <-> x63_k_homogeneous_with col k.
Proof.
rewrite /X63Legacy.x63_k_homogeneous_with /x63_k_homogeneous_with.
setoid_rewrite x63_proper_colouring_compat.
reflexivity.
Qed.

Lemma x109_recolour_walk_compat (G : sgraph) (q : nat) (c d : {ffun G -> 'I_q}) (w : seq {ffun G -> 'I_q}) :
  X109Legacy.x109_recolour_walk c d w <-> x109_recolour_walk c d w.
Proof.
rewrite /X109Legacy.x109_recolour_walk /x109_recolour_walk.
by rewrite (eq_all (@x109_proper_colouring_compat G q)).
Qed.

Lemma x109_recolour_diameter_at_most_compat (G : sgraph) (q bound : nat) :
  X109Legacy.x109_recolour_diameter_at_most G q bound <-> x109_recolour_diameter_at_most G q bound.
Proof.
rewrite /X109Legacy.x109_recolour_diameter_at_most /x109_recolour_diameter_at_most.
setoid_rewrite x109_proper_colouring_compat.
setoid_rewrite x109_recolour_walk_compat.
reflexivity.
Qed.

Lemma x162_kempe_class_for_q_compat (G : sgraph) (q : nat) :
  X162Legacy.x162_kempe_class_for_q G q <-> x162_kempe_class_for_q G q.
Proof.
rewrite /X162Legacy.x162_kempe_class_for_q /x162_kempe_class_for_q.
setoid_rewrite x162_proper_colouring_compat.
reflexivity.
Qed.

Lemma rainbow_consecutive_vertices_in_hole_statement_compat :
  X3Legacy.rainbow_consecutive_vertices_in_hole_statement <->
  rainbow_consecutive_vertices_in_hole_statement.
Proof.
rewrite /X3Legacy.rainbow_consecutive_vertices_in_hole_statement /rainbow_consecutive_vertices_in_hole_statement.
setoid_rewrite x3_proper_colouring_compat.
reflexivity.
Qed.

Lemma cubic_two_homogeneous_four_colour_statement_compat :
  X63Legacy.cubic_two_homogeneous_four_colour_statement <->
  cubic_two_homogeneous_four_colour_statement.
Proof.
rewrite /X63Legacy.cubic_two_homogeneous_four_colour_statement /cubic_two_homogeneous_four_colour_statement.
setoid_rewrite x63_k_homogeneous_colouring_compat.
setoid_rewrite x63_k_homogeneous_with_compat.
reflexivity.
Qed.

Lemma finite_bridgeless_cubic_two_homogeneous_exceptions_statement_compat :
  X64Original.finite_bridgeless_cubic_two_homogeneous_exceptions_statement <->
  finite_bridgeless_cubic_two_homogeneous_exceptions_statement.
Proof.
rewrite /X64Original.finite_bridgeless_cubic_two_homogeneous_exceptions_statement /finite_bridgeless_cubic_two_homogeneous_exceptions_statement.
setoid_rewrite delete_edge.x64_bridgeless_original_compat.
setoid_rewrite x63_k_homogeneous_colouring_compat.
reflexivity.
Qed.

Lemma triangle_free_planar_distant_precolouring_extension_statement_compat :
  X68Legacy.triangle_free_planar_distant_precolouring_extension_statement <->
  triangle_free_planar_distant_precolouring_extension_statement.
Proof.
rewrite /X68Legacy.triangle_free_planar_distant_precolouring_extension_statement /triangle_free_planar_distant_precolouring_extension_statement.
setoid_rewrite x68_proper_three_colouring_compat.
reflexivity.
Qed.

Lemma aravind_rainbow_induced_chromatic_path_statement_compat :
  X83Original.aravind_rainbow_induced_chromatic_path_statement <->
  aravind_rainbow_induced_chromatic_path_statement.
Proof.
rewrite /X83Original.aravind_rainbow_induced_chromatic_path_statement /aravind_rainbow_induced_chromatic_path_statement.
setoid_rewrite x3_proper_colouring_compat.
setoid_rewrite consecutive_in_path.x83_rainbow_induced_path_compat.
reflexivity.
Qed.

Lemma cereceda_degenerate_recolouring_quadratic_diameter_statement_compat :
  X109Legacy.cereceda_degenerate_recolouring_quadratic_diameter_statement <->
  cereceda_degenerate_recolouring_quadratic_diameter_statement.
Proof.
rewrite /X109Legacy.cereceda_degenerate_recolouring_quadratic_diameter_statement /cereceda_degenerate_recolouring_quadratic_diameter_statement.
setoid_rewrite x109_recolour_diameter_at_most_compat.
reflexivity.
Qed.

Lemma wsk_triangular_lattice_q5_kempe_class_statement_compat :
  X162Legacy.wsk_triangular_lattice_q5_kempe_class_statement <->
  wsk_triangular_lattice_q5_kempe_class_statement.
Proof.
rewrite /X162Legacy.wsk_triangular_lattice_q5_kempe_class_statement /wsk_triangular_lattice_q5_kempe_class_statement.
setoid_rewrite x162_kempe_class_for_q_compat.
reflexivity.
Qed.

Lemma planar_triangle_free_request_graph_fraction_statement_compat :
  X187Legacy.planar_triangle_free_request_graph_fraction_statement <->
  planar_triangle_free_request_graph_fraction_statement.
Proof.
split=> -[p [q [p0 pq h]]]; exists p, q; split=> // G E N w gp tf rq;
  have [col [hc hs]] := h G E N w gp tf rq;
  exists col; split=> //.
- exact: (proj1 (x187_proper_3_colouring_compat col) hc).
- exact: (proj2 (x187_proper_3_colouring_compat col) hc).
Qed.
