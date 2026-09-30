(** * Hypergraph.conjectures.XE1 -- Erdos open clean/bounded rows *)

From Hypergraph.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_complete_uniform_edges (T : finType) (r : nat) : {set {set T}} :=
  [set e : {set T} | #|e| == r].

Definition xe1_mono_3_clique (m n : nat) (col : {set 'I_m} -> bool) : Prop :=
  exists S : {set 'I_m},
    #|S| = n /\
    exists b : bool,
      forall e : {set 'I_m}, e \subset S -> #|e| = 3 -> col e = b.

Definition xe1_hypergraph_ramsey3 (n m : nat) : Prop :=
  forall col : {set 'I_m} -> bool, xe1_mono_3_clique n col.

Definition xe1_hypergraph_ramsey3_number (n m : nat) : Prop :=
  xe1_hypergraph_ramsey3 n m /\
  forall m' : nat, xe1_hypergraph_ramsey3 n m' -> m <= m'.

Definition xe1_contains_complete_uniform
    (T : finType) (E : {set {set T}}) (r q : nat) : Prop :=
  exists S : {set T},
    #|S| = q /\ forall e : {set T}, e \subset S -> #|e| = r -> e \in E.

Definition xe1_extremal_no_complete_uniform (n r q m : nat) : Prop :=
  (exists (T : finType) (E : {set {set T}}),
      [/\ #|T| = n, x6_uniform E r, ~ xe1_contains_complete_uniform E r q
        & #|E| = m]) /\
  forall m' : nat,
    (exists (T : finType) (E : {set {set T}}),
      [/\ #|T| = n, x6_uniform E r, ~ xe1_contains_complete_uniform E r q
        & #|E| = m']) ->
    m' <= m.

Definition xe1_complete_piece (T : finType) (E : {set {set T}}) (r : nat)
    (S : {set T}) : Prop :=
  (#|S| = r \/ #|S| = r.+1) /\
  forall e : {set T}, e \subset S -> #|e| = r -> e \in E.

Definition xe1_piece_covers_edge (T : finType) (r : nat)
    (P : {set T}) (e : {set T}) : Prop :=
  e \subset P /\ #|e| = r.

Definition xe1_pieces_pairwise_share_no_r_set
    (T : finType) (r m : nat) (P : 'I_m -> {set T}) : Prop :=
  forall i j : 'I_m, i != j ->
    forall e : {set T}, #|e| = r -> e \subset P i -> e \subset P j -> False.

Definition xe1_hypergraph_decomposition_bound
    (T : finType) (E : {set {set T}}) (r b : nat) : Prop :=
  exists m : nat, exists P : 'I_m -> {set T},
    m <= b /\
    (forall i : 'I_m, xe1_complete_piece E r (P i)) /\
    xe1_pieces_pairwise_share_no_r_set r P /\
    forall e : {set T}, e \in E -> exists i : 'I_m, xe1_piece_covers_edge r (P i) e.

Definition xe1_intersecting_hypergraph (T : finType) (E : {set {set T}}) : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e != f -> ~~ [disjoint e & f].

(** Corpus row: erdos:564
    Site: none
    Review: none
    English statement: (Erdos problem #564)
      Let R_3(n) be the least m such that every two-colouring of the three-element subsets of an
      m-element set contains a monochromatic complete 3-uniform hypergraph on n vertices.  There
      is a positive constant c such that R_3(n) is at least 2 raised to the power 2 raised to
      the power c times n, for all sufficiently large n.
    Definitions: [xe1_mono_3_clique m n col] - some n-element subset of the m-element host has
      all of its three-element subsets of the same colour (hypergraph-theory/theories/conjectures/XE1.v);
      [xe1_hypergraph_ramsey3 n m] - every two-colouring of the subsets of an m-element host
      yields such a clique (same file); [xe1_hypergraph_ramsey3_number n m] - m is the least
      such host size, i.e. m = R_3(n) (same file).
    Notes: the positive real constant c is presented as a positive rational cnum/cden and the
      exponent c*n as the natural-division floor (cnum * n) %/ cden, which only weakens the
      lower bound and so keeps the statement faithful.  The threshold N makes "for all
      sufficiently large n" explicit; both the constant and the threshold are chosen before n.
      The colouring is a function on all subsets of the host, but only three-element subsets are
      constrained. *)
Definition erdos_564_statement : Prop :=
  exists cnum cden N : nat,
    0 < cnum /\ 0 < cden /\
    forall n R : nat,
      N <= n ->
      xe1_hypergraph_ramsey3_number n R ->
      2 ^ (2 ^ ((cnum * n) %/ cden)) <= R.

(** Corpus row: erdos:719
    Site: none
    Review: none
    English statement: (Erdos problem #719)
      Let ex_r(n; K^r_(r+1)) be the maximum number of r-element hyperedges that can be placed on
      n vertices without forming a complete r-uniform hypergraph on r+1 vertices.  Then for
      r at least 2, every r-uniform hypergraph on n vertices is the union of at most
      ex_r(n; K^r_(r+1)) copies of complete r-uniform hypergraphs on r or on r+1 vertices, no
      two of which share an r-element set.
    Definitions: [xe1_complete_uniform_edges T r] - the family of all r-element subsets of T
      (hypergraph-theory/theories/conjectures/XE1.v); [xe1_contains_complete_uniform E r q] - some
      q-element vertex set has all of its r-element subsets in E (same file);
      [xe1_extremal_no_complete_uniform n r q m] - m is attained by, and bounds the hyperedge
      count of, every r-uniform hypergraph on n vertices with no complete r-uniform hypergraph
      on q vertices (same file); [xe1_complete_piece E r S] - S has r or r+1 vertices and all
      of its r-element subsets are hyperedges, i.e. S carries a copy of K^r_r or K^r_(r+1)
      inside E (same file); [xe1_piece_covers_edge r P e] - e is an r-element subset of the
      piece P (same file); [xe1_pieces_pairwise_share_no_r_set r P] - no r-element set is
      contained in two distinct pieces (same file);
      [xe1_hypergraph_decomposition_bound E r b] - E is covered by at most b such pieces,
      pairwise sharing no r-element set (same file); [x6_uniform E r] (hypergraph-theory/theories/conjectures/X6.v).
    Notes: "no two of which share a K^r_r" is read as "no r-element set is contained in two of
      the pieces"; "union of copies" is read as "every hyperedge of E lies inside some piece".
      The extremal number is introduced as a universally quantified number characterised by an
      "attained and maximal" pair, rather than by a maximum operator.
      [xe1_complete_uniform_edges] is defined in the file but is not used by this statement. *)
Definition erdos_719_statement : Prop :=
  forall (r n ex : nat) (T : finType) (E : {set {set T}}),
    2 <= r -> #|T| = n -> x6_uniform E r ->
    xe1_extremal_no_complete_uniform n r r.+1 ex ->
    xe1_hypergraph_decomposition_bound E r ex.

(** Corpus row: erdos:836
    Site: none
    Review: none
    English statement: (Erdos problem #836)
      Two questions, conjoined.  Let r be at least 2 and let H be an r-uniform hypergraph whose
      chromatic number is 3 - there is a three-colouring of the vertices with no monochromatic
      hyperedge, and no two-colouring does - and in which any two distinct hyperedges meet.
      First: there is a constant C such that every such H with no isolated vertex has at most
      C times r squared vertices.  Second: there is a positive constant c such that every such H
      has two distinct hyperedges meeting in at least c times r vertices.
    Definitions: [xe1_intersecting_hypergraph E] - any two distinct hyperedges of E meet
      (hypergraph-theory/theories/conjectures/XE1.v); [x6_uniform E r] - every hyperedge has exactly r
      vertices (hypergraph-theory/theories/conjectures/X6.v); [x6_chromatic_number E 3] - 3 is the least
      number of colours admitting a colouring with no monochromatic hyperedge (same file).
    Notes: "must contain O(r^2) many vertices" is the constant C quantified before r; "two edges
      which meet in >> r many vertices" is a positive rational c = cnum/cden with the bound
      cross-multiplied as cnum * r <= cden * #|e :&: f|.  The no-isolated-vertex hypothesis
      appears only in the first half, where it is load-bearing (the vertex type may contain
      vertices lying in no hyperedge, which would make the vertex bound false); the second half
      concerns hyperedges only and needs no such guard. *)
Definition erdos_836_statement : Prop :=
  (exists C : nat,
      forall (r : nat) (T : finType) (E : {set {set T}}),
        2 <= r -> x6_uniform E r -> x6_chromatic_number E 3 ->
        xe1_intersecting_hypergraph E ->
        (forall v : T, exists e : {set T}, e \in E /\ v \in e) ->
        #|T| <= C * r ^ 2) /\
  (exists cnum cden : nat,
      0 < cnum /\ 0 < cden /\
      forall (r : nat) (T : finType) (E : {set {set T}}),
        2 <= r -> x6_uniform E r -> x6_chromatic_number E 3 ->
        xe1_intersecting_hypergraph E ->
        exists e f : {set T},
          e \in E /\ f \in E /\ e != f /\ cnum * r <= cden * #|e :&: f|).
