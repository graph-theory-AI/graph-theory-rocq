(** * Cycle.conjectures.X10 -- v2 clean cycle continuation *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X10 vocabulary ************************************************)

Definition x10_rainbow_cycle
    (G : sgraph) (n : nat) (col : {set G} -> 'I_n) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  uniq (map col (map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)))).

Definition x10_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition x10_colour_classes_large
    (G : sgraph) (n k : nat) (col : {set G} -> 'I_n) : Prop :=
  forall i : 'I_n, k <= #|[set e in x10_edge_set G | col e == i]|.

Definition x10_cycle_vertices (G : sgraph) (c : seq G) : {set G} :=
  [set v | v \in c].

Definition x10_longest_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\ 2 < size c /\
  forall c' : seq G, ucycle (--) c' -> 2 < size c' -> size c' <= size c.

(** ** X10 statements ******************************************************)

(** Corpus row: studies:std_aharoni_s_rainbow_generalization_of_the_caccetta_43
    Site: none
    Review: none
    English statement: (Aharoni, DeVos and Holzman, "Aharoni's Rainbow Generalization of
      the Caccetta-Haeggkvist Conjecture")
      For all positive natural numbers n and k and every simple graph G on exactly n
      vertices, if the edges of G are coloured with n colours in such a way that every
      colour class contains at least k edges, then G has a rainbow cycle of length at most
      the ceiling of n/k, that is, a closed walk visiting more than two distinct vertices
      without repetition whose consecutive-pair edges all receive pairwise distinct
      colours.
    Definitions: [x10_edge_set G] - the two-element vertex sets that are edges (X10.v);
      [x10_colour_classes_large G n k col] - every one of the n colour classes has at least
      k edges (X10.v); [x10_rainbow_cycle G n col c] - c is a [ucycle] of length more than
      two whose list of consecutive edge colours is duplicate-free (X10.v); [ceil_div a b]
      - the ceiling of a/b, with the MathComp convention that division by zero is zero
      (base/theories/base.v); [ucycle] - a closed walk with no repeated vertex (MathComp
      path.v).
    Notes: the colouring is typed as a map from vertex PAIRS, [{set G} -> 'I_n], so it is
      defined on all two-element sets and its restriction to edges is what the colour-class
      condition and the rainbow condition use. The corpus row is a studies slice with no
      site or review page. *)
Definition aharoni_rainbow_caccetta_haggkvist_statement : Prop :=
  forall (n k : nat) (G : sgraph) (col : {set G} -> 'I_n),
    0 < n -> 0 < k -> #|G| = n ->
    @x10_colour_classes_large G n k col ->
    exists c : seq G,
      @x10_rainbow_cycle G n col c /\
      size c <= ceil_div n k.

(** Corpus row: studies:std_smith_s_conjecture_longest_cycles_in_r_connected
    Site: none
    Review: none
    English statement: (Smith, "Smith's Conjecture (Longest Cycles in r-Connected
      Graphs)")
      For every natural number r at least 2, every r-connected simple graph G and any two
      longest cycles c and d of G, the sets of vertices of c and of d meet in at least r
      vertices.
    Definitions: [x10_longest_cycle G c] - c is a cycle of length more than two and no
      cycle of length more than two is longer (X10.v); [x10_cycle_vertices G c] - the set
      of vertices appearing in c (X10.v); [k_connected G r] - more than r vertices and
      deleting any fewer than r vertices leaves the graph connected
      (base/theories/base.v); [ucycle] (MathComp path.v).
    Notes: "longest cycle" is relative to cycles of length more than two, the genuine
      cycles of a simple graph; if the graph has no such cycle the hypotheses are
      unsatisfiable and the statement holds vacuously for it. The corpus row is a studies
      slice with no site or review page. *)
Definition smith_longest_cycles_r_connected_statement : Prop :=
  forall (r : nat) (G : sgraph) (c d : seq G),
    2 <= r ->
    k_connected G r ->
    @x10_longest_cycle G c ->
    @x10_longest_cycle G d ->
    r <= #|@x10_cycle_vertices G c :&: @x10_cycle_vertices G d|.
