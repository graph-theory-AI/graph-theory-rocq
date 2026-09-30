(** * Hypergraph.conjectures.X108 -- v2 3-uniform Burr-Erdos row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X108 vocabulary ***********************************************)

Definition x108_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x108_degree_in
    (T : finType) (E : {set {set T}}) (W : {set T}) (v : T) : nat :=
  #|[set e in E | (v \in e) && (e \subset W)]|.

Definition x108_d_degenerate (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall W : {set T},
    W != set0 ->
    exists v : T, v \in W /\ x108_degree_in E W v <= d.

Definition x108_image_edge
    (T U : finType) (f : T -> U) (e : {set T}) : {set U} :=
  [set y : U | [exists x : T, (x \in e) && (y == f x)]].

Definition x108_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x108_image_edge f e) = colour.

Definition x108_two_colour_ramsey_at_most
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, x108_monochromatic_copy E col.

(** ** X108 statements *****************************************************)

(** Corpus row: studies:std_burr_erd_s_conjecture_for_3_uniform_hypergraphs
    Site: none
    Review: none
    English statement: (Burr and Erdos, conjecture for 3-uniform hypergraphs)
      For every d there is a constant c depending only on d such that for every d-degenerate
      3-uniform hypergraph H on n vertices, every two-colouring of the three-element subsets of
      a host set of c times n vertices contains a monochromatic copy of H; that is, the
      two-colour Ramsey number of H is at most c(d) times n.
    Definitions: [x108_uniform E r] - every hyperedge has exactly r vertices
      (hypergraph-theory/theories/conjectures/X108.v); [x108_degree_in E W v] - the number of
      hyperedges contained in W that contain v (same file); [x108_d_degenerate E d] - every
      nonempty vertex set W contains a vertex whose degree inside W is at most d (same file);
      [x108_image_edge f e] - the image of the hyperedge e under the map f (same file);
      [x108_monochromatic_copy E col] - there are a colour and an injection of the vertices of
      H into the host such that the image of every hyperedge receives that colour (same file);
      [x108_two_colour_ramsey_at_most E N] - every two-colouring of the subsets of an N-element
      host admits such a copy (same file).
    Notes: the constant c is chosen after d and before the hypergraph, matching "c(d) depending
      only on d".  Instead of naming the Ramsey number, the statement says that a host of
      c * n vertices already forces a monochromatic copy, which is equivalent because forcing is
      monotone in the host size.  The colouring is a function on all subsets of the host, but
      only the images of hyperedges (three-element sets) are constrained, so its other values
      are irrelevant. *)
Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        x108_uniform E 3 ->
        x108_d_degenerate E d ->
        x108_two_colour_ramsey_at_most E (c * #|T|).
