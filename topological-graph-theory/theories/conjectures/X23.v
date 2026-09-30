(** * Topological.conjectures.X23 -- v2 planar colouring layout rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X23 vocabulary ************************************************)

Definition x23_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

Definition x23_nonrepetitive_colouring
    (G : sgraph) (k : nat) (col : G -> 'I_k) : Prop :=
  forall (p : seq G) (h : nat),
    x23_genuine_path p ->
    size p = 2 * h ->
    0 < h ->
    map col (take h p) != map col (take h (drop h p)).

Definition x23_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x23_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (x23_edge_colour_rel col i).
Proof.
by move=> x y; rewrite /x23_edge_colour_rel sg_sym setUC.
Qed.

Lemma x23_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (x23_edge_colour_rel col i).
Proof. by move=> x; rewrite /x23_edge_colour_rel sg_irrefl. Qed.

Definition x23_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (x23_edge_colour_sym col i) (x23_edge_colour_irrefl col i).

Definition x23_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x23_colour_graph col i] /\
  Delta (x23_colour_graph col i) <= 2.

Definition x23_linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q,
    forall i : 'I_q, x23_linear_forest_colour col i.

Definition x23_linear_arboricity (G : sgraph) (q : nat) : Prop :=
  x23_linear_arboricity_at_most G q /\
  forall q' : nat, x23_linear_arboricity_at_most G q' -> q <= q'.

(** ** X23 statements ******************************************************)

(** Corpus row: studies:std_alon_grytczuk_ha_uszczak_riordan_conjecture
    Site: none
    Review: none
    English statement: (Alon, Grytczuk, Haluszczak, Riordan 2002, studies slice)
      Planar graphs have bounded nonrepetitive chromatic number: there is a constant k such
      that every planar graph G satisfies pi(G) <= k.  In the Rocq body: there is a positive
      natural k such that every finite simple graph with no K5 and no K3,3 minor admits a
      vertex colouring with k colours in which no path has a repetitive colour sequence.
    Definitions: [x23_genuine_path G p] - p is a non-empty duplicate-free list of vertices
      consecutively adjacent, i.e. an honest path (this file);
      [x23_nonrepetitive_colouring G k col] - for every genuine path p of even length 2h with
      h > 0, the colour sequence of the first h vertices differs from that of the last h
      (this file); [wagner_planar] - base/theories/base.v.
    Notes: The source constant was later determined (Dujmovic, Esperet, Joret, Walczak, Wood
      2020: planar graphs are nonrepetitively 768-colourable), but the row states the
      bounded-ness form as posed.  Modelling choices: paths are vertex lists required to be
      duplicate-free, so repetitions are sought on simple paths only, which is the standard
      definition of the Thue chromatic number pi; "square-free" is expressed directly as the
      inequality of the two half-sequences rather than through a word-combinatorics layer.
      [x23_genuine_path] duplicates MathComp's [path] plus [uniq]; see the ledger. *)
Definition planar_bounded_nonrepetitive_chromatic_statement : Prop :=
  exists k : nat,
    0 < k /\
    forall G : sgraph,
      wagner_planar G ->
      exists col : G -> 'I_k, x23_nonrepetitive_colouring col.

(** Corpus row: studies:std_planar_linear_arboricity_conjecture
    Site: none
    Review: none
    English statement: (planar linear arboricity conjecture, studies slice)
      For every planar graph G of maximum degree D >= 5, the linear arboricity of G equals
      ceil(D/2).  In the Rocq body: for every finite simple graph G with no K5 and no K3,3
      minor whose maximum degree is at least 5, ceil(D/2) is both achievable as the number of
      colours of an edge colouring all of whose colour classes are linear forests, and
      minimal among such numbers.
    Definitions: [x23_edge_colour_rel col i] / [x23_colour_graph col i] - the spanning
      subgraph of G whose edges are those receiving colour i (this file);
      [x23_linear_forest_colour col i] - that subgraph is a forest of maximum degree at most
      2, i.e. a disjoint union of paths (this file); [x23_linear_arboricity_at_most G q] -
      there is a q-colouring of the vertex-pair sets all of whose colour classes are linear
      forests (this file); [x23_linear_arboricity G q] - q is such a number and is minimal
      (this file); [ceil_div a b] - ceiling division (base/theories/base.v); [Delta],
      [wagner_planar] - base/theories/base.v.
    Notes: The colouring is a total map on 2-element vertex sets ({set G} -> 'I_q); only its
      values on genuine edges matter, because a non-edge contributes nothing to
      [x23_edge_colour_rel].  "Linear forest" is rendered as acyclic plus maximum degree at
      most 2, which is exactly a disjoint union of paths.  The statement asserts EQUALITY
      (achievability and minimality), matching the source's la(G) = ceil(Delta/2); the
      general linear arboricity conjecture also has a Delta <= 4 regime, excluded here by the
      Delta >= 5 hypothesis exactly as in the source row. *)
Definition planar_linear_arboricity_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    5 <= Delta G ->
    x23_linear_arboricity G (ceil_div (Delta G) 2).
