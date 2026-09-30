(** * Digraph.conjectures.heroes_dichotomy — P6 (cont.): the hero-dichotomy conjectures

    The dichotomy / value statements of the heroes corpus (Aboulker–Charbit–Naserasr,
    arXiv:2009.13319), built on the [Forb_ind] / [heroic] / [hero] machinery of heroes.v
    and the dichromatic keystone. Adds the structural predicates these conjectures need:
    the underlying (undirected) graph and its [oriented_forest] / star-forest notions
    (via graph-theory's [is_forest]), transitive tournaments, and the small forbidden
    patterns (stated in the self-contained "no induced pattern" first-order form, which
    avoids fresh finite-type boilerplate).

    Statements:
      - [conj_6_2]  : χ⃗(Forb_ind(digon, C₃, S₂⁺)) ≤ 2  — the smallest OPEN beachhead.
      - [thm_6_1]   : χ⃗(Forb_ind(digon, C₃, →K₂+K₁)) ≤ 2 — proved landmark (as a target).
      - [conj_4_4]  : {digon, K_l, F} is heroic for every oriented forest F and every l.
      - [conj_4_2]  : the hero dichotomy — {digon, H, F} heroic iff F is a star forest or
                      H is a transitive tournament.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P6). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The underlying (undirected) graph and forest / star-forest predicates *)

Section Underlying.
Variable F : orientedDigraph.
Definition urel : rel F := fun u v => (u --> v) || (v --> u).
Fact urel_sym : symmetric urel. Proof. by move=> u v; rewrite /urel orbC. Qed.
Fact urel_irrefl : irreflexive urel. Proof. by move=> u; rewrite /urel arc_irrefl. Qed.
(** The underlying simple graph of an oriented graph (forget arc directions). *)
Definition underlying : sgraph := SGraph urel_sym urel_irrefl.
End Underlying.

(** [F] is an oriented forest: its underlying graph is acyclic. *)
Definition oriented_forest (F : orientedDigraph) : Prop :=
  is_forest [set: underlying F].

(** [F] is a disjoint union of oriented stars = an oriented forest with no path on four
    vertices (a tree with no P₄ is a star). *)
Definition no_P4 (F : orientedDigraph) : Prop :=
  ~ exists a b c d : F,
      [/\ uniq [:: a; b; c; d], urel a b, urel b c & urel c d].
Definition union_of_oriented_stars (F : orientedDigraph) : Prop :=
  oriented_forest F /\ no_P4 F.

(** A transitive tournament: a tournament whose arc relation is transitive. *)
Definition transitive_tournament (H : diGraphType) : Prop :=
  is_tournament H /\ transitive (@arc H).

(** ** Forbidden small patterns (self-contained "no induced pattern" form) *)

(** Digon-free = oriented (asymmetric; this also forbids loops). *)
Definition oriented_dg (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> ~~ (v --> u).

(** No induced directed triangle C₃. *)
Definition no_induced_C3 (D : diGraphType) : Prop :=
  ~ exists a b c : D, [/\ a --> b, b --> c & c --> a].

(** No induced out-star S₂⁺ (centre x with x→a, x→b and {a,b} otherwise non-adjacent). *)
Definition no_induced_S2plus (D : diGraphType) : Prop :=
  ~ exists x a b : D,
      x != a /\ x != b /\ a != b /\ x --> a /\ x --> b /\
      ~~ (a --> b) /\ ~~ (b --> a) /\ ~~ (a --> x) /\ ~~ (b --> x).

(** No induced →K₂+K₁ (an arc a→b together with a vertex c isolated from {a,b}). *)
Definition no_induced_arrowK2_K1 (D : diGraphType) : Prop :=
  ~ exists a b c : D,
      a != b /\ a != c /\ b != c /\ a --> b /\ ~~ (b --> a) /\
      ~~ (a --> c) /\ ~~ (c --> a) /\ ~~ (b --> c) /\ ~~ (c --> b).

(** No induced orientation of K_l (no l pairwise-adjacent vertices). *)
Definition no_induced_Kl (l : nat) (D : diGraphType) : Prop :=
  ~ exists S : {set D},
      #|S| = l /\
      (forall u v : D, u \in S -> v \in S -> u != v -> (u --> v) || (v --> u)).

(** ** The conjectures *)

(** Corpus row: derived:drv_heroforest_h1
    Site: none
    Review: none
    English statement: (Aboulker, Charbit, Naserasr 2020, Extension of Gyarfas-Sumner conjecture to digraphs, arXiv:2009.13319, Conjecture 6.2; corpus derived row)
      Every finite digraph that is oriented (no digon and no loop), has no directed triangle,
      and has no induced out-star S2-plus (no three distinct vertices x, a, b with arcs from x
      to a and from x to b and no arc at all between a and b, nor back to x) has dichromatic
      number at most 2.
    Definitions: [oriented_dg D] - asymmetric arc relation, hence also loopless (this file);
      [no_induced_C3 D] - no three vertices carrying a directed triangle (this file);
      [no_induced_S2plus D] - no induced out-star on three vertices (this file); [dicolorableb D
      2] - the vertex set splits into two parts each inducing an acyclic subdigraph
      (conjectures/dichromatic.v).
    Notes: The value-2 statement of the source is an equality; the open content is the upper
      bound, the lower bound being witnessed by the directed 4-cycle, which lies in the class
      and has dichromatic number 2. In an oriented graph a directed triangle is automatically
      induced, which is why [no_induced_C3] needs no non-adjacency clauses. *)
Definition conj_6_2 : Prop :=
  forall D : diGraphType,
    oriented_dg D -> no_induced_C3 D -> no_induced_S2plus D -> dicolorableb D 2.

(** Theorem 6.1 (proved landmark, as a target): every oriented, C₃-free, →K₂+K₁-free
    digraph is 2-dicolourable. *)
Definition thm_6_1 : Prop :=
  forall D : diGraphType,
    oriented_dg D -> no_induced_C3 D -> no_induced_arrowK2_K1 D -> dicolorableb D 2.

(** Corpus row: arxiv:2009.13319#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2009.13319__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2009.13319__02.json
    English statement: (Aboulker, Charbit, Naserasr 2020, Extension of Gyarfas-Sumner conjecture to digraphs, arXiv:2009.13319, Conjecture 4.4)
      For every oriented forest F and every l, the class of oriented digraphs that contain no l
      pairwise adjacent vertices and no induced copy of F has bounded dichromatic number: one
      constant dicolours every member. Equivalently the set consisting of the digon, the
      complete graph on l vertices and F is heroic.
    Definitions: [oriented_forest F] - the underlying simple graph of F is acyclic (this file);
      [no_induced_Kl l D] - no l vertices pairwise joined by an arc in some direction (this
      file); [ind_free F D] - no induced copy of F (conjectures/heroes.v); [dichromatic_bounded
      C] - one constant k with every member of C k-dicolourable (conjectures/dichromatic.v);
      [underlying] and [oriented_dg] (this file).
    Notes: Forbidding the digon is the [oriented_dg] hypothesis; forbidding K_l is read as
      forbidding every orientation of K_l as an induced subdigraph, which is the
      no-l-pairwise-adjacent-vertices condition. *)
Definition conj_4_4 : Prop :=
  forall (F : orientedDigraph) (l : nat),
    oriented_forest F ->
    dichromatic_bounded
      (fun D : diGraphType => [/\ oriented_dg D, no_induced_Kl l D & ind_free F D]).

(** Corpus row: arxiv:2009.13319#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2009.13319__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2009.13319__01.json
    English statement: (Aboulker, Charbit, Naserasr 2020, Extension of Gyarfas-Sumner conjecture to digraphs, arXiv:2009.13319, Conjecture 4.2, the hero dichotomy)
      For every hero H and every oriented forest F, the class of oriented digraphs with no
      induced copy of H and no induced copy of F has bounded dichromatic number IF AND ONLY IF F
      is a disjoint union of oriented stars or H is a transitive tournament.
    Definitions: [hero H] - H is a hero, the class of digraphs with no induced copy of H having
      bounded dichromatic number (conjectures/heroes.v); [oriented_forest F] and
      [union_of_oriented_stars F] - oriented forest, resp. oriented forest with no path on four
      vertices (this file); [transitive_tournament H] - tournament with transitive arc relation
      (this file); [ind_free] (conjectures/heroes.v); [dichromatic_bounded]
      (conjectures/dichromatic.v); [no_P4] and [underlying] (this file).
    Notes: Disjoint union of oriented stars is encoded as oriented forest without an underlying
      path on four vertices, which is equivalent for forests. The only-if direction is proved in
      the source; the if direction is the open content. *)
Definition conj_4_2 : Prop :=
  forall (H F : orientedDigraph),
    hero H -> oriented_forest F ->
    ( dichromatic_bounded
        (fun D : diGraphType => [/\ oriented_dg D, ind_free H D & ind_free F D])
      <-> (union_of_oriented_stars F \/ transitive_tournament H) ).
