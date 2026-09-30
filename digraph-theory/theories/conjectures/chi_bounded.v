(** * Digraph.conjectures.chi_bounded — χ-bounded / chordal / oriented-triangle-free cluster

    The χ-boundedness corpus for oriented graphs, the chordal-class non-χ-boundedness
    landmark, and the oriented-triangle-free extremal cores:

      - Aboulker–Charbit–Naserasr, "χ-bounded families of oriented graphs"
        (arXiv:1605.07411): Conj 2 (Forb(H) is χ-bounded iff the underlying graph of H is
        a forest), Conj 4 (every oriented star is χ-bounding) and Conj 5 (every non-empty
        subset of the orientations of P₄, other than the two exceptions, is χ-bounding).
        Here "χ-bounded" is the ORDINARY undirected χ/ω of the underlying graph
        (graph-theory's [χ(_)] and [ω(_)]), NOT the dichromatic number.
      - Aboulker–Bousquet–de Verclos, "Chordal directed graphs are not χ-bounded"
        (arXiv:2202.01006): the chordal class C₃ (oriented, no induced transitive triangle
        TT₃, no induced directed cycle of length ≥ 4) is NOT directed-χ-bounded — here the
        relevant invariant is the dichromatic number, so the statement uses
        [dichromatic_bounded] (the negation of it over the chordal class).
      - "Minimum acyclic number and maximum dichromatic number of oriented triangle-free
        graphs of a given order" (arXiv:2403.02298): the acyclic-number a⃗ and dichromatic
        t⃗ cores over oriented graphs whose UNDERLYING graph is triangle-free, and the
        m(3) landmark (some oriented triangle-free graph is not 2-dicolourable) as a
        bounded existential.

    Reuses dichromatic.v ([dicolorableb], [dichromatic_bounded]) and heroes.v
    ([ind_subdigraph], [ind_free], [Forb_ind]); the undirected underlying graph and its
    forest predicate follow the [is_forest [set: underlying _]] idiom of heroes_dichotomy.
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath.
From Digraph Require Import dichromatic heroes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Oriented graphs and the underlying undirected graph *)

(** Digon-free = oriented (asymmetric arc relation; also forbids loops). *)
Definition oriented_dg (D : diGraphType) : Prop :=
  forall u v : D, u --> v -> ~~ (v --> u).

Section Underlying.
Variable D : diGraphType.
(** The underlying (symmetric, irreflexive on an oriented graph) adjacency. *)
Definition urel : rel D := fun u v => (u != v) && ((u --> v) || (v --> u)).
Fact urel_sym : symmetric urel.
Proof. by move=> u v; rewrite /urel orbC eq_sym. Qed.
Fact urel_irrefl : irreflexive urel.
Proof. by move=> u; rewrite /urel eqxx. Qed.
(** The underlying simple graph of [D] (forget arc directions). *)
Definition underlying : sgraph := SGraph urel_sym urel_irrefl.
End Underlying.

(** [H] is an oriented forest: its underlying graph is acyclic. *)
Definition oriented_forest (H : diGraphType) : Prop :=
  is_forest [set: underlying H].

(** No [l] pairwise underlying-adjacent vertices (no induced K_l in the underlying graph;
    for [l = 3] this is exactly "the underlying graph is triangle-free"). *)
Definition no_underlying_Kl (l : nat) (D : diGraphType) : Prop :=
  ~ exists S : {set underlying D}, #|S| = l /\ clique S.

(** The underlying graph of [D] is triangle-free. *)
Definition underlying_triangle_free (D : diGraphType) : Prop := no_underlying_Kl 3 D.

(** ** χ-boundedness in the UNDIRECTED sense (the 1605.07411 invariant)

    A class [C] of oriented graphs is χ-bounded when a single binding function [f] bounds
    the ordinary undirected chromatic number χ(underlying G) by f(ω(underlying G)) for
    every member. (Guarded by [0 < #|G|] so the empty graph is not load-bearing.) *)
Definition chi_bounded_under (C : diGraphType -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : diGraphType,
      C G -> (0 < #|G|)%N ->
      (χ([set: underlying G]) <= f (ω([set: underlying G])))%N.

(** Corpus row: arxiv:1605.07411#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1605.07411__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1605.07411__00.json
    English statement: (Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Maffray, Zamora 2016, chi-bounded families of oriented graphs, arXiv:1605.07411, Conjecture 2)
      For every oriented graph H, the class of oriented graphs having no induced copy of H is
      chi-bounded if and only if the underlying simple graph of H is a forest.
    Definitions: [chi_bounded_under C] - there is one function f such that every nonempty member
      G of the class C satisfies chi(U(G)) <= f(omega(U(G))), where U(G) is the underlying
      simple graph and chi, omega are the ordinary undirected chromatic and clique numbers of
      coq-graph-theory (this file); [oriented_dg D] - the arc relation is asymmetric, hence also
      loopless (this file); [underlying D] - the underlying simple graph, u and v adjacent when
      distinct and joined by an arc either way (this file); [ind_free H G] - G has no induced
      subdigraph isomorphic to H, an injection preserving and reflecting arcs
      (conjectures/heroes.v); [oriented_forest H] - the underlying simple graph of H is acyclic
      (this file).
    Notes: chi-boundedness here is the ORDINARY undirected chi and omega of the underlying
      graph, as in the source paper, not the dichromatic number. The bound is required only of
      nonempty members, so the empty digraph is never load-bearing. *)
Definition conj2_1605_statement : Prop :=
  forall H : diGraphType,
    oriented_dg H ->
    ( chi_bounded_under (fun G => oriented_dg G /\ ind_free H G)
      <-> oriented_forest H ).

(** ** Oriented stars and Conjecture 4 (1605.07411)

    An oriented star = an orientation of [K_{1,t}]: a centre [c] adjacent (in the
    underlying graph) to every other vertex, with the leaves pairwise non-adjacent. *)
Definition oriented_star (S : diGraphType) : Prop :=
  oriented_dg S /\
  exists c : S,
    (forall v : S, v != c -> @urel S c v) /\
    (forall u v : S, u != c -> v != c -> u != v -> ~~ @urel S u v).

(** Corpus row: arxiv:1605.07411#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1605.07411__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1605.07411__01.json
    English statement: (Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Maffray, Zamora 2016, chi-bounded families of oriented graphs, arXiv:1605.07411, Conjecture 4)
      For every oriented star S, that is every orientation of a complete bipartite graph K_{1,t}
      (a centre adjacent in the underlying graph to all other vertices, the leaves pairwise
      non-adjacent), the class of oriented graphs with no induced copy of S is chi-bounded.
    Definitions: [chi_bounded_under C] - there is one function f such that every nonempty member
      G of the class C satisfies chi(U(G)) <= f(omega(U(G))), where U(G) is the underlying
      simple graph and chi, omega are the ordinary undirected chromatic and clique numbers of
      coq-graph-theory (this file); [oriented_dg D] - the arc relation is asymmetric, hence also
      loopless (this file); [underlying D] - the underlying simple graph, u and v adjacent when
      distinct and joined by an arc either way (this file); [oriented_star S] - oriented, with a
      centre adjacent to every other vertex and pairwise non-adjacent leaves (this file);
      [ind_free S G] (conjectures/heroes.v).
    Notes: A one-vertex or two-vertex S is an oriented star under this definition, which matches
      the paper's degenerate cases k = 0 and k = l = 1. *)
Definition conj4_1605_statement : Prop :=
  forall S : diGraphType,
    oriented_star S ->
    chi_bounded_under (fun G => oriented_dg G /\ ind_free S G).

(** ** Orientations of P₄ and Conjecture 5 (1605.07411)

    [P4_underlying P] : [P] is an orientation of the path on four vertices — its
    underlying graph is exactly a P₄: four distinct vertices a–b–c–d adjacent
    consecutively and with no other adjacency. *)
Definition P4_underlying (P : diGraphType) : Prop :=
  oriented_dg P /\
  exists a b c d : P,
    [/\ uniq [:: a; b; c; d],
        forall x : P, x \in [:: a; b; c; d],
        @urel P a b, @urel P b c & @urel P c d] /\
    ~~ @urel P a c /\ ~~ @urel P a d /\ ~~ @urel P b d.

(** The two exceptional members are the all-forward directed path [→P₄] and the
    "alternating" orientation [P⁺(1,1,1)] (the two end-arcs point inward / outward). *)

(** [→P₄] = the transitive-on-the-path directed path a→b→c→d (the orientation that is the
    directed path of length 3). *)
Definition is_dirP4 (P : diGraphType) : Prop :=
  P4_underlying P /\
  exists a b c d : P,
    [/\ uniq [:: a; b; c; d],
        forall x : P, x \in [:: a; b; c; d],
        a --> b, b --> c & c --> d].

(** [P⁺(1,1,1)] = the alternating orientation: the middle arc and the two end-arcs
    alternate direction (a→b, c→b, c→d : the two ends both point toward the middle on the
    left and away on the right — an alternating P₄). *)
Definition is_altP4 (P : diGraphType) : Prop :=
  P4_underlying P /\
  exists a b c d : P,
    [/\ uniq [:: a; b; c; d],
        forall x : P, x \in [:: a; b; c; d],
        a --> b, c --> b & c --> d].

(** No corpus row: Conjecture 5 of arXiv:1605.07411 (every nonempty family of orientations of
    the path on four vertices, other than the two exceptional singletons, is chi-bounding); the
    corpus carries only rows __00 (Conjecture 2) and __01 (Conjecture 4) for that paper, so this
    third conjecture of the same cluster owns no row. *)
Definition conj5_1605_statement : Prop :=
  forall forb : diGraphType -> Prop,
    (forall P : diGraphType, forb P -> P4_underlying P) ->
    (exists P : diGraphType, forb P) ->
    (exists P : diGraphType, forb P /\ ~ is_dirP4 P /\ ~ is_altP4 P) ->
    chi_bounded_under (fun G => oriented_dg G /\ Forb_ind forb G).

(** ** The chordal class C₃ (arXiv:2202.01006) and its non-χ-boundedness

    No induced transitive triangle [TT₃]: no three vertices [a,b,c] inducing a transitively
    oriented triangle (a→b, b→c, a→c, and no reverse arcs). *)
Definition no_induced_TT3 (D : diGraphType) : Prop :=
  ~ exists a b c : D,
    [/\ a --> b, b --> c, a --> c,
        ~~ (b --> a) /\ ~~ (c --> b) & ~~ (c --> a)].

(** [D] has an induced directed cycle of length ≥ 4 (a chordless long dicycle): a directed
    cycle [c] of length ≥ 4 whose only arcs among its vertices are the cycle's own forward
    arcs (so the cycle is induced / chordless). *)
Definition has_induced_long_dicycle (D : diGraphType) : Prop :=
  exists c : seq D,
    (4 <= size c)%N /\ dicycle c /\
    (forall u v : D, u \in c -> v \in c -> u --> v -> next c u = v).

(** The chordal class C₃: oriented, no induced TT₃, no induced directed cycle of length
    ≥ 4. (Equivalently every long directed cycle has a chord.) *)
Definition chordal_C3 (D : diGraphType) : Prop :=
  [/\ oriented_dg D, no_induced_TT3 D & ~ has_induced_long_dicycle D].

(** No corpus row: the theorem of Aboulker, Bousquet, de Joannis de Verclos, Chordal directed
    graphs are not chi-bounded (arXiv:2202.01006): the chordal class C3 (oriented, no induced
    transitive triangle, no induced directed cycle of length at least 4) has unbounded
    dichromatic number; it is stated here as the context of the chi-boundedness cluster and is
    not a conjecture row of the corpus. *)
Definition chordal_not_dichromatic_bounded_statement : Prop :=
  ~ dichromatic_bounded chordal_C3.

(** ** Oriented-triangle-free extremal cores (arXiv:2403.02298)

    The acyclic number a(D) = the maximum order of an acyclic induced subdigraph, here as
    a decidable boolean predicate "[D] has an acyclic induced set of size [m]". *)
Definition has_acyclic_set (D : diGraphType) (m : nat) : bool :=
  [exists S : {set D}, (m <= #|S|)%N && acyclicb (induced_digraph S)].

(** [acyclic_number_ge D m] : the acyclic number of [D] is at least [m]. *)
Definition acyclic_number_ge (D : diGraphType) (m : nat) : Prop := has_acyclic_set D m.

(** No corpus row: combinatorial core extracted from arXiv:2403.02298 (minimum acyclic number of
    oriented triangle-free graphs of a given order): a sequence g attaining, at every order n,
    the minimum acyclic number over oriented triangle-free digraphs of that order. The paper's
    Theta(sqrt(n log n)) envelope is asymptotic and real-valued, so only this core is formalised
    and the corpus has no row for it. *)
Definition avec_core_statement : Prop :=
  exists g : nat -> nat,
    forall n : nat, (0 < n)%N ->
      (* lower bound: every order-n oriented triangle-free D has an acyclic set of size g n *)
      (forall D : diGraphType,
         #|D| = n -> oriented_dg D -> underlying_triangle_free D ->
         acyclic_number_ge D (g n)) /\
      (* attained — pins g to the MINIMUM a⃗(n): some order-n such D has no acyclic set of
         size g n + 1 (without this, g := 1 satisfies the lower bound vacuously). *)
      (exists D : diGraphType,
         [/\ #|D| = n, oriented_dg D, underlying_triangle_free D
           & ~ acyclic_number_ge D (g n).+1]).

(** No corpus row: combinatorial core extracted from arXiv:2403.02298 (maximum dichromatic
    number of oriented triangle-free graphs of a given order): a sequence h that upper-bounds,
    and is attained by, the dichromatic number over oriented triangle-free digraphs of each
    order n. The paper's Theta(sqrt(n/log n)) envelope is asymptotic, so only this core is
    formalised and the corpus has no row for it. *)
Definition tvec_core_statement : Prop :=
  exists h : nat -> nat,
    forall n : nat, (0 < n)%N ->
      (* upper bound: every order-n oriented triangle-free D is h n-dicolourable *)
      (forall D : diGraphType,
         #|D| = n -> oriented_dg D -> underlying_triangle_free D ->
         dicolorableb D (h n)) /\
      (* attained — pins h to the MAXIMUM t⃗(n): some order-n such D is not
         (h n − 1)-dicolourable (without the upper bound, h := 1 makes (h n).-1 = 0 and
         the clause holds vacuously). *)
      (exists D : diGraphType,
         [/\ #|D| = n, oriented_dg D, underlying_triangle_free D
           & ~~ dicolorableb D (h n).-1]).

(** No corpus row: the m(3) landmark of arXiv:2403.02298 (some nonempty oriented digraph with
    triangle-free underlying graph is not 2-dicolourable, so the least order realising
    dichromatic number 3 in that class is finite); a bounded existential recorded as context for
    [avec_core_statement] and [tvec_core_statement], with no corpus row. *)
Definition m3_landmark_statement : Prop :=
  exists D : diGraphType,
    [/\ (0 < #|D|)%N, oriented_dg D, underlying_triangle_free D & ~~ dicolorableb D 2].

(** ** Relative edge: the m(3) landmark refutes (single-handedly) directed χ-boundedness
    of the oriented triangle-free class — a non-2-dicolourable triangle-free graph shows the
    class {oriented, underlying-triangle-free} is not 2-bounded. This is a faithful, proof-
    relative consequence (no conjecture is resolved): if the class were dichromatic-bounded
    by the bound 2 it would 2-dicolour every member, contradicting the m(3) witness. *)
Theorem m3_landmark_refutes_2bound :
  m3_landmark_statement ->
  ~ (forall D : diGraphType,
        (0 < #|D|)%N -> oriented_dg D -> underlying_triangle_free D -> dicolorableb D 2).
Proof.
move=> [D [Dpos orD tfD nc2]] H.
by move: (H D Dpos orD tfD); rewrite (negbTE nc2).
Qed.
