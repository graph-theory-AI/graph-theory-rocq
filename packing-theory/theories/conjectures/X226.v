(** * Packing.conjectures.X226 -- eta-boundedness and hypercube-partition rows (wave X226, 2026-09-23) *)

From GTBase Require Export base.
(* [hypercube d] (the d-dimensional cube Q_d) is already owned by this package: it was
   introduced for milestone U9 (row 12 / matchings in hypercubes) and is reused here
   rather than redefined. *)
From Packing.conjectures Require Export U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X226 vocabulary ***********************************************

    Absent from coq-graph-theory, GTBase and this package's [foundations/]:
    the hitting-set parameter eta, eta-boundedness of a class of graphs, the
    path P_t and the star S_a as concrete carriers, and subcube partitions of
    the hypercube.  Everything else is library vocabulary: [stable] and
    [maxstabsets]/[alpha]/[omega] come from coq-graph-theory ([dom.v],
    [coloring.v]), [induced_free] ("H-free") and [is_forest] from
    GTBase.common / [sgraph.v], the disjoint union from [sgraph.sjoin], and
    [hypercube] from [Packing.conjectures.U9]. *)

(** *** The parameter eta (Hajebi–Li–Spirkl) *)

(** [x226_hitting_set X]: [X] meets every MAXIMUM stable set of [G].
    Equivalently (this is the source's definition) removing [X] from [G] drops
    the stability number: [alpha(G - X) < alpha(G)]. *)
Definition x226_hitting_set (G : sgraph) (X : {set G}) : bool :=
  [forall S : {set G}, (S \in maxstabsets [set: G]) ==> (S :&: X != set0)].

(** [x226_eta_le G b]: "eta(G) <= b", i.e. some hitting set has at most [b]
    vertices.  Stated as a bound rather than through a minimum, so that no
    choice operator is needed; [eta(G)] itself is the least such [b]. *)
Definition x226_eta_le (G : sgraph) (b : nat) : Prop :=
  exists X : {set G}, x226_hitting_set X /\ #|X| <= b.

(** A class [C] of graphs is ETA-BOUNDED: one function bounds eta in terms of
    the clique number throughout [C]. *)
Definition x226_eta_bounded (C : sgraph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall G : sgraph, C G -> 0 < #|G| -> x226_eta_le G (f ω(G)).

(** *** Concrete forests: the path P_t and the star S_a *)

(** The path [P_t] on [t] vertices: ['I_t] with consecutive indices adjacent. *)
Definition x226_path_rel (t : nat) : rel 'I_t :=
  fun i j => (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).

Lemma x226_path_sym (t : nat) : symmetric (@x226_path_rel t).
Proof. by move=> i j; rewrite /x226_path_rel eq_sym orbC. Qed.

Lemma x226_path_irrefl (t : nat) : irreflexive (@x226_path_rel t).
Proof. by move=> i; rewrite /x226_path_rel eqxx. Qed.

Definition x226_path_graph (t : nat) : sgraph :=
  SGraph (@x226_path_sym t) (@x226_path_irrefl t).

(** The star [S_a] = [K_{1,a}]: the centre is index 0 of ['I_a.+1] and the [a]
    remaining vertices are pairwise non-adjacent leaves joined to it. *)
Definition x226_star_rel (a : nat) : rel 'I_a.+1 :=
  fun i j => (i == ord0) (+) (j == ord0).

Lemma x226_star_sym (a : nat) : symmetric (@x226_star_rel a).
Proof. by move=> i j; rewrite /x226_star_rel addbC. Qed.

Lemma x226_star_irrefl (a : nat) : irreflexive (@x226_star_rel a).
Proof. by move=> i; rewrite /x226_star_rel addbb. Qed.

Definition x226_star (a : nat) : sgraph :=
  SGraph (@x226_star_sym a) (@x226_star_irrefl a).

(** *** Subcube partitions of the hypercube Q_d *)

(** A SUBCUBE of [Q_d] is described by a partial assignment [c] of the [d]
    coordinates: its vertices are the [d]-bit strings agreeing with [c]
    wherever [c] is defined.  Its DIMENSION is the number of free
    coordinates. *)
Definition x226_subcube (d : nat) (c : {ffun 'I_d -> option bool}) :
    {set hypercube d} :=
  [set x : hypercube d | [forall i : 'I_d, oapp (fun b => tnth x i == b) true (c i)]].

Definition x226_subcube_dim (d : nat) (c : {ffun 'I_d -> option bool}) : nat :=
  #|[set i : 'I_d | c i == None]|.

Definition x226_is_subcube (d : nat) (S : {set hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool}, S == x226_subcube c].

Definition x226_is_subcube_dim_le (d k : nat) (S : {set hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool},
      (S == x226_subcube c) && (x226_subcube_dim c <= k)].

(** All partitions of the vertex set of [Q_d] into subcubes ... *)
Definition x226_subcube_partitions (d : nat) : {set {set {set hypercube d}}} :=
  [set P : {set {set hypercube d}} |
     partition P [set: hypercube d] && [forall S in P, x226_is_subcube S]].

(** ... and those using only subcubes of dimension at most [k]. *)
Definition x226_subcube_partitions_dim_le (d k : nat) :
    {set {set {set hypercube d}}} :=
  [set P in x226_subcube_partitions d | [forall S in P, @x226_is_subcube_dim_le d k S]].

(** The source's counting functions [f(d)] and [f_{<=2}(d)]. *)
Definition x226_f (d : nat) : nat := #|x226_subcube_partitions d|.
Definition x226_f_dim_le2 (d : nat) : nat := #|x226_subcube_partitions_dim_le d 2|.

(** ** X226 statements ****************************************************)

(** Corpus row: arxiv:2302.04986#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2302.04986__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2302.04986__00.json
    English statement: (Hajebi, Li and Spirkl, "Hitting all maximum stable sets in
      P_5-free graphs", arXiv:2302.04986, Conjecture 1.8)
      For every forest H there is a function f on natural numbers such that every
      graph G with no induced subgraph isomorphic to H and with at least one vertex
      has a set of at most f(omega(G)) vertices meeting every maximum stable set
      of G.
    Definitions: [x226_hitting_set X] — X meets every maximum stable set
      (this file, over the library's [maxstabsets]); [x226_eta_le G b] — such a set
      of size at most b exists, i.e. eta(G) <= b (this file);
      [x226_eta_bounded C] — one function f gives eta(G) <= f(omega(G)) for every
      G in C with a vertex (this file); [induced_free G H] — G has no induced
      subgraph isomorphic to H (GTBase.common); [is_forest] — coq-graph-theory
      sgraph.v; [omega] — clique number (coq-graph-theory coloring.v).
    Notes: eta is encoded as the BOUND [x226_eta_le] rather than as a minimum, so
      no choice operator or well-definedness side condition is needed; "eta(G) <= b"
      and "some hitting set has size at most b" are the same proposition. The guard
      [0 < #|G|] is load-bearing: a graph with no vertex has the empty set as its
      unique maximum stable set, which no set meets, so eta would be infinite there
      (see [grounding_X226.x226_no_eta_bound_empty]); the source states eta for
      graphs, implicitly nonempty. "Forest" is the library's [is_forest [set: H]]
      (at most one irredundant path between any two vertices), not a cardinality
      count. The source's proved cases (stars, subdivided stars, P_t for t <= 5)
      are theorems about eta-boundedness, not part of this statement. *)
Definition eta_bounded_forest_free_classes_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    x226_eta_bounded (fun G : sgraph => induced_free G H).

(** Corpus row: arxiv:2302.04986#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2302.04986__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2302.04986__01.json
    English statement: (Hajebi, Li and Spirkl, "Hitting all maximum stable sets in
      P_5-free graphs", arXiv:2302.04986, Conjecture 1.13)
      For every integer t at least 6 there is a function f on natural numbers such
      that every graph G with no induced path on t vertices and with at least one
      vertex has a set of at most f(omega(G)) vertices meeting every maximum stable
      set of G.
    Definitions: [x226_eta_bounded C] — one function f gives eta(G) <= f(omega(G))
      throughout C (this file); [x226_path_graph t] — the path P_t on 'I_t, indices
      adjacent iff consecutive (this file); [induced_free G H] — G has no induced
      subgraph isomorphic to H (GTBase.common).
    Notes: the bound [6 <= t] is the source's, t <= 5 being its Theorem 1.12; the
      conjecture is a separate statement for each t, so the quantifier over t is
      outermost and f may depend on t. Same eta encoding and same [0 < #|G|] guard
      as Conjecture 1.8 above. *)
Definition eta_bounded_path_free_classes_statement : Prop :=
  forall t : nat,
    6 <= t ->
    x226_eta_bounded (fun G : sgraph => induced_free G (x226_path_graph t)).

(** Corpus row: arxiv:2302.04986#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2302.04986__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2302.04986__04.json
    English statement: (Hajebi, Li and Spirkl, "Hitting all maximum stable sets in
      P_5-free graphs", arXiv:2302.04986, open problem on the disjoint union of two
      stars)
      For all integers a and b at least 1 there is a function f on natural numbers
      such that every graph G with no induced subgraph isomorphic to the disjoint
      union of a star with a leaves and a star with b leaves, and with at least one
      vertex, has a set of at most f(omega(G)) vertices meeting every maximum stable
      set of G.
    Definitions: [x226_eta_bounded C] — one function f gives eta(G) <= f(omega(G))
      throughout C (this file); [x226_star a] — the star K_{1,a}: vertex 0 of
      'I_a.+1 joined to the a other vertices, which are pairwise non-adjacent (this
      file); [sjoin G H] — the disjoint union of two graphs (coq-graph-theory
      sgraph.v); [induced_free G H] — G has no induced subgraph isomorphic to H
      (GTBase.common).
    Notes: this is the instance H = S_a union S_b of Conjecture 1.8; it is recorded
      as a separate open problem because the component-wise reduction available for
      chi-boundedness is not known for eta. The guards [0 < a] and [0 < b] are the
      source's "a, b >= 1"; S_a is the star with a LEAVES, hence a.+1 vertices. Same
      eta encoding and same [0 < #|G|] guard as Conjecture 1.8. *)
Definition eta_bounded_two_stars_free_classes_statement : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    x226_eta_bounded
      (fun G : sgraph => induced_free G (sjoin (x226_star a) (x226_star b))).

(** Corpus row: arxiv:2401.00299#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2401.00299__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2401.00299__04.json
    English statement: (Alon, Balogh and Potapov, "Partitioning the hypercube into
      smaller hypercubes", arXiv:2401.00299, Problem 1.10, i.e. Problem 1.2 (iii))
      Write f(d) for the number of partitions of the vertex set of the d-dimensional
      hypercube into subcubes, and f_2(d) for the number of such partitions that use
      only subcubes of dimension at most 2. Is the ratio f(d) / f_2(d)
      subexponential in n = 2^(d-1), that is: for every positive integer q there is
      a d0 such that for every d at least d0 the q-th power of f(d) is at most
      2^(2^(d-1)) times the q-th power of f_2(d)?
    Definitions: [hypercube d] — the d-dimensional cube Q_d on d-bit strings
      (Packing.conjectures.U9); [x226_subcube c] — the set of vertices agreeing with
      the partial coordinate assignment c (this file); [x226_subcube_dim c] — the
      number of coordinates c leaves free (this file); [x226_is_subcube S],
      [x226_is_subcube_dim_le d k S] — S is a subcube, resp. a subcube of dimension
      at most k (this file); [x226_subcube_partitions d],
      [x226_subcube_partitions_dim_le d k] — the partitions of the vertex set of Q_d
      into such subcubes (this file, over MathComp's [partition]);
      [x226_f d], [x226_f_dim_le2 d] — their cardinalities (this file).
    Notes: "subexponential in n" is unfolded in the standard way: for every
      eps > 0 the ratio is at most 2^(eps * n) for all large d. Only the
      reciprocals eps = 1/q need be tested, and multiplying out clears both the
      rational exponent and the division, giving
      [x226_f d ^ q <= 2 ^ (2 ^ d.-1) * x226_f_dim_le2 d ^ q], which is equivalent
      to [(f d / f_2 d) ^ q <= 2 ^ n] over the rationals. n = 2^(d-1) is the
      source's, written [2 ^ d.-1]. The quantifier order is the one asked for: q
      first, then the threshold d0. This is a yes/no question in the source; the
      statement formalises the "yes" answer. *)
Definition subcube_partition_count_ratio_subexponential_statement : Prop :=
  forall q : nat,
    0 < q ->
    exists d0 : nat,
      forall d : nat, d0 <= d ->
        x226_f d ^ q <= 2 ^ (2 ^ d.-1) * x226_f_dim_le2 d ^ q.
