(** * Digraph.conjectures.X221 -- dichromatic / heroes / (un)avoidability / tournament-structure rows (wave X221, 2026-09-23) *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order strong classic_core dichromatic omegabar.
From Digraph Require Import heroes heroes_dichotomy unvd twinwidth twinwidth_ordered.
From GTBase Require Import asymptotics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x221 vocabulary ***********************************************

    Everything the wave can borrow is borrowed: [ind_subdigraph]/[ind_free],
    the domination join [djoin] and the C3-substitution [c3sub], [K1] and the
    transitive tournaments [TT k] come from conjectures/heroes.v; [oriented_dg]
    (asymmetric arc relation, hence loopless) and [no_induced_arrowK2_K1] (no
    induced copy of an arc together with a vertex isolated from both its ends,
    i.e. K_1 + P⃗_2) come from conjectures/heroes_dichotomy.v; [dicolorableb]
    / [acyclicb] / [dichromatic_bounded] from conjectures/dichromatic.v;
    [contains_subdigraph] and [unvd] from conjectures/unvd.v; [tww_le],
    [bclique] from conjectures/twinwidth.v and the CONCRETE ordered twin-width
    [concrete_otww_le] from conjectures/twinwidth_ordered.v; [omegabar] from
    invariants/omegabar.v; [outdeg]/[outsel] from core/oriented.v and [indeg]
    from conjectures/classic_core.v; [big_Theta_nat], [sqrt_ceil] from
    GTBase.asymptotics.

    What is genuinely new here and defined below: the digraph Delta(1,2,2),
    complete multipartite orientations, triangle-freeness of the underlying
    graph, the ACYCLIC NUMBER and the DICHROMATIC NUMBER as nat-valued
    invariants, the extremal functions a-vec(n) / t-vec(n) as relations, the
    twin-width VALUE as a relation, linear unavoidability and k-extensions,
    Eulerian digraphs and Eulerian-avoidability, and the four orientations of
    the 4-cycle. *)

(** *** Delta(1,2,2)

    Delta(k1,k2,k3) is the tournament obtained from the directed triangle by
    substituting the transitive tournaments TT k1, TT k2, TT k3 into its three
    vertices -- exactly [c3sub] of conjectures/heroes.v. *)
Definition x221_Delta122 : diGraphType := c3sub (TT 1) (TT 2) (TT 2).

(** *** Oriented complete multipartite digraphs

    Two vertices are NON-ADJACENT when no arc joins them. A digraph is an
    oriented complete multipartite graph exactly when it is oriented (no digon,
    hence no loop) and non-adjacency is transitive: the non-adjacency classes
    are then the parts, and two vertices are adjacent iff they lie in different
    parts. *)
Definition x221_nonadj (D : diGraphType) (u v : D) : bool :=
  ~~ (u --> v) && ~~ (v --> u).

Definition x221_oriented_complete_multipartite (D : diGraphType) : Prop :=
  oriented_dg D /\
  forall u v w : D, x221_nonadj u v -> x221_nonadj v w -> x221_nonadj u w.

(** *** Oriented graphs whose underlying graph is triangle-free *)

Definition x221_uadj (D : diGraphType) (u v : D) : bool :=
  (u --> v) || (v --> u).

Definition x221_oriented_triangle_free (D : diGraphType) : Prop :=
  oriented_dg D /\
  ~ (exists u v w : D,
       [/\ x221_uadj u v, x221_uadj v w & x221_uadj u w]).

(** *** The acyclic number and the dichromatic number as nat-valued invariants

    [x221_alphavec D] is the maximum order of an induced subdigraph of [D] that
    is acyclic (a genuine maximum: the vertex subsets form a finite type).
    [x221_dichro D] is the least [k <= #|D|] with [dicolorableb D k], taken with
    neutral element [#|D|] (colouring each vertex with its own colour is always
    available for a loopless digraph, so the neutral value never inflates the
    invariant below). *)
Definition x221_alphavec (D : diGraphType) : nat :=
  \max_(S : {set D} | acyclicb (induced_digraph S)) #|S|.

Definition x221_dichro (D : diGraphType) : nat :=
  \big[minn/#|D|]_(k < #|D|.+1 | dicolorableb D k) (k : nat).

(** *** The two extremal functions of arXiv:2403.02298

    [x221_abar n a]: a-vec(n) = a, the MINIMUM of the acyclic number over all
    oriented triangle-free digraphs of order n. [x221_tbar n t]: t-vec(n) = t,
    the MAXIMUM of the dichromatic number over the same class. Both are stated
    as RELATIONS (attained bound + extremal witness), as [unvd] is in
    conjectures/unvd.v, because the minimum ranges over a class of types. *)
Definition x221_abar (n a : nat) : Prop :=
  (forall D : diGraphType,
     x221_oriented_triangle_free D -> #|D| = n -> (a <= x221_alphavec D)%N)
  /\ (exists D : diGraphType,
        [/\ x221_oriented_triangle_free D, #|D| = n & x221_alphavec D = a]).

Definition x221_tbar (n t : nat) : Prop :=
  (forall D : diGraphType,
     x221_oriented_triangle_free D -> #|D| = n -> (x221_dichro D <= t)%N)
  /\ (exists D : diGraphType,
        [/\ x221_oriented_triangle_free D, #|D| = n & x221_dichro D = t]).

(** *** The twin-width of a tournament as a value

    [tww_le T k] (conjectures/twinwidth.v) says "some contraction sequence of T
    has width at most k"; [x221_tww_eq T t] pins the VALUE tww(T) = t as the
    least such bound, in the relational style of [unvd]. *)
Definition x221_tww_eq (T : tournament) (t : nat) : Prop :=
  tww_le T t /\ forall m : nat, (m < t)%N -> ~ tww_le T m.

(** *** Linear unavoidability and k-extensions (arXiv:2410.23566)

    [unvd D N] (conjectures/unvd.v) says N is the unavoidability number of D.
    A family is LINEARLY UNAVOIDABLE when one constant C bounds unvd(D) by
    C*|V(D)| throughout the family. An acyclic digraph D is a K-EXTENSION of A
    when deleting some k vertices of D leaves a copy of A. *)
Definition x221_linearly_unavoidable (F : diGraphType -> Prop) : Prop :=
  exists C : nat,
    forall (D : diGraphType) (N : nat), F D -> unvd D N -> (N <= C * #|D|)%N.

Definition x221_kextension (k : nat) (F : diGraphType -> Prop)
    (D : diGraphType) : Prop :=
  acyclicb D /\
  exists S : {set D},
    #|S| = k /\ exists A : diGraphType, F A /\ dgiso (induced_digraph (~: S)) A.

(** *** Eulerian digraphs and Eulerian-avoidability (arXiv:2510.11311)

    A digraph is EULERIAN when every vertex has equal out- and in-degree.
    A digraph F is EULERIAN-AVOIDABLE when there is d_F : nat -> nat such that
    for every k, every Eulerian digraph of minimum out-degree at least d_F(k)
    has an F-free subdigraph of minimum out-degree at least k. A spanning
    subdigraph is given by an out-neighbourhood selection f through
    [outsel f] (core/oriented.v), whose arcs are the arcs of D lying in f. *)
Definition x221_eulerian (D : diGraphType) : Prop :=
  forall v : D, outdeg v = indeg v.

Definition x221_eulerian_avoidable (F : diGraphType) : Prop :=
  exists d : nat -> nat,
    forall (k : nat) (D : diGraphType),
      x221_eulerian D -> (forall v : D, (d k <= outdeg v)%N) ->
      exists f : D -> {set D},
        (forall v : outsel f, (k <= outdeg v)%N)
        /\ ~ contains_subdigraph F (outsel f).

(** *** The orientations of the 4-cycle

    [x221_c4or b] is the orientation of C_4 in which the edge {i, i+1} of the
    cycle 0-1-2-3-0 on 'Z_4 is directed i -> i+1 when [b i] and i+1 -> i
    otherwise; the sixteen boolean vectors [b] enumerate all orientations (each
    orientation arising from exactly one [b]). *)
Definition x221_c4or (b : 'Z_4 -> bool) : Type := 'Z_4.

Section C4Orientations.
Local Open Scope ring_scope.
Import GRing.Theory.
Variable b : 'Z_4 -> bool.

HB.instance Definition _ := Finite.on (x221_c4or b).
HB.instance Definition _ :=
  HasArc.Build (x221_c4or b)
    (fun u v : 'Z_4 => ((v == u + 1) && b u) || ((u == v + 1) && ~~ b v)).

End C4Orientations.

(** ** X221 statements *****************************************************)

(** Corpus row: arxiv:2306.04710#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2306.04710__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2306.04710__02.json
    English statement: (Carbonero, Koerts, Moore, Spirkl 2023, arXiv:2306.04710, open problem:
      the hero status of Delta(1,2,2))
      There is a single bound B such that every oriented digraph which has no induced copy of
      an arc together with a vertex non-adjacent to both its ends, and no induced copy of
      Delta(1,2,2), has dichromatic number at most B; that is, the forbidden pair
      {Delta(1,2,2), K_1 + P_2-directed} is chi-vector-finite.
    Definitions: [dichromatic_bounded C] - one bound B dicolours every member of the class C
      (conjectures/dichromatic.v); [dicolorableb D k] - V(D) splits into k acyclic-inducing
      classes (conjectures/dichromatic.v); [oriented_dg D] - the arc relation is asymmetric,
      hence also irreflexive (conjectures/heroes_dichotomy.v); [no_induced_arrowK2_K1 D] -
      no three distinct vertices a, b, c with a -> b the only arc among them, i.e. no induced
      K_1 + P_2-directed (conjectures/heroes_dichotomy.v); [ind_free H D] - D has no induced
      subdigraph isomorphic to H (conjectures/heroes.v); [x221_Delta122] - the C3-substitution
      of TT 1, TT 2, TT 2, i.e. Delta(1,2,2) (this file, over [c3sub] of
      conjectures/heroes.v).
    Notes: The [oriented_dg] guard is LOAD-BEARING and encodes the "digraph" of this corner of
      the literature as an oriented graph. Without it the statement is FALSE for a trivial
      reason unrelated to the question: a digraph all of whose adjacencies are digons has no
      induced single arc at all, hence lies in the class, yet the bidirected complete graphs
      have unbounded dichromatic number; a single vertex carrying a loop is likewise in the
      unguarded class and is not dicolourable for any number of colours (see
      [x221_loop_not_dicolorable] in grounding_X221.v). Within oriented digraphs
      "no induced K_1 + P_2-directed" is equivalent to "complete multipartite underlying
      graph", which is why the corpus edge e105 to arxiv:2202.13306#00 closes
      (implications_X221.v). Second-reader readback 2026-09-23: the guard is not a modelling
      liberty but the source's own convention -- arXiv:2306.04710, first paragraph of the
      introduction, reads "Throughout this paper, (di)graphs are finite and simple. In
      particular, for digraphs, between every two vertices u and v, at most one of uv and vu
      is present" (and the paper's "tournaments are exactly the digraphs which forbid 2K_1"
      only holds under that reading). The equivalence just mentioned goes BOTH ways, so this
      row and arxiv:2202.13306#00 encode logically equivalent Props although the corpus lists
      this one open and the other disproved; that is a corpus-status question (the open status
      predates Walczak's remark), not an encoding defect. *)
Definition delta122_hero_k1_plus_dipath2_free_statement : Prop :=
  dichromatic_bounded
    (fun D : diGraphType =>
       [/\ oriented_dg D, no_induced_arrowK2_K1 D & ind_free x221_Delta122 D]).

(** Corpus row: arxiv:2202.13306#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.13306__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.13306__00.json
    English statement: (Aboulker, Aubian, Charbit 2022, Heroes in oriented complete multipartite
      graphs, arXiv:2202.13306, Question 1.4)
      There is a single bound B such that every oriented complete multipartite digraph with no
      induced copy of Delta(1,2,2) has dichromatic number at most B; that is, Delta(1,2,2) is a
      hero in oriented complete multipartite graphs.
    Definitions: [dichromatic_bounded C] (conjectures/dichromatic.v);
      [x221_oriented_complete_multipartite D] - D is oriented and non-adjacency is transitive,
      so the non-adjacency classes are the parts and two vertices are adjacent exactly when
      they lie in different parts (this file); [x221_nonadj u v] - no arc joins u and v (this
      file); [oriented_dg] (conjectures/heroes_dichotomy.v); [ind_free H D]
      (conjectures/heroes.v); [x221_Delta122] (this file).
    Notes: The corpus row is DISPROVED: Remark 1.5 of the published version records Walczak's
      unbounded-chromatic-number result for non-interlaced ordered graphs, which with
      Theorem 4.2 of the paper shows Delta(1,2,2) is NOT a hero there, so this Prop is expected
      to be FALSE; no refutation is committed here, only the question as asked. Complete
      multipartiteness is encoded through transitivity of non-adjacency rather than an explicit
      part function: for an oriented digraph the two formulations agree, and non-adjacency is
      automatically reflexive and symmetric, so transitivity makes it an equivalence whose
      classes are the parts. *)
Definition delta122_hero_oriented_complete_multipartite_statement : Prop :=
  dichromatic_bounded
    (fun D : diGraphType =>
       x221_oriented_complete_multipartite D /\ ind_free x221_Delta122 D).

(** Corpus row: arxiv:2403.02298#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2403.02298__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2403.02298__00.json
    English statement: (Aboulker, Havet, Pirot, Schabanel 2024, arXiv:2403.02298, Conjecture 3)
      Write a-vec(n) for the least possible order of a largest acyclic induced subdigraph of an
      oriented triangle-free digraph on n vertices. Then a-vec(n) is of order square root of
      n times the logarithm of n: there are positive constants C and C' and a threshold beyond
      which a-vec(n) is at most C times, and at least one over C' times, the ceiling of the
      square root of n times the floor of the base-2 logarithm of n.
    Definitions: [x221_alphavec D] - the acyclic number, the largest size of a vertex set
      inducing an acyclic subdigraph (this file); [x221_oriented_triangle_free D] - D is
      oriented and no three vertices are pairwise adjacent in the underlying graph (this file);
      [x221_abar n a] - a is the minimum of the acyclic number over the oriented triangle-free
      digraphs of order n, stated as "a bounds them all from below and is attained" (this
      file); [acyclicb] (conjectures/dichromatic.v); [oriented_dg]
      (conjectures/heroes_dichotomy.v); [big_Theta_nat f g] - f is at most C*g and g is at most
      C'*f eventually, with positive nat constants (GTBase.asymptotics); [sqrt_ceil]
      (GTBase.asymptotics); [trunc_log 2] - floor of the base-2 logarithm (MathComp).
    Notes: Three modelling choices. (1) a-vec is a MINIMUM over a class of types, so it is
      carried as the relation [x221_abar] and the statement is quantified over any total
      function a realizing it; [x221_abar_functional] (grounding_X221.v) shows the relation
      pins a unique value, so at most one such a exists. (2) Theta is GTBase's nat-valued
      [big_Theta_nat], with explicit positive nat constants and a threshold, which is exactly
      the two-sided constant-factor reading of Theta. (3) The real square root and natural
      logarithm are replaced by [sqrt_ceil] and [trunc_log 2]; both differ from their real
      counterparts by a bounded factor on the relevant range, so the Theta class is unchanged.
      The paper's known bounds leave only the upper half open. *)
Definition oriented_triangle_free_acyclic_number_theta_statement : Prop :=
  forall a : nat -> nat,
    (forall n : nat, x221_abar n (a n)) ->
    big_Theta_nat a (fun n => sqrt_ceil (n * trunc_log 2 n)).

(** Corpus row: arxiv:2403.02298#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2403.02298__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2403.02298__01.json
    English statement: (Aboulker, Havet, Pirot, Schabanel 2024, arXiv:2403.02298, Conjecture 4)
      Write t-vec(n) for the largest dichromatic number of an oriented triangle-free digraph on
      n vertices. Then t-vec(n) is of order square root of n divided by the logarithm of n:
      there are positive constants C and C' and a threshold beyond which t-vec(n) is at most C
      times, and at least one over C' times, the ceiling of the square root of n divided by the
      floor of the base-2 logarithm of n.
    Definitions: [x221_dichro D] - the dichromatic number, the least k with a k-dicolouring
      (this file, over [dicolorableb] of conjectures/dichromatic.v);
      [x221_oriented_triangle_free D] (this file); [x221_tbar n t] - t is the maximum of the
      dichromatic number over the oriented triangle-free digraphs of order n, stated as "t
      bounds them all from above and is attained" (this file); [big_Theta_nat], [sqrt_ceil]
      (GTBase.asymptotics); [trunc_log 2] - floor of the base-2 logarithm (MathComp).
    Notes: Same three modelling choices as arxiv:2403.02298#00 (relational extremal function,
      nat-valued Theta, floor-log and ceiling-square-root discretisation). The nat division
      [n %/ trunc_log 2 n] truncates and is 0 for n < 2, which the eventual quantifier of
      [big_Theta_nat] makes harmless. Conjecture 4 follows from Conjecture 3 in the source
      (corpus edge e158, recorded as a candidate in implications_X221.v). *)
Definition oriented_triangle_free_dichromatic_theta_statement : Prop :=
  forall t : nat -> nat,
    (forall n : nat, x221_tbar n (t n)) ->
    big_Theta_nat t (fun n => sqrt_ceil (n %/ trunc_log 2 n)).

(** Corpus row: arxiv:2310.04265#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2310.04265__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2310.04265__03.json
    English statement: (Aboulker, Aubian, Charbit, Lopes 2023, Clique number of tournaments,
      arXiv:2310.04265, Conjecture 3.13 of v1 / Conjecture 3.14 of v2)
      There is one function f such that every nonempty tournament T has a vertex ordering p for
      which the clique number of the back-edge graph of T under p is at most f applied to the
      tournament clique number of T, and the ordered twin-width of T under p is at most f
      applied to the twin-width of T.
    Definitions: [bclique p] - the clique number of the back-edge graph of the ordering p
      (conjectures/twinwidth.v, over invariants/omegabar.v and core/order.v); [omegabar T] -
      the tournament clique number (invariants/omegabar.v); [concrete_otww_le p k] - the
      CONCRETE ordered twin-width bound: some contraction sequence all of whose partitions have
      p-interval classes has width at most k (conjectures/twinwidth_ordered.v); [tww_le T k]
      (conjectures/twinwidth.v); [x221_tww_eq T t] - t is the twin-width of T, the least k with
      [tww_le T k] (this file).
    Notes: This row REPLACES the earlier encoding [conj_3_13_statement] of
      conjectures/twinwidth.v, which bounded the ordered twin-width by f applied to the
      tournament clique number instead of f applied to the TWIN-WIDTH; that definition is left
      untouched and keeps its own "No corpus row" block. Two modelling choices here. (1) The
      twin-width of T appears as a value, so it is carried by the relation [x221_tww_eq] and
      the bound is quantified over the value it pins ([x221_tww_eq_functional] in
      grounding_X221.v shows the value is unique); this is the relational convention of
      [unvd]. (2) Ordered twin-width is the CONCRETE [concrete_otww_le] of
      conjectures/twinwidth_ordered.v, not the abstract section variable of
      conjectures/twinwidth.v, so the statement carries no abstract predicate. The single
      function f bounds both quantities, as in the source. *)
Definition ordered_twinwidth_clique_and_tww_bound_statement : Prop :=
  exists f : nat -> nat,
    forall T : tournament, (0 < #|T|)%N ->
      forall t : nat, x221_tww_eq T t ->
        exists p : {perm T},
          (bclique p <= f (omegabar T))%N /\ concrete_otww_le p (f t).

(** Corpus row: arxiv:2410.23566#05
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2410.23566__05/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2410.23566__05.json
    English statement: (Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Hoersch, Maffray,
      Zamora 2024, Unavoidability of digraphs, arXiv:2410.23566, Conjecture 11)
      Call a family of digraphs linearly unavoidable when one constant C bounds the
      unavoidability number of every member by C times its number of vertices. Then for every
      linearly unavoidable family F and every k, the family of acyclic digraphs that become a
      member of F after deleting k of their vertices is again linearly unavoidable.
    Definitions: [x221_linearly_unavoidable F] - one constant C with unavoidability number at
      most C times the order, throughout F (this file); [x221_kextension k F D] - D is acyclic
      and deleting some k vertices of D leaves a digraph isomorphic to a member of F (this
      file); [unvd D N] - N is the unavoidability number of D, the least N such that every
      tournament on N vertices contains D via an injective arc-preserving map
      (conjectures/unvd.v); [acyclicb] (conjectures/dichromatic.v); [induced_digraph],
      [dgiso] (core/digraph.v).
    Notes: The unavoidability number appears relationally, as in [conj_9] of
      conjectures/unvd.v, so a member whose unavoidability number is not pinned imposes no
      constraint. The acyclicity guard on the k-extension is the source's (k-extensions are
      defined for acyclic digraphs) and has teeth: a digraph with a directed cycle can also be
      reduced to a member of F by deleting k vertices and is deliberately excluded (see
      [x221_kextension_acyclic_guard_has_teeth] in grounding_X221.v). The deletion is written
      as the induced subdigraph on the complement of a k-element set, matched to a member of F
      up to digraph isomorphism. *)
Definition kextension_linear_unavoidability_statement : Prop :=
  forall (F : diGraphType -> Prop) (k : nat),
    x221_linearly_unavoidable F ->
    x221_linearly_unavoidable (x221_kextension k F).

(** Corpus row: arxiv:2510.11311#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2510.11311__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2510.11311__04.json
    English statement: (Christoph, Janzer, Petrova, Steiner 2025, arXiv:2510.11311,
      Question 6.4)
      Is every orientation of the 4-cycle Eulerian-avoidable? That is, for each of the
      orientations F of the cycle on four vertices, is there a function d such that for every
      k, every finite digraph in which each vertex has as many out-neighbours as in-neighbours
      and at least d(k) out-neighbours contains a spanning subdigraph with no copy of F in
      which every vertex still has at least k out-neighbours?
    Definitions: [x221_c4or b] - the orientation of the 4-cycle on 'Z_4 in which the edge
      {i, i+1} runs forwards exactly when b i holds (this file); [x221_eulerian D] - every
      vertex has equal out- and in-degree (this file); [x221_eulerian_avoidable F] - the
      existence of the threshold function d above (this file); [outsel f] - the spanning
      subdigraph of D keeping the arcs of D that lie in the selection f (core/oriented.v);
      [contains_subdigraph F D] - an injective arc-preserving map from F to D, i.e. F is a
      subdigraph of D, not necessarily induced (conjectures/unvd.v); [outdeg]
      (core/oriented.v); [indeg] (conjectures/classic_core.v).
    Notes: Three modelling choices. (1) The source's definition of Eulerian-avoidable leaves d
      and k unbound; the intended reading, matching the paper's definition of AVOIDABLE, binds
      d before k and is the one used here. (2) "F-free subdigraph" is taken with respect to
      ordinary (not induced) containment, as in the avoidability literature; a spanning
      subdigraph is presented by an out-neighbourhood selection, and [outsel] intersects the
      selection with the arcs of D so every selection really gives a subdigraph. (3) The
      sixteen boolean vectors b enumerate the orientations of C_4 with repetitions (the four
      genuinely different orientations each occur several times), which is harmless for a
      universally quantified question. (4) BLOCKED by the second-reader readback of
      2026-09-23: choice (2) is NOT the source's. arXiv:2510.11311 defines "F is
      Eulerian-avoidable" as "there exists d_F : N -> N such that every Eulerian digraph of
      minimum out-degree at least d_F(k) contains an F-free SUBDIGRAPH of minimum out-degree
      at least k", and a subdigraph there may live on any subset of the vertices, whereas
      [outsel f] keeps every vertex of the host, so "forall v : outsel f, k <= outdeg v"
      constrains ALL of V(D). A spanning witness gives a subdigraph witness but not
      conversely (the vertices left out would each have to be given k out-arcs, which may
      create copies of F; the source's notion is satisfied by a witness inside a single
      component of a disjoint union, the spanning one is not), so this Prop IMPLIES Question
      6.4 without being implied by it -- failure mode 3, "too strong". The row is
      [state: blocked] in meta/v2_statement_waves.json; the fix is to existentially quantify
      a vertex subset (an [induced_digraph S] carrying an out-neighbourhood selection, the
      minimum out-degree taken inside S) instead of [outsel] on all of D. The binding order
      "exists d, forall k" is the paper's own, and non-induced F-freeness is correct. *)
Definition orientation_C4_eulerian_avoidable_statement : Prop :=
  forall b : 'Z_4 -> bool, x221_eulerian_avoidable (x221_c4or b).
