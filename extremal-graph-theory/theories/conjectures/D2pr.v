(** * Extremal.conjectures.D2pr — milestone D2pr (namespace Extremal, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of seven OPEN problems in PROBABILISTIC / asymptotic graph theory.
    Each row is a single [Definition <formal_name> : Prop]; the carrier type is
    chosen PER ROW from its [rocq_idiom] (NOT a blanket [sgraph]).

    DESIGN — FINITE PROBABILITY IS EXACT.  Every probability appearing in these
    rows is over a FINITE sample space (random subgraph = subset of edges; uniform
    random forest = uniform over acyclic edge-sets; random lift = uniform over
    permutation tuples; random preference profile = uniform over permutation
    tuples).  Such probabilities and expectations are EXACT RATIONALS — a counting
    quotient — so they are rendered faithfully with no measure-theoretic layer:
    [E[X] = (\sum_outcomes X)/N], [P(A) = #|A|/N].  Asymptotic claims
    (lim / Θ / whp / 'almost all') use the EVENTUAL ε–N form over [nat] with ratios
    CROSS-MULTIPLIED; no informal o/O/Θ token appears.

    SHARED LOCAL VOCABULARY (kept in this single deliverable file; would migrate to
    a [foundations/probabilistic_core.v] module on a 2nd area consumer — tagged
    [@MOVE-to-base] where cross-area):
      - [srel]/[mkG] : build an [sgraph] as the symmetric-irreflexive closure of any
        boolean relation on a finite vertex type (used by Rows 2,3,5 and the cycle
        graph).  [@MOVE-to-base].
      - [adjb] : edge-set adjacency ([{set {set V}}] of 2-subsets) (Rows 1,2,4).
        [@MOVE-to-base].
      - [edge2] : the 2-subset edge set of an [sgraph] (Rows 2,4).  [@MOVE-to-base].
      - [strong_power] : the n-fold STRONG product [G^⊠n] (Row 3; distinct from
        [base.graph_power], the distance power).  [@MOVE-to-base].
      - [cyc_rel]/[cycle_graph] : the cycle [C_n] on ['I_n] (Row 3).  [@MOVE-to-base].

    CARRIERS (per row):
      - Row 1 (almost all non-Ham 3-regular are 1-connected): labelled simple graphs
        on ['I_(2n)] as edge sets [{set {set 'I_(2n)}}]; counts [NH],[NHB]; eventual
        ratio→1.
      - Row 2 (colouring random subgraphs): an [sgraph G]; [Echi G] = exact rational
        E[χ(G_{1/2})] over all edge-subsets; existence-of-constant comparison.
      - Row 3 (Shannon capacity of C_7): the strong power [strong_power C7 n] (an
        [sgraph] on ['I_7]-tuples); the capacity as the root-free INF characterisation
        over an ordered field.
      - Row 4 (negative association in uniform forests): an [sgraph G] with two edges
        [e,f]; cross-multiplied counting inequality over acyclic edge-sets.
      - Row 5 (χ of random lifts of K_5): lift parameters
        [{ffun 'I_5*'I_5 -> {perm 'I_h}}]; whp concentration on a single value.
      - Row 6 (random stable roommates): preference profiles
        [{ffun 'I_n -> {perm 'I_n}}]; Θ(n^{-1/4}) via 4th powers (root-free).
      - Row 7 (asymptotic distribution of β for polyhedra): PARTIAL — labelled
        graphs on ['I_v]; limiting distribution of [β = v/(k+2)] as an eventual
        empirical-convergence statement.

    PARTIAL / FAITHFULNESS NOTES:
      - Rows 1 & 7 count LABELLED graphs (over edge sets on ['I_m]); the sources speak
        of (iso-class / topologically-inequivalent) graphs.  Iso-class enumeration is
        not available; labelled counting is the faithful finite core, and "almost
        all"/"limiting distribution" are stable under this choice.  "1-connected" is
        rendered as connected ([connectedb]).
      - Row 2 uses [trunc_log 2] (mathcomp floor-log₂) for the logarithm.  The QUESTION
        is "does a constant c exist?"; its truth value is invariant under replacing
        ln by any function within a constant factor of it (for χ ≥ 2,
        trunc_log 2 χ and ln χ agree up to constants), so the existence question is
        rendered faithfully.  The expectation [Echi] is EXACT.
      - Row 3: the value is OPEN ("what is …?"); the statement asserts the capacity
        EXISTS (is well-defined) over every ordered field, via the inf
        characterisation [c = inf{ b : ∀n, α(C₇^⊠n) ≤ bⁿ }] (= sup α^{1/n}, root-free).
        GATE (analysis): a COMPLETE real field ([mathcomp-analysis] [realType]) would
        make the inf provably attained; that package is NOT installed in this switch,
        so the carrier is the available [realFieldType].  Over an incomplete field the
        inf need not be attained, so this row encodes the well-definedness target up to
        that completeness gate (documented, not a type-checking defect).
      - Row 5: the unused [{ffun}] entries (diagonal / reversed pairs) multiply the
        numerator and denominator of every fraction equally, so the counting quotient
        is exactly the true uniform-lift probability.  "Concentrated on a single
        value" = ∃k with P(χ=k) → 1 (whp), in eventual ε–N form.
      - Row 7 is PARTIAL: PLANARITY is not installed as a decidable predicate
        (gate G2), so the boolean count [polyhedralb] uses only 3-connectivity (an
        over-approximation of polyhedra; by Steinitz polyhedra = 3-connected PLANAR).
        Missing: the planarity restriction and the identification of the limit F (the
        open content).  The statement asserts a well-defined limiting β-distribution
        F exists (eventual empirical convergence) — the faithful core of the open
        "what is the distribution?". *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring dom.
From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared local vocabulary *)

(** [srel r] = the symmetric, irreflexive closure of a boolean relation [r]; [mkG r]
    is the [sgraph] it carries.  [@MOVE-to-base]. *)
Definition srel (V:finType)(r:rel V) : rel V :=
  fun x y => (x != y) && (r x y || r y x).
Lemma srel_sym (V:finType)(r:rel V) : symmetric (srel r).
Proof. by move=> x y; rewrite /srel eq_sym orbC. Qed.
Lemma srel_irr (V:finType)(r:rel V) : irreflexive (srel r).
Proof. by move=> x; rewrite /srel eqxx. Qed.
Definition mkG (V:finType)(r:rel V) : sgraph :=
  @SGraph V (srel r) (@srel_sym V r) (@srel_irr V r).

(** Edge-set adjacency: [x ~ y] iff the 2-subset [{x,y}] is a listed edge.
    [@MOVE-to-base] (cross-area: Rows 1,2,4). *)
Definition adjb (V:finType)(E:{set {set V}}) : rel V := fun x y => [set x; y] \in E.

(** The 2-subset edge set of an [sgraph].  [@MOVE-to-base] (cross-area: Rows 2,4). *)
Definition edge2 (G:sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, exists y, (x -- y) && (e == [set x; y])]].

(** The cycle [C_n] on ['I_n] now comes from [GTBase.base] (cross-area finite
    invariant), imported via [base]; base's [cycle_graph] is the same relation. *)

(** ================================================================= *)
(** ** Row 1 — Almost all non-Hamiltonian 3-regular graphs are 1-connected (OPEN)

    Source (Conjecture): NH(n) = number of non-Hamiltonian 3-regular graphs of size
    2n, NHB(n) = number of non-Hamiltonian 3-regular 1-connected graphs of size 2n;
    is lim_{n→∞} NHB(n)/NH(n) = 1?

    Labelled graphs on ['I_(2n)] (edge sets).  [valid_edges] = every listed edge is a
    genuine 2-subset; [regularb E 3] = every vertex has [adjb]-degree 3; "1-connected"
    = [connectedb]; [hamiltonianb] = a Hamiltonian cycle (a full-length [uniq]
    [cycle]) exists.  lim = 1 ⇒ for every ε = a/b, eventually NHB/NH ≥ 1−ε; since
    NHB ≤ NH this pins the ratio to 1.  Cross-multiplied (no division, no guard
    needed — when NH n = 0 both sides vanish): [(b−a)·NH n ≤ b·NHB n]. *)

Definition valid_edges (V:finType)(E:{set {set V}}) : bool :=
  [forall e : {set V}, (e \in E) ==> (#|e| == 2)].
Definition regularb (V:finType)(E:{set {set V}})(d:nat) : bool :=
  [forall x : V, #|[set y : V | adjb E x y]| == d].
Definition connectedb (V:finType)(E:{set {set V}}) : bool :=
  [forall x : V, [forall y : V, connect (adjb E) x y]].
Definition hamiltonianb (V:finType)(E:{set {set V}}) : bool :=
  [exists s : #|V|.-tuple V, cycle (adjb E) (val s) && uniq (val s)].

Definition NH (n:nat) : nat :=
  #|[set E : {set {set 'I_(2*n)}} |
       [&& valid_edges E, regularb E 3 & ~~ hamiltonianb E]]|.
Definition NHB (n:nat) : nat :=
  #|[set E : {set {set 'I_(2*n)}} |
       [&& valid_edges E, regularb E 3, ~~ hamiltonianb E & connectedb E]]|.

(** Corpus row: opg:almost_all_non_hamiltonian_3_regular_graphs_are_1_connected
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/almost_all_non_hamiltonian_3_regular_graphs_are_1_connected/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/almost_all_non_hamiltonian_3_regular_graphs_are_1_connected.json
    English statement: (Open Problem Garden, "Almost all non-Hamiltonian 3-regular graphs are 1-connected")
      For every positive rational eps = a/b there is N such that for all n >= N the counts
      NH(n) of non-Hamiltonian 3-regular labelled graphs on 2n vertices and NHB(n) of those
      that are additionally connected satisfy (b-a) * NH(n) <= b * NHB(n), i.e.
      NHB(n)/NH(n) >= 1 - eps; since NHB <= NH this says the ratio tends to 1.
    Definitions: [valid_edges E] - every listed edge is a genuine 2-element vertex set (D2pr.v);
      [adjb E] - the adjacency carried by an edge set (D2pr.v); [regularb E d] - every vertex
      has [adjb]-degree d (D2pr.v); [connectedb E] - every two vertices are [adjb]-connected
      (D2pr.v); [hamiltonianb E] - some duplicate-free tuple of all |V| vertices is a cycle
      (D2pr.v); [NH n], [NHB n] - the two counts above, over edge sets on 'I_(2n) (D2pr.v).
    Notes: graphs are counted LABELLED, as edge sets over 'I_(2n); the source speaks of
      (isomorphism-class) graphs. Iso-class enumeration is not available, and labelled
      counting is the faithful finite core, "almost all" being stable under this choice.
      "1-connected" is rendered as connected. The limit is cross-multiplied, so no guard on
      NH(n) = 0 is needed (both sides then vanish); instances with a >= b are trivially true. *)
Definition almost_all_non_hamiltonian_3_regular_graphs_are_1_co_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (0 < b)%N ->
    exists N : nat, forall n : nat, (N <= n)%N ->
      ((b - a) * NH n <= b * NHB n)%N.

(** ================================================================= *)
(** ** Row 2 — Colouring random subgraphs (OPEN Problem)

    Source (Problem): for [G_p] (each edge of [G] kept independently w.p. [p]), does
    there exist a constant [c] with E(χ(G_{1/2})) > c·χ(G)/log χ(G)?

    Carrier [G : sgraph].  The sample space of [G_{1/2}] is the set of edge-subsets
    [S ⊆ edge2 G], each w.p. [1/2^{|E|}]; [Echi G] is the EXACT rational expectation
    [(\sum_{S ⊆ E} χ(G_S))/2^{|E|}], where [G_S = mkG (adjb S)] keeps exactly the
    edges in [S].  The logarithm is [trunc_log 2] (see header note: the existence-of-
    constant question is invariant under a constant-factor change of log). *)

Definition Echi (G:sgraph) : rat :=
  ((\sum_(S : {set {set G}} | S \subset edge2 G) (χ([set: mkG (adjb S)]))%:Q)
    / (2 ^ #|edge2 G|)%:Q)%R.

(** Corpus row: opg:coloring_random_subgraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/coloring_random_subgraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/coloring_random_subgraphs.json
    English statement: (Open Problem Garden, "Coloring random subgraphs")
      There is a positive rational constant c such that every graph G with chromatic number at
      least 2 satisfies c * chi(G) / floor(log_2 chi(G)) < E(chi(G_{1/2})), the expectation of
      the chromatic number of the random subgraph keeping each edge with probability 1/2.
    Definitions: [edge2 G] - the edges of G as 2-element vertex sets (D2pr.v); [adjb S] - the adjacency
      carried by an edge set (D2pr.v); [mkG r] - the sgraph that is the symmetric irreflexive
      closure of a boolean relation (D2pr.v); [Echi G] - the EXACT rational expectation, the
      sum of chi over all subsets S of [edge2 G] divided by 2^|E(G)| (D2pr.v); [trunc_log 2] -
      MathComp floor of log base 2; [chi] - chromatic number (coq-graph-theory).
    Notes: the sample space is finite, so the expectation is an exact counting quotient in [rat];
      no measure-theoretic layer is used. The logarithm is [trunc_log 2]; the QUESTION is
      whether a constant exists, and its truth value is invariant under replacing the natural
      logarithm by any function within a constant factor of it, so this is faithful. The guard
      2 <= chi(G) keeps the denominator non-zero. *)
Definition coloring_random_subgraphs_statement : Prop :=
  exists c : rat, (0 < c)%R /\
    forall G : sgraph, (2 <= χ([set: G]))%N ->
      (c * (χ([set: G]))%:Q / (trunc_log 2 (χ([set: G])))%:Q < Echi G)%R.

(** ================================================================= *)
(** ** Row 3 — Shannon capacity of the seven-cycle (OPEN Problem)

    Source (Problem): what is the Shannon capacity of [C_7]?

    [strong_power G n] = the n-fold STRONG product [G^⊠n] on ['I_n]-indexed tuples
    of vertices: distinct [x,y] adjacent iff in every coordinate [i] either
    [x i = y i] or [x i -- y i].  The Shannon capacity is
    [c = lim_n α(G^⊠n)^{1/n} = sup_n α(G^⊠n)^{1/n}]; equivalently (root-free, by
    Fekete) the INFIMUM of bases [b] with [α(G^⊠n) ≤ bⁿ] for all [n ≥ 1].  The OPEN
    value is rendered as: over every ordered field, the capacity EXISTS. *)

(** [strong_power G n] = the n-fold STRONG product [G^⊠n].  [@MOVE-to-base]
    (genuinely new cross-area primitive; base has NO strong product).  NOTE: this is
    NOT [base.graph_power], which is the same-vertex DISTANCE power [G^m] (reach in
    ≤ m steps); nor [base.tensor_product]/[base.cartesian_product] (binary products).
    The strong product over [{ffun 'I_n -> G}] is a distinct construction. *)
Definition strong_power (G:sgraph)(n:nat) : sgraph :=
  @mkG {ffun 'I_n -> G} (fun x y => [forall i, (x i == y i) || (x i -- y i)]).

Definition is_shannon_capacity (R:realFieldType)(G:sgraph)(c:R) : Prop :=
  (forall n, (0 < n)%N -> ((alpha (strong_power G n))%:R <= c ^+ n)%R) /\
  (forall b : R, (forall n, (0 < n)%N -> ((alpha (strong_power G n))%:R <= b ^+ n)%R) ->
     (c <= b)%R).

(** Corpus row: opg:shannon_capacity_of_the_seven_cycle
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/shannon_capacity_of_the_seven_cycle/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/shannon_capacity_of_the_seven_cycle.json
    English statement: (Open Problem Garden, "Shannon capacity of the seven-cycle")
      Over every ordered field R there is c >= 1 that is the Shannon capacity of the 7-cycle:
      the independence number of the n-fold strong power of C_7 is at most c^n for every
      n >= 1, and c is the least element of R with that property.
    Definitions: [strong_power G n] - the n-fold strong product of G on {ffun 'I_n -> G}, distinct tuples
      adjacent when in every coordinate the entries are equal or adjacent (D2pr.v);
      [is_shannon_capacity R G c] - c bounds every alpha(G^n) by c^n and is least such
      (D2pr.v); [mkG] (D2pr.v); [alpha] - independence number (coq-graph-theory dom.v);
      [cycle_graph 7] - C_7 (GTBase).
    Notes: the source asks for the VALUE, which is not a Prop; the body asserts instead that the
      capacity EXISTS (is well defined) over every ordered field, via the root-free infimum
      characterisation c = inf{b : alpha(G^n) <= b^n for all n}, equal to sup alpha^(1/n) by
      Fekete. A COMPLETE real field would make that infimum provably attained; mathcomp-analysis
      is not installed in this switch, so the carrier is [realFieldType], over which the
      infimum need not be attained. The statement therefore encodes well-definedness up to that
      completeness gate. This is a proxy for the source question (recorded in the ledger).
      Note [strong_power] is NOT base's [graph_power] (the distance power). *)
Definition shannon_capacity_of_the_seven_cycle_statement : Prop :=
  forall R : realFieldType,
    exists c : R, (1 <= c)%R /\ is_shannon_capacity (cycle_graph 7) c.

(** ================================================================= *)
(** ** Row 4 — Negative association in uniform forests (OPEN Conjecture)

    Source (Conjecture): for a finite graph [G], DISTINCT edges [e≠f], and [F] a
    uniformly random forest (acyclic edge-subset) of [G]: P(e ∈ F | f ∈ F) ≤ P(e ∈ F).
    The [e ≠ f] hypothesis is essential: at [e = f] the inequality degenerates to
    "every forest contains [e]" (generically false), so distinctness is required to
    state the genuine negative-association conjecture rather than a false instance.

    [forestb S] = [S] is an acyclic subset of [edge2 G]: a set of [v]-vertex edges is
    a forest iff [#edges + #components = #vertices] ([cpts S] = number of connected
    components of [(V, adjb S)]).  Uniform over forests ⇒ all probabilities are
    counting quotients; the conditional inequality, cross-multiplied (clearing the
    positive denominators #forests and #{forests ∋ f}), is the division-free
    [#{F ∋ e,f}·#{F} ≤ #{F ∋ e}·#{F ∋ f}]. *)

Definition cpts (V:finType)(S:{set {set V}}) : nat :=
  #|[set [set y : V | connect (adjb S) x y] | x in [set: V]]|.
Definition forestb (G:sgraph)(S:{set {set G}}) : bool :=
  (S \subset edge2 G) && (#|S| + cpts S == #|[set: G]|).

(** Corpus row: opg:negative_association_in_uniform_forests
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/negative_association_in_uniform_forests/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/negative_association_in_uniform_forests.json
    English statement: (Open Problem Garden, "Negative association in uniform forests")
      For every finite graph G and all DISTINCT edges e, f of G, if F is a uniformly random
      forest (acyclic edge subset) of G then P(e in F | f in F) <= P(e in F); cross-multiplied,
      #{F : e,f in F} * #{F} <= #{F : e in F} * #{F : f in F}.
    Definitions: [edge2 G] - the edges of G as 2-element sets (D2pr.v); [cpts S] - the number of connected
      components of the graph carried by the edge set S (D2pr.v); [forestb G S] - S is a subset
      of [edge2 G] with |S| + cpts S = |V(G)|, i.e. S is acyclic (D2pr.v); [adjb] (D2pr.v).
    Notes: uniformity over forests makes both probabilities counting quotients, and clearing the
      positive denominators gives the division-free inequality in the body. The source says
      "let e, f in E(G)" without distinctness; the body adds e != f, because at e = f the
      inequality degenerates to "every forest contains e", which is generically false, so
      distinctness is required to state the genuine negative-association conjecture rather than
      a false instance (recorded in the ledger as a deliberate added guard). *)
Definition negative_association_in_uniform_forests_statement : Prop :=
  forall (G:sgraph)(e f:{set G}),
    e \in edge2 G -> f \in edge2 G -> e != f ->
    (#|[set S : {set {set G}} | [&& forestb S, e \in S & f \in S]]|
        * #|[set S : {set {set G}} | forestb S]|
     <= #|[set S : {set {set G}} | forestb S && (e \in S)]|
        * #|[set S : {set {set G}} | forestb S && (f \in S)]|)%N.

(** ================================================================= *)
(** ** Row 5 — Chromatic number of random lifts of K_5 (OPEN Question)

    Source (Question): is the chromatic number of a random lift of [K_5]
    concentrated on a single value?

    An h-lift of [K_5] picks, for each (ordered, [u<v]) edge, a permutation
    [π_{uv} ∈ S_h]; the lift has vertices [(u,i) ∈ 'I_5 × 'I_h] and edges
    [(u,i)—(v,j)] iff [u≠v] (K_5 complete) and (for [u<v]) [j = π_{uv}(i)].
    Parameters range over [{ffun 'I_5*'I_5 -> {perm 'I_h}}] (uniform); [mkG] takes the
    symmetric closure so only the [u<v] case is specified.  [chiLift] = χ of the lift.
    "Concentrated on a single value" (whp) = for every ε = a/b, eventually in [h]
    there is one value [k] with P(χ = k) ≥ 1−ε, cross-multiplied. *)

Definition liftadj (h:nat)(p:{ffun ('I_5 * 'I_5) -> {perm 'I_h}}) : rel ('I_5 * 'I_h) :=
  fun a b => (val a.1 < val b.1)%N && (b.2 == (p (a.1, b.1)) a.2).
Definition chiLift (h:nat)(p:{ffun ('I_5 * 'I_5) -> {perm 'I_h}}) : nat :=
  χ([set: mkG (liftadj p)]).

(** Corpus row: opg:chromatic_number_of_random_lifts_of_complete_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/chromatic_number_of_random_lifts_of_complete_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/chromatic_number_of_random_lifts_of_complete_graphs.json
    English statement: (Open Problem Garden, "Chromatic number of random lifts of complete graphs")
      For every positive rational eps = a/b there is H such that for every h >= H there is a
      single value k with at least a (1 - eps) fraction of the h-lift parameters of K_5 giving
      a lift of chromatic number exactly k; that is, the chromatic number of a random lift of
      K_5 is concentrated on one value with high probability.
    Definitions: [liftadj h p] - the adjacency of the h-lift of K_5 given by a permutation for each
      ordered pair of K_5 vertices: (u,i) is joined to (v,j) when u < v and j = p(u,v)(i)
      (D2pr.v); [chiLift p] - the chromatic number of the sgraph carried by [liftadj] via [mkG]
      (D2pr.v); [mkG] takes the symmetric closure, so only the u < v case needs specifying
      (D2pr.v); [chi] - chromatic number (coq-graph-theory).
    Notes: the probability is a counting quotient over the finite parameter space
      {ffun 'I_5 * 'I_5 -> {perm 'I_h}}, cross-multiplied to avoid division. The unused ffun
      entries (diagonal and reversed pairs) multiply numerator and denominator equally, so the
      quotient is exactly the true uniform-lift probability. "Concentrated on a single value"
      is rendered as: for every eps there is eventually a k with P(chi = k) >= 1 - eps. *)
Definition chromatic_number_of_random_lifts_of_complete_graphs_statement : Prop :=
  forall a b : nat, (0 < a)%N -> (0 < b)%N ->
    exists H : nat, forall h : nat, (H <= h)%N ->
      exists k : nat,
        ((b - a) * #|[set: {ffun ('I_5 * 'I_5) -> {perm 'I_h}}]|
          <= b * #|[set p : {ffun ('I_5 * 'I_5) -> {perm 'I_h}} | chiLift p == k]|)%N.

(** ================================================================= *)
(** ** Row 6 — Random stable roommates (OPEN Conjecture)

    Source (Conjecture): the probability that a random instance of the stable
    roommates problem on [n ∈ 2ℕ] people admits a solution is Θ(n^{-1/4}).

    A profile assigns each person a strict preference ranking of all people
    ([{ffun 'I_n -> {perm 'I_n}}], [(pr i) j] = the rank j receives from i; smaller =
    more preferred).  A solution is a perfect matching ([m] a fixed-point-free
    involution) with no blocking pair [(i,j)] (both strictly prefer each other to
    their partners).  [Pstar n] = #{solvable profiles}/#{profiles} (EXACT rational).
    Θ(n^{-1/4}) is root-free via 4th powers: [P ≍ n^{-1/4} ⟺ P⁴·n ≍ 1], i.e. there
    are constants [0 < A ≤ B] with eventually [A ≤ P⁴·n ≤ B] (n even). *)

Definition stable_solvableb (n:nat)(pr:{ffun 'I_n -> {perm 'I_n}}) : bool :=
  [exists m : {ffun 'I_n -> 'I_n},
     [forall i, (m (m i) == i) && (m i != i)] &&
     [forall i, [forall j, (i != j) ==>
        ~~ ((val ((pr i) j) < val ((pr i) (m i)))%N &&
            (val ((pr j) i) < val ((pr j) (m j)))%N) ]]].
Definition Pstar (n:nat) : rat :=
  ((#|[set pr : {ffun 'I_n -> {perm 'I_n}} | stable_solvableb pr]|)%:Q
    / (#|[set: {ffun 'I_n -> {perm 'I_n}}]|)%:Q)%R.

(** Corpus row: opg:random_stable_roommates
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/random_stable_roommates/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/random_stable_roommates.json
    English statement: (Open Problem Garden, "Random stable roommates")
      There are rationals 0 < A <= B and a threshold N such that for every even n >= N the
      probability P(n) that a uniformly random stable-roommates preference profile on n people
      admits a solution satisfies A <= P(n)^4 * n <= B; equivalently P(n) is Theta(n^(-1/4)).
    Definitions: [stable_solvableb n pr] - some fixed-point-free involution m of 'I_n has no blocking
      pair, i.e. no distinct i, j each of which ranks the other strictly above its own partner
      (D2pr.v); [Pstar n] - the EXACT rational ratio of solvable profiles to all profiles in
      {ffun 'I_n -> {perm 'I_n}} (D2pr.v).
    Notes: a profile assigns each person a strict ranking of everyone, [(pr i) j] being the rank j
      receives from i (smaller = more preferred). Theta(n^(-1/4)) is made root-free by raising
      to the fourth power: P ~ n^(-1/4) iff P^4 * n is bounded above and below by positive
      constants. The source restricts to n in 2N, which is the [~~ odd n] guard. *)
Definition random_stable_roommates_statement : Prop :=
  exists A B : rat, (0 < A)%R /\ (A <= B)%R /\
    exists N : nat, forall n : nat, ~~ odd n -> (N <= n)%N ->
      ((A <= (Pstar n) ^+ 4 * n%:Q)%R /\ ((Pstar n) ^+ 4 * n%:Q <= B)%R).

(** ================================================================= *)
(** ** Row 7 — Asymptotic distribution of the form parameter of polyhedra
       (OPEN Problem; PARTIAL)

    Source (Problem): over topologically-inequivalent polyhedra with [k] edges,
    [β := v/(k+2)] ([v] = #vertices); what is the distribution of [β] as [k→∞]?

    PARTIAL (see header): planarity is not a decidable predicate in the installed
    toolchain, so the boolean polyhedron test [polyhedralb] uses only 3-connectivity
    ([three_connb]: [3 < |V|] and deleting any [<3] vertices keeps the graph
    connected).  [cP v k] counts labelled 3-connected graphs on ['I_v] with [k]
    edges; [Dk k] totals over [v ≤ k]; [Bk k x] totals those with [β ≤ x] (for fixed
    [k], [v] vertices, [β ≤ x ⟺ v ≤ x·(k+2)]).  The OPEN "what is the distribution?"
    is rendered as: a limiting CDF [F] EXISTS, i.e. the empirical fraction
    [Bk k x / Dk k] converges to [F x] for every threshold [x] (eventual ε–N,
    cross-multiplied with an absolute value). *)

Definition radj (V:finType)(E:{set {set V}})(S:{set V}) : rel V :=
  fun x y => (y \notin S) && adjb E x y.
Definition three_connb (V:finType)(E:{set {set V}}) : bool :=
  [&& (3 < #|V|),
      [forall T : {set V}, (#|T| < 3) ==>
         [forall x : V, [forall y : V,
            (x \notin T) ==> (y \notin T) ==> connect (radj E T) x y]]]
    & valid_edges E].
Definition polyhedralb (v:nat)(E:{set {set 'I_v}}) : bool := three_connb E.
Definition cP (v k:nat) : nat :=
  #|[set E : {set {set 'I_v}} | polyhedralb E && (#|E| == k)]|.
Definition Dk (k:nat) : nat := \sum_(i < k.+1) cP i k.
Definition Bk (k:nat)(x:rat) : nat :=
  \sum_(i < k.+1) (if (i%:Q <= x * (k + 2)%:Q)%R then cP i k else 0).

Definition is_beta_limit (F:rat -> rat) : Prop :=
  forall (x:rat)(a b:nat), (0 < a)%N -> (0 < b)%N ->
    exists K : nat, forall k : nat, (K <= k)%N -> (0 < Dk k)%N ->
      (b%:Q * `|(Bk k x)%:Q - F x * (Dk k)%:Q| <= a%:Q * (Dk k)%:Q)%R.

(** Corpus row: opg:asymptotic_distribution_of_form_of_polyhedra
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/asymptotic_distribution_of_form_of_polyhedra/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/asymptotic_distribution_of_form_of_polyhedra.json
    English statement: (Open Problem Garden, "Asymptotic Distribution of Form of Polyhedra")
      There is a function F from rationals to rationals with values in [0,1] that is the
      limiting cumulative distribution of the form parameter beta = v/(k+2): for every
      threshold x and every positive rational eps = a/b there is K such that for all k >= K
      with at least one graph counted, the empirical fraction Bk(k,x)/Dk(k) is within eps of
      F(x).
    Definitions: [three_connb E] - more than 3 vertices, every vertex set of size less than 3 leaves the
      rest connected, and [valid_edges] (D2pr.v); [polyhedralb v E] - the polyhedron test, here
      just [three_connb] (D2pr.v); [cP v k] - the number of labelled such graphs on 'I_v with k
      edges (D2pr.v); [Dk k] - their total over v <= k (D2pr.v); [Bk k x] - the total over the
      v with beta = v/(k+2) <= x (D2pr.v); [is_beta_limit F] - the eventual convergence above,
      cross-multiplied with an absolute value (D2pr.v); [radj E S] - adjacency avoiding the set
      S, used to express vertex deletion (D2pr.v).
    Notes: this row is recorded as PARTIAL. Planarity is not available as a decidable predicate in
      the installed toolchain, so [polyhedralb] uses only 3-connectivity, an OVER-approximation
      of polyhedra (by Steinitz, polyhedra are exactly the 3-connected PLANAR graphs). Graphs
      are counted LABELLED, whereas the source counts topologically inequivalent polyhedra.
      The source asks WHAT the distribution is; the body asserts only that a limiting
      distribution F exists. All three gaps are recorded in the ledger. *)
Definition asymptotic_distribution_of_form_of_polyhedra_statement : Prop :=
  exists F : rat -> rat,
    (forall x:rat, (0 <= F x)%R /\ (F x <= 1)%R) /\ is_beta_limit F.
