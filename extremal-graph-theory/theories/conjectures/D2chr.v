(** * Extremal.conjectures.D2chr — milestone D2chr (namespace Extremal, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of ten open/partial problems on FRACTIONAL, CIRCULAR and LIST
    colouring and the fractional Hadwiger number.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base):
    [sgraph], [x -- y], [N], [χ]=[chi_mem], [Delta] (Δ), [connected], [triangle_free],
    [complete]=['K_n], [graph_power], [is_choice_number], [wagner_planar] (the
    combinatorial Wagner planarity façade: no K5 / K3,3 minor).  [GraphTheory.minor]
    supplies [minor G H] ("H is a minor of G") for the Hadwiger rows.  [all_algebra]
    supplies [int]/[absz], [rat] (for χ_f, χ_c, had_f, the choosability threshold),
    and [rcfType]/[matrix] (for the R^3 orthogonality graph).  The shared circular
    layer ([pq_colouring], [is_circular_chromatic], parametric in an abstract
    [adj : V -> V -> bool]) lives in [Extremal.foundations.circular_colouring].

    CARRIER TYPES (per row.rocq_idiom):
      - [sgraph] for the fractional/list/circular rows on finite graphs (1,2,3,5,6,7,8);
      - finite [{ffun 'I_n -> 'I_n}] matchings + sign function for the perfect-matching
        weight row (4);
      - the infinite geometric graph on [{ }'rV[R]_3] (R : rcfType), perpendicularity
        adjacency, for the orthogonality row (9).

    PARTIAL / abstraction notes:
      - Row 1 [is_fractional_hadwiger] gives the LP relaxation of the (clique-minor)
        Hadwiger number — a faithful but definitional choice of the fractional value;
        branch sets are NON-EMPTY (wave-E10 guard repair, see the row's Notes).
      - Row 2 (mixing) is PARTIAL: the genuine object M_c(G) is a REAL number and the
        question is whether it is rational; with no real-number / recolouring-dynamics
        layer we model the recolouring graph by single-vertex moves under [connect] and
        state the existence of a RATIONAL attained mixing threshold (the cleanest
        faithful core of "is M_c(G) always rational?").
      - Row 9 quantifies over every real-closed field [R : rcfType] (the reals R are one
        instance); the vertices are nonzero 3-vectors with perpendicularity adjacency,
        the natural representative model of the lines-through-the-origin graph. *)

From GTBase Require Export base.
From GraphTheory Require Import minor.
From Extremal.foundations Require Export circular_colouring.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Row 1 — Fractional Hadwiger conjecture (OPEN).
    "For every graph G: (a) χ_f(G) ≤ had(G); (b) χ(G) ≤ had_f(G); (c) χ_f(G) ≤ had_f(G)."

    AREA primitives:
      - [bfold_colouring]/[is_fractional_chromatic] : χ_f via (a:b)-colourings (each
        vertex an b-subset of an a-palette, adjacent vertices disjoint); χ_f = inf a/b,
        attained (rational for finite G);
      - [is_hadwiger] : had(G) = largest h with a K_h minor (via base [minor]);
      - [frac_clique_minor]/[is_fractional_hadwiger] : had_f(G) = the LP relaxation —
        rational weights on non-empty connected, pairwise-adjacent branch sets, each vertex
        covered with total weight ≤ 1, maximise the total weight (0/1 weights recover
        a clique minor, so the optimum is had_f ≥ had). *)
Definition bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

Definition is_fractional_chromatic (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\ (exists f, @bfold_colouring G a b f) /\ r = a%:Q / b%:Q) /\
  (forall a b : nat, (0 < b)%N -> (exists f, @bfold_colouring G a b f) -> r <= a%:Q / b%:Q).

Definition is_hadwiger (G : sgraph) (h : nat) : Prop :=
  minor G 'K_h /\ (forall h', minor G 'K_h' -> (h' <= h)%N).

Definition frac_clique_minor (G : sgraph) (n : nat)
    (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) : Prop :=
  [/\ (forall i, 0 <= w i),
      (forall i, B i != set0 /\ connected (B i)),
      (forall i j, i != j -> exists x y : G, [/\ x \in B i, y \in B j & x -- y]),
      (forall v : G, (\sum_(i | v \in B i) w i <= 1)%R)
    & r = \sum_i w i].

Definition is_fractional_hadwiger (G : sgraph) (r : rat) : Prop :=
  (exists (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat), frac_clique_minor B w r) /\
  (forall (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r' : rat),
     frac_clique_minor B w r' -> r' <= r).

(** Corpus row: opg:fractional_hadwiger
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/fractional_hadwiger/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/fractional_hadwiger.json
    English statement: (Open Problem Garden, "Fractional Hadwiger")
      For every non-empty finite graph G, if xf is its fractional chromatic number, h its
      Hadwiger number and hf its fractional Hadwiger number (the maximum total weight of a
      non-negative weighting of non-empty connected vertex sets, any two of them joined by an
      edge, such that every vertex is covered by total weight at most 1), then all three
      inequalities hold: xf <= h, chi(G) <= hf, and xf <= hf.
    Definitions: [bfold_colouring G a b f] - an (a:b)-colouring: every vertex gets a b-element subset
      of an a-element palette and adjacent vertices get disjoint subsets (D2chr.v);
      [is_fractional_chromatic G r] - r is the attained minimum of a/b over (a:b)-colourings
      with b > 0 (D2chr.v); [is_hadwiger G h] - h is the largest integer with a K_h minor,
      using coq-graph-theory's [minor] (D2chr.v); [frac_clique_minor B w r] - the LP
      relaxation of a clique minor: non-negative rational weights w on branch sets B i that
      are non-empty, connected and pairwise joined by an edge, with every vertex covered by
      total weight at most 1, and r the total weight (D2chr.v); [is_fractional_hadwiger G r] - r is the
      attained maximum of that LP (D2chr.v); [chi] - chromatic number (coq-graph-theory).
    Notes: the fractional Hadwiger number is defined here as the LP relaxation of the
      clique-minor number (Fox; Pedersen; Harvey-Wood): the maximum total weight of a
      non-negative weighting of non-empty connected vertex sets that pairwise touch, with
      every vertex covered by total weight at most 1; 0/1 weights recover an ordinary clique
      minor, so had_f >= had. Branch sets are not required to be pairwise disjoint (that is
      the point of the relaxation). The encoding asks two distinct branch sets to be joined
      by an EDGE rather than merely to touch (share a vertex or be joined by an edge); for
      non-empty connected sets the two notions differ only for two indices carrying the same
      singleton, which can be merged (their weights add under the same vertex constraint),
      so the optimum is unchanged. All three values are passed as parameters constrained by
      attainment predicates; for every finite graph these optima exist (rational LP optima:
      atlas fractional.frac_chromatic_exists and fractional.frac_hadwiger_exists, via the
      Fourier-Motzkin attainment lemma Extremal.foundations.lp_rational.lp_max_fin), so no
      instance is vacuous.
      GUARD REPAIR (2026-09-24, wave E10): [frac_clique_minor] now requires every branch
      set to be NON-EMPTY (B i != set0). Without it [is_fractional_hadwiger G hf] held for
      NO graph and NO hf, so the row was VACUOUSLY TRUE: a single EMPTY branch set is
      [connected], meets no adjacency constraint (only one index) and covers no vertex, so
      its weight is unbounded and the LP has no maximum (wave-A1 witness
      atlas fractional.is_fractional_hadwiger_unsat, now ported as
      grounding_D2chr.old_is_fractional_hadwiger_unsat on the old body spelled out inline).
      The paper's branch sets are connected SUBGRAPHS, hence non-empty; nonemptiness also
      forces each weight to be at most 1, as in the source. [is_fractional_chromatic] has no
      such defect (it ranges over (a:b)-colourings with b > 0, not over weighted sets) and
      is unchanged. Teeth and non-vacuity: grounding_D2chr.v
      (old_is_fractional_hadwiger_unsat, frac_clique_minor_le_card,
      is_fractional_hadwiger_K1, is_fractional_hadwiger_K2,
      fractional_hadwiger_hyps_K2, fractional_hadwiger_instance_K2,
      fractional_hadwiger_conclusion_has_content). *)
Definition fractional_hadwiger_statement : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    is_fractional_chromatic G xf -> is_hadwiger G h -> is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].

(** ** Row 2 — Is the colouring-mixing threshold M_c(G) always rational? (OPEN; PARTIAL).
    The recolouring graph on the [(p,q)]-colourings (single-vertex moves); [circ_mixing]
    says it is connected (all valid colourings reachable). M_c(G) is the INFIMUM p/q over
    mixing pairs; the statement asserts this infimum is RATIONAL for every G — the
    faithful core of the rationality question (NO attainment is required: [r] is modelled
    as the greatest lower bound, not as an attained minimum). *)

(** [pqb G p q c] is the decidable (boolean) reflection of the shared Prop-level
    [pq_colouring (fun x y => x -- y) p q (fun v => c v : nat)] (foundations): the
    [c v < p] clause is discharged by the ['I_p] carrier, and the [q <= |.| <= p-q]
    edge condition is the same notion, recast over [{ffun G -> 'I_p}] because
    [connect]/[rel] require a boolean adjacency. *)
Definition pqb (G : sgraph) (p q : nat) (cf : {ffun G -> 'I_p}) : bool :=
  [forall x : G, [forall y : G, (x -- y) ==>
     ((q <= absz (Posz (cf x) - Posz (cf y)))%N &&
      (absz (Posz (cf x) - Posz (cf y)) <= p - q)%N)]].

Definition recolour_adj (G : sgraph) (p q : nat) : rel {ffun G -> 'I_p} :=
  fun c c' => [&& @pqb G p q c, @pqb G p q c' & #|[set v | c v != c' v]| == 1%N].

Definition circ_mixing (G : sgraph) (p q : nat) : Prop :=
  forall c c' : {ffun G -> 'I_p},
    @pqb G p q c -> @pqb G p q c' -> connect (@recolour_adj G p q) c c'.

(** A NON-TRIVIAL mixing pair: a genuine circular regime [2*q <= p] (every edge of a
    nonempty graph forces [p >= 2q]) in which an actual valid colouring exists AND the
    recolouring graph is connected.  The colourability + [2*q <= p] guards block the
    spurious empty-palette pair [p = 0] (under which [pqb] holds vacuously) from
    dragging the infimum down to a meaningless [0]. *)
Definition mixing_pair (G : sgraph) (p q : nat) : Prop :=
  [/\ (0 < q)%N, (2 * q <= p)%N, (exists c : {ffun G -> 'I_p}, @pqb G p q c)
    & circ_mixing G p q].

(** [r = M_c(G)] as the INFIMUM (greatest lower bound) of the ratios [p/q] over mixing
    pairs: [r] is a lower bound (clause 1) and the greatest such (clause 2).  Then
    [exists r : rat, is_colouring_mixing_threshold G r] holds exactly when this real
    infimum is rational — faithfully "is M_c(G) always rational?", with no spurious
    attainment. *)
Definition is_colouring_mixing_threshold (G : sgraph) (r : rat) : Prop :=
  (forall p q : nat, mixing_pair G p q -> r <= p%:Q / q%:Q) /\
  (forall s : rat,
     (forall p q : nat, mixing_pair G p q -> s <= p%:Q / q%:Q) -> s <= r).

(** Corpus row: opg:mixing_circular_colourings_0
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/mixing_circular_colourings_0/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/mixing_circular_colourings_0.json
    English statement: (Open Problem Garden, "Mixing Circular Colourings")
      For every finite graph G the circular mixing threshold M_c(G) is rational: there is a
      rational r that is the greatest lower bound of the ratios p/q over all pairs (p,q) for
      which the single-vertex recolouring graph on the (p,q)-colourings of G is connected.
    Definitions: [pqb G p q c] - the boolean reflection of [pq_colouring] over {ffun G -> 'I_p}: on every
      edge the two colours differ by at least q and at most p - q in absolute value
      (D2chr.v); [recolour_adj G p q] - two valid (p,q)-colourings differing at exactly one
      vertex (D2chr.v); [circ_mixing G p q] - all valid (p,q)-colourings are connected under
      [recolour_adj] (D2chr.v); [mixing_pair G p q] - q > 0, 2q <= p, at least one valid
      (p,q)-colouring exists, and [circ_mixing] holds (D2chr.v);
      [is_colouring_mixing_threshold G r] - r is a lower bound of the ratios p/q over mixing
      pairs and the greatest such (D2chr.v); [pq_colouring] - foundations/circular_colouring.v.
    Notes: this row is recorded as PARTIAL. The genuine object M_c(G) is a real number and the
      question is whether it is rational; with no real-number or recolouring-dynamics layer,
      the recolouring graph is modelled by single-vertex moves under [connect] and the
      statement asserts the existence of a RATIONAL greatest lower bound, with NO attainment
      required. The guards q > 0 and 2q <= p together with the requirement that a valid
      colouring exists block the spurious empty-palette pair p = 0, under which [pqb] holds
      vacuously and would drag the infimum down to a meaningless 0. *)
Definition mixing_circular_colourings_0_statement : Prop :=
  forall G : sgraph, exists r : rat, is_colouring_mixing_threshold G r.

(** Corpus row: opg:list_chromatic_number_and_maximum_degree_of_bipartite_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/list_chromatic_number_and_maximum_degree_of_bipartite_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/list_chromatic_number_and_maximum_degree_of_bipartite_graphs.json
    English statement: (Open Problem Garden, "List chromatic number and maximum degree of bipartite graphs")
      There is a constant c such that every bipartite graph G with maximum degree Delta >= 2
      has list chromatic number m satisfying 2^m <= Delta^c, i.e. m <= c * log_2 Delta.
    Definitions: [bipartite G] - a 2-colouring of the vertices with no monochromatic edge, equivalently
      chi(G) <= 2 (GTBase); [Delta G] - maximum degree (GTBase); [is_choice_number G m] - m is
      the list chromatic number ch(G) (GTBase).
    Notes: the logarithm is removed by exponentiating: m <= c * log_2 Delta is equivalent to
      2^m <= Delta^c. The guard 2 <= Delta excludes the degenerate small-degree regime where
      log Delta vanishes and no constant c could work. *)
Definition list_chromatic_number_and_maximum_degree_of_bipartit_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (m : nat),
      bipartite G -> (2 <= Delta G)%N -> is_choice_number G m ->
      (2 ^ m <= (Delta G) ^ c)%N.

(** ** Row 4 — Monochromatic colorings inherited from perfect matchings (OPEN).
    "For which (n,d) is there a bi-colored graph on n vertices and d colors such that all
    d monochromatic colorings have unit weight and every other coloring cancels?"

    AREA primitives [bicolored_unit] / [coloring_weight]: the bicoloring is a sign
    function [sgn] on vertex pairs; a perfect matching is a fixed-point-free involution
    [m]; [match_weight] = ∏_{i < m i} sgn i (m i); [coloring_weight c] = the signed sum,
    over perfect matchings whose every matched pair is monochromatic under [c], of
    [match_weight].  [bicolored_unit n d]: a sign function exists for which every constant
    (monochromatic) colouring has weight 1 and every non-constant colouring has weight 0.
    The "for which (n,d)" question is encoded as the existence of at least one nontrivial
    [(n,d)] with this property (the full characterisation of the admissible set is the
    open content). *)
Definition pmatch (n : nat) (m : {ffun 'I_n -> 'I_n}) : bool :=
  [forall i, (m (m i) == i) && (m i != i)].

Definition match_weight (n : nat) (sgn : 'I_n -> 'I_n -> int) (m : {ffun 'I_n -> 'I_n}) : int :=
  \prod_(i : 'I_n | (i < m i)%N) sgn i (m i).

Definition coloring_weight (n d : nat) (sgn : 'I_n -> 'I_n -> int) (c : 'I_n -> 'I_d) : int :=
  \sum_(m : {ffun 'I_n -> 'I_n} | pmatch m && [forall i, c (m i) == c i]) match_weight sgn m.

Definition bicolored_unit (n d : nat) : Prop :=
  exists sgn : 'I_n -> 'I_n -> int,
    (* bi-coloured: [sgn] is a genuine 2-valued sign, not an arbitrary weight *)
    (forall i j : 'I_n, sgn i j = 1 \/ sgn i j = -1) /\
    (forall (k : 'I_d) (c : 'I_n -> 'I_d),
        (forall i, c i = k) -> @coloring_weight n d sgn c = (1 : int)) /\
    (forall c : 'I_n -> 'I_d,
        ~ (exists k : 'I_d, forall i, c i = k) -> @coloring_weight n d sgn c = (0 : int)).

(** Corpus row: opg:monochromatic_vertex_colorings_inherited_from_perfect_matchings
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/monochromatic_vertex_colorings_inherited_from_perfect_matchings/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/monochromatic_vertex_colorings_inherited_from_perfect_matchings.json
    English statement: (Open Problem Garden, "Monochromatic vertex colorings inherited from Perfect Matchings")
      There exist n > 0 and d >= 2 and a sign function on the pairs of an n-element vertex set
      such that every one of the d constant (monochromatic) vertex colourings has weight 1 and
      every non-constant colouring has weight 0, the weight of a colouring being the signed sum
      over the perfect matchings all of whose matched pairs are monochromatic.
    Definitions: [pmatch n m] - m is a fixed-point-free involution of 'I_n, i.e. a perfect matching
      (D2chr.v); [match_weight sgn m] - the product of sgn i (m i) over the pairs with
      i < m i (D2chr.v); [coloring_weight n d sgn c] - the sum of [match_weight] over the
      perfect matchings whose every matched pair is monochromatic under c (D2chr.v);
      [bicolored_unit n d] - existence of a +/-1-valued sign function with the two weight
      properties above (D2chr.v).
    Notes: the source asks "for which values of n and d" such a bi-coloured graph exists; a
      characterisation of the admissible set is not a Prop, so the Rocq body only asserts the
      EXISTENCE of at least one non-trivial pair (n > 0, d >= 2). That is strictly weaker than
      the source question (recorded in the ledger). Weights live in [int], and the sign
      function is forced to be 2-valued by the clause sgn i j = 1 or sgn i j = -1. *)
Definition monochromatic_vertex_colorings_inherited_from_perfec_statement : Prop :=
  exists n d : nat, (2 <= d)%N /\ (0 < n)%N /\ bicolored_unit n d.

(** ** Row 5 — Choosability of graph powers (Noel, 2013) (OPEN).
    "Does there exist f(k)=o(k²) with ch(G²) ≤ f(χ(G²)) for every graph G?"
    [graph_power G 2] = G²; [is_o_ksq] is the ε–N rendering of o(k²):
    for every c>0, eventually [c·f(k) ≤ k²] (i.e. f(k)/k² → 0). *)
Definition is_o_ksq (f : nat -> nat) : Prop :=
  forall c : nat, (0 < c)%N -> exists N, forall k, (N <= k)%N -> (c * f k <= k * k)%N.

(** Corpus row: opg:choosability_of_graph_powers
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/choosability_of_graph_powers/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/choosability_of_graph_powers.json
    English statement: (Noel 2013, Open Problem Garden "Choosability of Graph Powers")
      There is a function f with f(k) = o(k^2) such that for every graph G, the list chromatic
      number of the square G^2 is at most f applied to the chromatic number of G^2.
    Definitions: [is_o_ksq f] - for every c > 0 there is N with c * f k <= k * k for all k >= N, the
      epsilon-N rendering of f(k)/k^2 -> 0 (D2chr.v); [graph_power G 2] - the square of G
      (GTBase); [is_choice_number H m] - m is the list chromatic number ch(H) (GTBase);
      [chi] - chromatic number (coq-graph-theory).
    Notes: f is a single function chosen before G, as the source requires. The o(k^2) condition is
      cleared of division by cross-multiplying. *)
Definition choosability_of_graph_powers_statement : Prop :=
  exists f : nat -> nat, is_o_ksq f /\
    forall (G : sgraph) (chG m : nat),
      χ([set: graph_power G 2]) = chG ->
      is_choice_number (graph_power G 2) m ->
      (m <= f chG)%N.

(** ** Row 6 — Circular choosability of planar graphs (OPEN; best bound asked).
    Following the source: a [t]-[(p,q)]-list-assignment gives each vertex a list
    [L v ⊆ {0,…,p-1}] with [|L v| ≥ t·q]; [G] is [t]-[(p,q)]-choosable if every such
    [L] admits a [(p,q)]-colouring picking [c v ∈ L v]; [G] is circularly [t]-choosable
    if [t]-[(p,q)]-choosable for all [p,q]; cch(G) = inf{t ≥ 1 : circularly t-choosable}.
    The Problem ("best upper bound over planar graphs") is the LEAST [B] bounding cch on
    every (Wagner-)planar graph. *)
Definition t_pq_choosable (G : sgraph) (t : rat) (p q : nat) : Prop :=
  forall L : G -> {set 'I_p},
    (forall v, t * q%:Q <= (#|L v|)%:Q) ->
    exists c : G -> 'I_p,
      pq_colouring (fun x y : G => x -- y) p q (fun v => (c v : nat)) /\
      (forall v, c v \in L v).

Definition circularly_t_choosable (G : sgraph) (t : rat) : Prop :=
  forall p q : nat, (0 < q)%N -> t_pq_choosable G t p q.

Definition is_circular_choosability (G : sgraph) (b : rat) : Prop :=
  [/\ (1 <= b)%R,
      (forall t : rat, b < t -> circularly_t_choosable G t)
    & (forall t : rat, 1 <= t -> circularly_t_choosable G t -> b <= t)].

(** Corpus row: opg:circular_choosability_of_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/circular_choosability_of_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/circular_choosability_of_planar_graphs.json
    English statement: (Open Problem Garden, "Circular choosability of planar graphs")
      There is a rational B that is the least upper bound of the circular choosability cch(G)
      over all planar graphs G: every planar graph with circular choosability b satisfies
      b <= B, and B <= B' for every other such bound B'.
    Definitions: [t_pq_choosable G t p q] - for every list assignment L giving each vertex a subset of
      {0,...,p-1} of size at least t*q, there is a (p,q)-colouring picking c v in L v
      (D2chr.v); [circularly_t_choosable G t] - t-(p,q)-choosable for all p and all q > 0
      (D2chr.v); [is_circular_choosability G b] - b >= 1, every t > b makes G circularly
      t-choosable, and b is a lower bound of the circularly t-choosable t >= 1, i.e.
      b = inf{t >= 1 : G is circularly t-choosable} (D2chr.v); [pq_colouring] -
      foundations/circular_colouring.v; [wagner_planar] - planarity in Wagner's form, no K_5
      and no K_{3,3} minor (GTBase).
    Notes: the source Problem asks WHAT the best upper bound is; the Rocq body asserts that a least
      upper bound exists and is rational, which is the closest Prop rendering but does not pin
      a value (recorded in the ledger). Planarity is the combinatorial Wagner facade, not a
      topological embedding. *)
Definition circular_choosability_of_planar_graphs_statement : Prop :=
  exists B : rat,
    (forall (G : sgraph) (b : rat),
        wagner_planar G -> is_circular_choosability G b -> b <= B) /\
    (forall B' : rat,
        (forall (G : sgraph) (b : rat),
            wagner_planar G -> is_circular_choosability G b -> b <= B') ->
        B <= B').

(** ** Row 7 — Star chromatic index of complete graphs (OPEN).
    "Is χ'_s(K_n) linear in n, i.e. O(n)?"  A star edge colouring is a proper edge
    colouring (adjacent edges differ) with NO bichromatic path or cycle on 4 edges
    (the colour set on the 4 edges has size ≥ 3).  [is_star_chromatic_index] is the least
    number of colours; the statement is the eventual linear bound [k ≤ c·n].

    BASE-REUSE NOTE: base's edge-colouring layer (line_graph / chromatic_index χ' /
    edge_colourable) exposes only a colour COUNT, not a colour assignment; the star
    constraints (no bichromatic P4/C4) need the explicit colour FUNCTION [f] on edges,
    so base's χ' cannot express them and a local [proper_ec] is required.  The genuinely
    new star primitives below carry a [@MOVE-to-base] tag for future migration. *)
Definition proper_ec (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  (forall x y : G, f x y = f y x) /\
  (forall x y z : G, x -- y -> x -- z -> y != z -> f x y != f x z).

Definition no_bichromatic_P4 (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  forall a b c d e : G,
    uniq [:: a; b; c; d; e] -> a -- b -> b -- c -> c -- d -> d -- e ->
    (2 < #|[set f a b; f b c; f c d; f d e]|)%N.

Definition no_bichromatic_C4 (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  forall a b c d : G,
    uniq [:: a; b; c; d] -> a -- b -> b -- c -> c -- d -> d -- a ->
    (2 < #|[set f a b; f b c; f c d; f d a]|)%N.

(** [@MOVE-to-base] [star_edge_colouring] / [is_star_chromatic_index] extend base's
    edge-colouring layer with the star (no bichromatic P4/C4) constraints; migrate to
    base when a 2nd area needs the star chromatic index. *)
Definition star_edge_colouring (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  [/\ proper_ec f, no_bichromatic_P4 f & no_bichromatic_C4 f].

Definition star_edge_k_colourable (G : sgraph) (k : nat) : Prop :=
  exists f : G -> G -> 'I_k, star_edge_colouring f.

Definition is_star_chromatic_index (G : sgraph) (k : nat) : Prop :=
  star_edge_k_colourable G k /\
  (forall k', star_edge_k_colourable G k' -> (k <= k')%N).

(** Corpus row: opg:star_chromatic_index_of_complete_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/star_chromatic_index_of_complete_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/star_chromatic_index_of_complete_graphs.json
    English statement: (Open Problem Garden, "Star chromatic index of complete graphs")
      There are constants c and N such that for every n >= N the star chromatic index of the
      complete graph K_n is at most c * n, i.e. it is linear in n; a star edge colouring is a
      proper edge colouring in which no 4-edge path and no 4-cycle uses only two colours.
    Definitions: [proper_ec f] - f is symmetric and gives distinct colours to two edges sharing a vertex
      (D2chr.v); [no_bichromatic_P4 f] - every path on five distinct vertices uses more than
      two colours on its four edges (D2chr.v); [no_bichromatic_C4 f] - likewise for every
      4-cycle on four distinct vertices (D2chr.v); [star_edge_colouring f] - the conjunction of
      the three (D2chr.v); [is_star_chromatic_index G k] - k is the least number of colours
      admitting a star edge colouring (D2chr.v); [complete n] - K_n (coq-graph-theory).
    Notes: base's edge-colouring layer (line_graph / chromatic_index / edge_colourable) exposes
      only a colour COUNT, not a colour assignment; the star constraints need the explicit
      colour FUNCTION on edges, so a local [proper_ec] is required. The star primitives carry a
      MOVE-to-base tag for future migration. O(n) is encoded as an eventual bound c * n with a
      threshold N. *)
Definition star_chromatic_index_of_complete_graphs_statement : Prop :=
  exists c N : nat,
    forall (n k : nat),
      (N <= n)%N -> is_star_chromatic_index (complete n) k -> (k <= c * n)%N.

(** Corpus row: opg:circular_chromatic_number_of_triangle_free_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/circular_chromatic_number_of_triangle_free_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/circular_chromatic_number_of_triangle_free_planar_graphs.json
    English statement: (Open Problem Garden, "Circular coloring triangle-free subcubic planar graphs")
      Every triangle-free planar graph of maximum degree at most 3 has circular chromatic
      number at most 20/7.
    Definitions: [is_circular_chromatic adj r] - r is the attained minimum of p/q over the (p,q)-colourings
      of the adjacency adj, a (p,q)-colouring giving every vertex a colour below p with linear
      colour difference between q and p - q on every edge (foundations/circular_colouring.v);
      [triangle_free], [Delta], [wagner_planar] - GTBase.
    Notes: planarity is the combinatorial Wagner facade (no K_5 and no K_{3,3} minor), not a
      topological embedding. The circular chromatic number is passed as a parameter constrained
      by the attainment predicate, so a graph whose value is not attained gives a vacuous
      instance. *)
Definition circular_chromatic_number_of_triangle_free_planar_gr_statement : Prop :=
  forall (G : sgraph) (r : rat),
    triangle_free G -> wagner_planar G -> (Delta G <= 3)%N ->
    is_circular_chromatic (fun x y : G => x -- y) r -> r <= 20%:Q / 7%:Q.

(** ** Row 9 — Circular colouring of the orthogonality graph (OPEN; PARTIAL/geometric).
    O has vertex set the lines through the origin in R^3, two adjacent iff perpendicular;
    Problem: is χ_c(O) = 4?  Modelled, over any real-closed field [R], on nonzero
    3-vectors with perpendicularity ([dot product = 0]) adjacency — the natural
    representative model of the lines graph; the shared [is_circular_chromatic] applies
    unchanged to this INFINITE vertex type. *)
Definition perp (R : rcfType) (u v : 'rV[R]_3) : bool :=
  [&& (u != 0), (v != 0) & ((u *m v^T) 0 0 == 0)].

(** Corpus row: opg:circular_colouring_the_orthogonality_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/circular_colouring_the_orthogonality_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/circular_colouring_the_orthogonality_graph.json
    English statement: (Open Problem Garden, "Circular colouring the orthogonality graph")
      Over every real-closed field R, the graph on the 3-dimensional row vectors over R in
      which two vectors are adjacent when both are non-zero and their dot product vanishes has
      circular chromatic number exactly 4.
    Definitions: [perp R u v] - u and v are non-zero and (u *m v^T) 0 0 = 0, i.e. perpendicular (D2chr.v);
      [is_circular_chromatic adj r] - r is the attained minimum of p/q over the
      (p,q)-colourings of adj (foundations/circular_colouring.v, parametric in an abstract
      boolean adjacency, so it also applies to this INFINITE vertex type).
    Notes: the source graph has the lines through the origin in R^3 as vertices; the model here has
      all 3-vectors, so each line becomes an independent set of its non-zero multiples and the
      zero vector is isolated. Blowing a vertex up into an independent set and adding isolated
      vertices leaves the circular chromatic number unchanged, so this is a faithful
      representative model, but it is a modelling proxy rather than the literal object. The
      statement is quantified over every real-closed field, of which the reals are one
      instance. *)
Definition circular_colouring_the_orthogonality_graph_statement : Prop :=
  forall R : rcfType, is_circular_chromatic (@perp R) 4%:Q.
