(** * GTMisc.conjectures.U13 — milestone U13 (namespace GTMisc, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of twelve OPEN problems from the "miscellaneous graph theory"
    bucket.  CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph]): most rows are
    undirected simple graphs ([G : sgraph]); the interconnection-network rows
    (shuffle-exchange, Beneš) live on a square bipartite STAGE relation
    [rel 'I_t] with permutation routing; the union-of-degenerate-graphs row
    quantifies over two edge relations [r1 r2 : rel V] on a SHARED vertex
    type [V : finType] (an edge-union needs a common vertex set).

    REUSE FROM graph-theory-base (GTBase.base, imported below, which also
    re-exports the coq-graph-theory undirected vocabulary):
      - [cartesian_product] (□)  — Row 6 (pebbling of a product);
      - [subdivision]            — Row 2 (one-subdivision = [subdivision G 2]);
      - [regular]                — Row 7 (57-regular);
      - [girth_geq]              — Row 3 (girth > g = [girth_geq H g.+1]) and
                                   Row 7 (girth ≥ 5);
      - [ball]                   — Row 7 (distance ≤ k neighbourhood, for the
                                   diameter and girth-exactness predicates);
      - [is_hom]                 — Row 3 (subgraph = injective homomorphism).
    Every other notion below is AREA-SPECIFIC to this milestone (graph-theory-
    misc) and defined locally.  Two such primitives are shared by TWO rows of
    this same area — [n_edges]/[oedges] (Rows 3,8,9) and the multistage-routing
    layer [rearrangeable]/[multistage_route] (Rows 5,11) — but as they are used
    only inside this one area they stay local (a future second AREA needing them
    would trigger a [@MOVE-to-base]); no cross-area primitive is introduced here. *)

From GTBase Require Export base.
From mathcomp Require Import fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared local helpers (oriented edge set / edge count)

    An undirected simple graph's edges as a set of ORIENTED pairs [(lo,hi)]
    with [lo ≺ hi] in the [enum_rank] order — a canonical representative per
    undirected edge, so [#|oedges G|] is the true edge count |E(G)|.  Reused by
    Rows 3 (average degree), 8 (graceful: |E| labels) and 9 (edge imbalances). *)
Definition oedges (G : sgraph) : {set G * G} :=
  [set p : G * G | (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N].

Definition n_edges (G : sgraph) : nat := #|oedges G|.

(** ================================================================= *)
(** ** Row 1 — 2-colouring a graph without a monochromatic maximum clique
       (OPEN)

    Source: "Conjecture If G is a non-empty graph containing no induced odd
    cycle of length at least 5, then there is a 2-vertex colouring of G in which
    no maximum clique is monochromatic."

    Carrier: [G : sgraph].  AREA primitives:
      - [induced_cycle f] / [has_induced_cycle G k] (induced-odd-cycle): an
        induced k-cycle is given by an injective map [f : 'I_k -> G] whose only
        adjacencies are the cyclic-successor edges ([f i -- f j] iff [i],[j] are
        consecutive modulo [k]); "induced" = chord-free, captured by the [iff].
      - [is_max_clique] / [monochromatic] / [splits_max_cliques]
        (monochromatic-max-clique-partition): a Boolean 2-colouring [c] splits
        the maximum cliques iff no maximum clique (a clique of size ω(G)) is
        monochromatic. *)
Definition induced_cycle (G : sgraph) (k : nat) (f : 'I_k -> G) : Prop :=
  injective f /\
  forall i j : 'I_k,
    (f i -- f j) <-> ((val j == (val i).+1 %% k) || (val i == (val j).+1 %% k)).

Definition has_induced_cycle (G : sgraph) (k : nat) : Prop :=
  exists f : 'I_k -> G, induced_cycle f.

Definition is_max_clique (G : sgraph) (Q : {set G}) : Prop :=
  clique Q /\ #|Q| = ω([set: G]).

Definition monochromatic (G : sgraph) (c : G -> bool) (Q : {set G}) : Prop :=
  {in Q &, forall x y : G, c x = c y}.

Definition splits_max_cliques (G : sgraph) (c : G -> bool) : Prop :=
  forall Q : {set G}, is_max_clique Q -> ~ monochromatic c Q.

(** Corpus row: opg:2_colouring_a_graph_without_a_monochromatic_maximum_clique
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/2_colouring_a_graph_without_a_monochromatic_maximum_clique/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/2_colouring_a_graph_without_a_monochromatic_maximum_clique.json
    English statement: (Open Problem Garden, "2-colouring a graph without a monochromatic
      maximum clique")
      For every finite simple graph G with at least one vertex, if G has no induced cycle of
      odd length at least 5, then there is a two-colouring of the vertices of G in which no
      maximum clique is monochromatic, i.e. every clique of size omega(G) contains two vertices
      of different colours.
    Definitions: [induced_cycle f] / [has_induced_cycle G k] - an induced k-cycle is an
      injective map f from the k cyclic positions to V(G) whose only adjacencies are the
      cyclic-successor pairs, the iff clause making it chord-free (this file);
      [is_max_clique Q] - Q is a clique of size omega(G) (this file); [monochromatic c Q] - c
      is constant on Q (this file); [splits_max_cliques c] - no maximum clique is
      monochromatic under c (this file); [clique], [omega] - cliques and the clique number
      (coq-graph-theory / GTBase).
    Notes: "non-empty graph" is read as "at least one vertex" ([0 < #|G|]).  The colouring is a
      map into [bool], so exactly two colours are available and the colouring is not required
      to be proper. *)
Definition two_colouring_a_graph_without_a_monochromatic_maximu_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall k : nat, odd k -> 5 <= k -> ~ has_induced_cycle G k) ->
    exists c : G -> bool, splits_max_cliques c.

(** ================================================================= *)
(** ** Row 2 — Book thickness of subdivisions  (OPEN)

    Source: "A k-page book embedding of G consists of a linear order ≼ of V(G)
    and a (non-proper) k-colouring of E(G) such that edges with the same colour
    do not cross … The book thickness bt(G) is the minimum k for which there is
    a k-page book embedding of G.  Let G' be the graph obtained by subdividing
    each edge of G exactly once.  Conjecture There is a function f such that for
    every graph G, bt(G) ≤ f(bt(G'))."

    Carrier: [G : sgraph].  One-subdivision G' = [subdivision G 2] (one internal
    vertex per edge — base's [subdivision G n] has [n-1] internal vertices).

    AREA primitive [book_embedding] / [is_book_thickness] (book-thickness): a
    [k]-page book embedding is a vertex position map [pos] (injective ⇒ a linear
    order) and a symmetric edge-colouring [col] into [k] colours with no two
    same-coloured edges CROSSING ([pos a < pos c < pos b < pos d] for edges
    [ab],[cd]).  bt(G) is the least number of pages, stated relationally to stay
    proof-free; the conjecture is the existence of a bounding function [f]. *)
Definition book_embedding (G : sgraph) (k : nat) : Prop :=
  exists (pos : G -> nat) (col : G -> G -> nat),
    [/\ injective pos,
        (forall x y : G, col x y = col y x),
        (forall x y : G, col x y < k) &
        (forall a b c d : G,
           a -- b -> c -- d -> col a b = col c d ->
           ~~ ((pos a < pos c) && (pos c < pos b) && (pos b < pos d)))].

Definition is_book_thickness (G : sgraph) (k : nat) : Prop :=
  book_embedding G k /\ (forall m : nat, book_embedding G m -> k <= m).

Definition subdivide1 (G : sgraph) : sgraph := subdivision G 2.

(** Corpus row: opg:book_thickness_of_subdivisions
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/book_thickness_of_subdivisions/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/book_thickness_of_subdivisions.json
    English statement: (Open Problem Garden, "Book Thickness of Subdivisions")
      There is a function f from naturals to naturals such that, for every finite simple graph
      G, if bG is the book thickness of G and bG' is the book thickness of the graph obtained
      from G by subdividing every edge exactly once, then bG <= f(bG').
    Definitions: [book_embedding G k] - there are an injective vertex position map (a linear
      order) and a symmetric edge colouring into k colours such that no two edges of the same
      colour cross, crossing meaning pos a < pos c < pos b < pos d for edges ab and cd (this
      file); [is_book_thickness G k] - k is the least such number of pages (this file);
      [subdivide1 G] - the one-subdivision of G, i.e. [subdivision G 2], one internal vertex per
      edge (this file); [subdivision] - GTBase.
    Notes: the book thickness is stated relationally (as a predicate "k is the book thickness")
      rather than as a function, to stay proof-free; consequently the statement is conditional
      on both book thicknesses being realized, and says nothing about a graph for which no
      minimum exists.  The colouring is non-proper (edges sharing a vertex may share a
      colour), as in the source. *)
Definition book_thickness_of_subdivisions_statement : Prop :=
  exists f : nat -> nat,
    forall (G : sgraph) (bG bG' : nat),
      is_book_thickness G bG ->
      is_book_thickness (subdivide1 G) bG' ->
      bG <= f bG'.

(** ================================================================= *)
(** ** Row 3 — Subgraph of large average degree and large girth  (OPEN)

    Source: "Conjecture For all positive integers g and k, there exists an
    integer d such that every graph of average degree at least d contains a
    subgraph of average degree at least k and girth greater than g."

    Carrier: [G : sgraph].  AREA primitives:
      - [avgdeg_geq G d] (average-degree): avg degree = 2|E|/|V|, so
        "avg degree ≥ d" is the fraction-free [d * |V| ≤ 2|E|];
      - [subgraph_of H G] (subgraph): [H] is a (not necessarily induced)
        subgraph of [G] iff there is an injective homomorphism [H → G] (base's
        [is_hom] preserves edges), i.e. [G] contains a copy of [H].
    "girth greater than g" reuses base's [girth_geq] as [girth_geq H g.+1].
    Average degree is undefined on the empty graph in the source sense, so the
    host graph is guarded by [0 < #|G|] before applying the fraction-free
    average-degree premise. *)
Definition avgdeg_geq (G : sgraph) (d : nat) : Prop := average_degree_geq G d 1.

Definition subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G, injective f /\ is_hom f.

(** Corpus row: opg:subgraph_of_large_average_degree_and_large_average_degree
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/subgraph_of_large_average_degree_and_large_average_degree/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/subgraph_of_large_average_degree_and_large_average_degree.json
    English statement: (Open Problem Garden, "Subgraph of large average degree and large
      girth")
      For all positive integers g and k there is an integer d such that every finite simple
      graph G with at least one vertex and average degree at least d contains a non-empty
      subgraph H whose average degree is at least k and whose girth is greater than g.
    Definitions: [avgdeg_geq G d] - average degree at least d, in the fraction-free form
      d * |V(G)| <= 2 * |E(G)| (this file, via [average_degree_geq] of GTBase);
      [subgraph_of H G] - there is an injective homomorphism from H to G, i.e. G contains a
      copy of H, not necessarily induced (this file); [oedges] / [n_edges] - the edges of a
      simple graph as oriented pairs in [enum_rank] order, giving the true edge count (this
      file); [girth_geq H g.+1] - girth greater than g (GTBase); [is_hom] -
      adjacency preservation (coq-graph-theory).
    Notes: the host graph is guarded by [0 < #|G|] because average degree is undefined on the
      empty graph; the witness H is also required to be non-empty. *)
Definition subgraph_of_large_average_degree_and_large_average_d_statement : Prop :=
  forall g k : nat,
    0 < g -> 0 < k ->
    exists d : nat,
      forall G : sgraph,
        0 < #|G| ->
        avgdeg_geq G d ->
        exists H : sgraph,
          [/\ 0 < #|H|, subgraph_of H G, avgdeg_geq H k & girth_geq H g.+1].

(** ================================================================= *)
(** ** Row 4 — Colouring the union of degenerate graphs  (OPEN)

    Source: "Conjecture The union of a 1-degenerate graph (a forest) and a
    2-degenerate graph is 5-colourable."

    Carrier: a SHARED finite vertex type [V : finType] with two edge relations
    [r1 r2 : rel V] (an edge-union requires a common vertex set; representing
    each summand by its edge relation, symmetrised by [mk_sgraph], is faithful).
    AREA primitives:
      - [mk_sgraph r] : the simple graph on [V] with adjacency = the
        symmetric/irreflexive closure of [r] (a graph-from-relation helper);
      - [degenerate G k] (k-degenerate): every nonempty vertex set [S] has a
        vertex of [S]-degree ≤ k (the standard k-degeneracy);
      - [edge_union r1 r2] (edge-union): [mk_sgraph] of the union of the two
        edge relations.
    The hypotheses are [k_degenerate (mk_sgraph r1) 1] (a forest) and
    [k_degenerate (mk_sgraph r2) 2]. *)
Section EdgeUnion.
Variable V : finType.

Definition relAdj (r : rel V) : rel V :=
  fun x y => (x != y) && (r x y || r y x).
Lemma relAdj_sym (r : rel V) : symmetric (relAdj r).
Proof. by move=> x y; rewrite /relAdj eq_sym orbC. Qed.
Lemma relAdj_irrefl (r : rel V) : irreflexive (relAdj r).
Proof. by move=> x; rewrite /relAdj eqxx. Qed.
Definition mk_sgraph (r : rel V) : sgraph := SGraph (@relAdj_sym r) (@relAdj_irrefl r).

Definition edge_union (r1 r2 : rel V) : sgraph :=
  mk_sgraph (fun x y => r1 x y || r2 x y).
End EdgeUnion.

(** Corpus row: opg:coloring_the_union_of_degenerate_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/coloring_the_union_of_degenerate_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/coloring_the_union_of_degenerate_graphs.json
    English statement: (Open Problem Garden, "Coloring the union of degenerate graphs")
      For every non-empty finite vertex type V and all edge relations r1 and r2 on V, if the
      simple graph with edge relation r1 is 1-degenerate (a forest) and the simple graph with
      edge relation r2 is 2-degenerate, then the simple graph whose edges are the union of r1
      and r2 has chromatic number at most 5.
    Definitions: [relAdj] / [mk_sgraph r] - the simple graph on V whose adjacency is the
      symmetric irreflexive closure of r (this file); [edge_union r1 r2] - [mk_sgraph] of the
      pointwise disjunction of the two relations (this file); [k_degenerate G k] - every
      non-empty vertex set contains a vertex of degree at most k inside that set, which for
      k = 1 is exactly "forest" (GTBase, equal to [k_degenerate_on [set: G]]);
      [chi] - chromatic number (coq-graph-theory colouring).
    Notes: an edge union needs a common vertex set, so both summands are given as edge
      relations on one shared finite vertex type rather than as two [sgraph]s. *)
Definition coloring_the_union_of_degenerate_graphs_statement : Prop :=
  forall (V : finType) (r1 r2 : rel V),
    0 < #|V| ->
    k_degenerate (mk_sgraph r1) 1 ->
    k_degenerate (mk_sgraph r2) 2 ->
    χ([set: edge_union r1 r2]) <= 5.

(** ================================================================= *)
(** ** Multistage interconnection networks (shared by Rows 5 and 11)

    An ordered bipartite STAGE is a relation [S : rel 'I_t] (input position →
    output position; both sides are the linearly ordered set ['I_t]).  The
    [r]-fold concatenation of identical copies of [S] is the [r]-stage network
    whose vertices are [r+1] layers, each a copy of ['I_t], with [S] between
    consecutive layers.  AREA primitives:
      - [stage_regular S d] (multistage-graph, regularity): every input has
        out-degree [d] and every output in-degree [d];
      - [stage_reachable S m a b] / [externally_connected S m]: input [a]
        reaches output [b] through [m] stages / every input reaches every
        output (the network is externally connected);
      - [multistage_route S r route π] (edge-disjoint-routing): for a target
        permutation [π], [route i s] is the position of message [i] in layer
        [s]; it starts at [i], ends at [π i], steps along [S], and at EVERY
        layer the positions form a bijection (node-disjoint routing — each layer
        realises a permutation), which is the rearrangeability routing model;
      - [rearrangeable S r] (rearrangeable): every permutation is routable
        through the [r]-stage network. *)
Definition stage_regular {t : nat} (S : rel 'I_t) (d : nat) : Prop :=
  (forall i : 'I_t, #|[set j : 'I_t | S i j]| = d) /\
  (forall j : 'I_t, #|[set i : 'I_t | S i j]| = d).

Definition stage_reachable {t : nat} (S : rel 'I_t) (m : nat) (a b : 'I_t) : Prop :=
  exists w : seq 'I_t, [/\ size w = m, path S a w & last a w = b].

Definition externally_connected {t : nat} (S : rel 'I_t) (m : nat) : Prop :=
  forall a b : 'I_t, stage_reachable S m a b.

Definition multistage_route {t : nat} (S : rel 'I_t) (r : nat)
  (route : 'I_t -> nat -> 'I_t) (pi : {perm 'I_t}) : Prop :=
  [/\ (forall i : 'I_t, route i 0 = i),
      (forall i : 'I_t, route i r = pi i),
      (forall (i : 'I_t) (s : nat), s < r -> S (route i s) (route i s.+1)) &
      (forall s : nat, s <= r -> injective (route^~ s))].

Definition rearrangeable {t : nat} (S : rel 'I_t) (r : nat) : Prop :=
  forall pi : {perm 'I_t},
    exists route : 'I_t -> nat -> 'I_t, multistage_route S r route pi.

(** ================================================================= *)
(** ** Row 5 — Shuffle-Exchange conjecture (graph-theoretic form)  (OPEN)

    Source: "the 2-stage Shuffle-Exchange graph SE(k,n) is the simple k-regular
    bipartite graph with parts U,V of size t := k^{n-1}, with u_i ~ v_j iff
    (j - k i) mod t < k.  (SE(k,n))^{r-1} is the concatenation of r-1 copies of
    SE(k,n).  Let r(k,n) be the smallest r ≥ 2 such that (SE(k,n))^{r-1} is
    rearrangeable.  Conjecture r(k,n) = 2n-1."

    Carrier: the SE stage relation [se_adj k n : rel 'I_(k^(n-1))].  AREA
    primitive [se_adj] (shuffle-exchange-graph); routing via the shared
    [rearrangeable].  [(SE)^{r-1}] = the [(r-1)]-stage network, so r(k,n)=2n-1
    means: it is rearrangeable at [r-1 = 2n-2] stages, and no smaller [r ≥ 2]
    works.  The modular [(j - k i) mod t] is computed as
    [(j + (t - (k i mod t))) mod t]. *)
Definition se_adj (k n : nat) : rel 'I_(k ^ (n - 1)) :=
  fun i j =>
    let t := k ^ (n - 1) in
    (val j + (t - (k * val i) %% t)) %% t < k.

(** Corpus row: opg:shuffle_exchange_conjecture_graph_theoretic_form
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/shuffle_exchange_conjecture_graph_theoretic_form/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/shuffle_exchange_conjecture_graph_theoretic_form.json
    English statement: (Open Problem Garden, "Shuffle-Exchange Conjecture (graph-theoretic
      form)")
      For all integers k, n >= 2, writing SE(k,n) for the shuffle-exchange stage relation on
      the k^(n-1) positions (position i is joined to position j exactly when
      (j - k*i) mod k^(n-1) < k), the network made of 2n-2 consecutive copies of SE(k,n) is
      rearrangeable, and every r >= 2 for which r-1 copies already suffice satisfies
      r >= 2n-1.  Together these say that the least number of stages r(k,n) equals 2n-1.
    Definitions: [se_adj k n] - the shuffle-exchange stage relation above, with the modular
      difference computed as (j + (t - (k*i) mod t)) mod t for t = k^(n-1) (this file);
      [stage_regular], [stage_reachable], [externally_connected] - stage vocabulary (this
      file); [multistage_route S r route pi] - a routing of the permutation pi through r
      stages: every message starts at its own position, ends at its image, steps along S, and
      at every layer the positions form a bijection, i.e. node-disjoint routing (this file);
      [rearrangeable S r] - every permutation is so routable through r stages (this file).
    Notes: the corpus row contains both a "Problem (find r(k,n))" proposition and the
      "Conjecture r(k,n) = 2n-1"; only the conjecture is formalized, and as a conjunction of
      the achievability and the optimality halves rather than as an equality between r(k,n)
      and 2n-1, since r(k,n) is not introduced as a function.  Note the off-by-one convention
      of the source: (SE(k,n))^(r-1) denotes r-1 concatenated copies, so r = 2n-1 corresponds
      to [rearrangeable] at 2n-2 stages. *)
Definition shuffle_exchange_conjecture_statement : Prop :=
  forall k n : nat,
    2 <= k -> 2 <= n ->
    rearrangeable (@se_adj k n) (2 * n - 2) /\
    (forall r : nat, 2 <= r -> rearrangeable (@se_adj k n) (r - 1) -> 2 * n - 1 <= r).

(** ================================================================= *)
(** ** Row 6 — Pebbling a Cartesian product  (Graham's conjecture, OPEN)

    Source: "We let p(G) denote the pebbling number of a graph G.
    Conjecture p(G₁ □ G₂) ≤ p(G₁) p(G₂)."

    Carrier: [G : sgraph]; the product is base's [cartesian_product] (□).  AREA
    primitive [pebble_move]/[reaches]/[solvable]/[is_pebbling_number]
    (pebbling-number): a pebbling move removes 2 pebbles from a vertex and adds 1
    to an adjacent vertex; a distribution [D] is [r]-solvable if a pebble can be
    moved onto [r]; p(G) is the least [N] such that EVERY distribution of [N]
    pebbles is solvable for every target (stated relationally / least). *)
Definition pebble_move (G : sgraph) (D D' : G -> nat) : Prop :=
  exists u v : G,
    [/\ u -- v, 2 <= D u &
        forall w : G, D' w = if w == u then D u - 2
                             else if w == v then D v + 1 else D w].

Inductive reaches (G : sgraph) : (G -> nat) -> (G -> nat) -> Prop :=
| reaches_refl (D : G -> nat) : reaches D D
| reaches_step (D D' D'' : G -> nat) :
    pebble_move D D' -> reaches D' D'' -> reaches D D''.

Definition solvable (G : sgraph) (D : G -> nat) (r : G) : Prop :=
  exists D' : G -> nat, reaches D D' /\ 1 <= D' r.

Definition is_pebbling_number (G : sgraph) (N : nat) : Prop :=
  (forall D : G -> nat, \sum_(v : G) D v = N -> forall r : G, solvable D r) /\
  (forall M : nat,
     (forall D : G -> nat, \sum_(v : G) D v = M -> forall r : G, solvable D r) ->
     N <= M).

(** Corpus row: opg:pebbling_a_cartesian_product
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/pebbling_a_cartesian_product/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/pebbling_a_cartesian_product.json
    English statement: (Graham; Open Problem Garden, "Pebbling a cartesian product")
      For all non-empty finite simple graphs G1 and G2, if p1 is the pebbling number of G1, p2
      that of G2 and p12 that of their Cartesian product, then p12 <= p1 * p2.
    Definitions: [pebble_move D D'] - one pebbling move: remove two pebbles from a vertex and
      add one to an adjacent vertex (this file); [reaches] - the reflexive transitive closure
      of [pebble_move] (this file); [solvable D r] - some reachable distribution puts at least
      one pebble on the target r (this file); [is_pebbling_number G N] - N is the least number
      such that every distribution of exactly N pebbles is solvable for every target (this
      file); [cartesian_product] - the Cartesian graph product (GTBase).
    Notes: the pebbling numbers are stated relationally (a predicate "N is the pebbling number
      of G") rather than as a function, so the statement is conditional on all three minima
      being realized. *)
Definition pebbling_a_cartesian_product_statement : Prop :=
  forall (G1 G2 : sgraph) (p1 p2 p12 : nat),
    0 < #|G1| -> 0 < #|G2| ->
    is_pebbling_number G1 p1 ->
    is_pebbling_number G2 p2 ->
    is_pebbling_number (cartesian_product G1 G2) p12 ->
    p12 <= p1 * p2.

(** ================================================================= *)
(** ** Row 7 — 57-regular Moore graph  (OPEN)

    Source: "Question Does there exist a 57-regular graph with diameter 2 and
    girth 5?"

    Carrier: [G : sgraph].  Reuses base's [regular] (57-regular) and [ball]
    (distance-≤-k neighbourhood) / [girth_geq].  AREA primitives:
      - [has_diameter G d] (diameter): every pair is within distance [d] AND
        some pair is not within distance [d-1] (so diam = d exactly);
      - [has_girth G g] (girth): no cycle shorter than [g] ([girth_geq G g])
        and a genuine [g]-cycle exists (so girth = g exactly). *)
Definition has_diameter (G : sgraph) (d : nat) : Prop :=
  (forall u v : G, v \in ball d u) /\ (exists u v : G, v \notin ball d.-1 u).

(** Corpus row: opg:57_regular_moore_graph
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/57_regular_moore_graph/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/57_regular_moore_graph.json
    English statement: (Open Problem Garden, "57-regular Moore graph?")
      There exists a finite simple graph that is 57-regular, has diameter exactly 2 and girth
      exactly 5.
    Definitions: [has_diameter G d] - every pair of vertices lies within distance d and some
      pair does not lie within distance d-1, so the diameter is exactly d (this file);
      [has_girth G g] - no cycle shorter than g exists and a g-cycle does exist, so the girth
      is exactly g (GTBase); [regular G 57], [ball], [girth_geq] - regularity, distance balls
      and the girth lower bound (GTBase).
    Notes: the source asks a question; the Rocq body is its positive answer, an existential
      over graphs, so the open question is the truth value of the statement. *)
Definition fiftyseven_regular_moore_graph_statement : Prop :=
  exists G : sgraph, [/\ regular G 57, has_diameter G 2 & has_girth G 5].

(** ================================================================= *)
(** ** Row 8 — Graceful tree conjecture  (OPEN)

    Source: "Conjecture All trees are graceful."

    Carrier: [G : sgraph].  AREA primitives:
      - [is_tree_card G] (tree): connected with |E| = |V| - 1 (connected +
        acyclic).  Named [is_tree_card] (an edge-count characterization) to AVOID
        shadowing the re-exported [GraphTheory.core.sgraph.is_tree] (= forest +
        connected on a {set G}); the two agree on nonempty finite graphs.
      - [edge_label l p] / [graceful_labeling] (graceful-labeling): a vertex
        labelling [l : V → ℕ] is graceful iff it is injective with all labels in
        [0..|E|], and the induced edge labels [|l u - l v|] are DISTINCT and lie
        in [1..|E|] — with [|oedges| = |E|] this forces them to be exactly
        {1,…,|E|}, the classic gracefulness condition. *)
Definition is_tree_card (G : sgraph) : Prop :=
  connected [set: G] /\ n_edges G = #|G| - 1.

Definition edge_label (G : sgraph) (l : G -> nat) (p : G * G) : nat :=
  (l p.1 - l p.2) + (l p.2 - l p.1).

Definition graceful_labeling (G : sgraph) (l : G -> nat) : Prop :=
  [/\ injective l,
      (forall v : G, l v <= n_edges G),
      (forall p : G * G, p \in oedges G ->
         (1 <= edge_label l p) && (edge_label l p <= n_edges G)) &
      {in oedges G &, injective (edge_label l)}].

(** Corpus row: opg:graceful_tree_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/graceful_tree_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/graceful_tree_conjecture.json
    English statement: (Ringel-Kotzig; Open Problem Garden, "Graceful Tree Conjecture")
      Every finite simple graph with at least one vertex that is connected and has exactly
      |V| - 1 edges admits a graceful labelling: an injective vertex labelling into
      {0, ..., |E|} whose induced edge labels |l u - l v| are pairwise distinct and all lie
      between 1 and |E|.
    Definitions: [is_tree_card G] - connected with |E(G)| = |V(G)| - 1, an edge-count
      characterization of "tree" named so as not to shadow the re-exported
      [GraphTheory.core.sgraph.is_tree] (forest and connected on a vertex set); the two agree
      on non-empty finite graphs (this file); [edge_label l p] - the truncated-subtraction form
      of the absolute difference of the two endpoint labels (this file);
      [graceful_labeling l] - the four conditions above (this file); [oedges] / [n_edges] - the
      oriented-pair edge set and the edge count (this file); [connected] - coq-graph-theory
      connectivity.
    Notes: with |oedges G| = |E(G)| the two conditions "edge labels are distinct" and "edge
      labels lie in 1..|E|" force the edge labels to be exactly the set {1, ..., |E|}, which
      is the classical gracefulness condition. *)
Definition graceful_tree_statement : Prop :=
  forall G : sgraph, 0 < #|G| -> is_tree_card G -> exists l : G -> nat, graceful_labeling l.

(** ================================================================= *)
(** ** Row 9 — Imbalance conjecture  (OPEN)

    Source: "Conjecture Suppose that for all edges e ∈ E(G) we have imb(e) > 0.
    Then M_G is graphic."

    Carrier: [G : sgraph].  AREA primitives:
      - [imb p] (edge-imbalance): the imbalance of edge [p = (u,v)] is
        [|deg u - deg v|];
      - [seq_M_G G] : the sequence of edge imbalances (over [oedges G]) — the
        multiset M_G;
      - [graphic s] (graphic-sequence): [s : seq ℕ] is graphic iff it is the
        degree sequence of some simple graph [H] (up to permutation). *)
Definition vdeg (G : sgraph) (v : G) : nat := #|N(v)|.

Definition imb (G : sgraph) (p : G * G) : nat :=
  (vdeg p.1 - vdeg p.2) + (vdeg p.2 - vdeg p.1).

Definition seq_M_G (G : sgraph) : seq nat := [seq imb p | p <- enum (oedges G)].

Definition graphic (s : seq nat) : Prop :=
  exists H : sgraph, perm_eq s [seq #|N(v)| | v <- enum [set: H]].

(** Corpus row: opg:imbalance_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/imbalance_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/imbalance_conjecture.json
    English statement: (Open Problem Garden, "Imbalance conjecture")
      For every finite simple graph G, if every edge uv of G has imbalance |deg u - deg v| > 0,
      then the sequence of edge imbalances of G is graphic, i.e. it is a permutation of the
      degree sequence of some finite simple graph.
    Definitions: [vdeg v] - the degree of v (this file); [imb p] - the truncated-subtraction
      form of |deg u - deg v| for the oriented edge p = (u,v) (this file); [seq_M_G G] - the
      sequence of edge imbalances over [oedges G], i.e. the multiset M_G of the source (this
      file); [graphic s] - s is a permutation of the degree sequence of some [sgraph] (this
      file); [oedges] - the canonical oriented representative of each undirected edge (this
      file).
    Notes: M_G is modelled as a [seq nat] in the [enum] order of [oedges G] and "graphic" is
      taken up to permutation ([perm_eq]), so the order of the sequence is immaterial, as it
      should be for a multiset.  No guard on the emptiness of G: on the empty graph the
      hypothesis is vacuous and the empty sequence is graphic. *)
Definition imbalance_statement : Prop :=
  forall G : sgraph,
    (forall p : G * G, p \in oedges G -> 0 < imb p) ->
    graphic (seq_M_G G).

(** ================================================================= *)
(** ** Row 10 — A gold-grabbing game  (Problem: find optimal strategies)

    Source: "Fix a tree T and for every vertex v a non-negative integer g(v)
    (gold).  Players alternate; on each turn a player takes the gold at a LEAF
    and deletes it.  The winner accumulates the most gold.  Problem Find optimal
    strategies for the players."

    Carrier: a tree [G : sgraph] with gold [g : V → ℕ].  AREA primitives:
      - [is_leaf S v] (leaf-removal-game): [v ∈ S] is TAKEABLE in the remaining
        forest [S] iff it has AT MOST one neighbour inside [S] (degree ≤ 1) — so
        the final isolated vertex is takeable and its gold is counted (a leaf, or
        the last lone vertex);
      - [leaf_game_solution g val sigma] (game-value): [val S] is the game value
        from state [S] for the player to move and [sigma] an optimal move
        function, characterised by the Bellman optimality recursion — total gold
        being fixed, the mover guarantees [g v + (total(S∖v) − val(S∖v))] by
        taking leaf [v], so [val S] is the max over leaves and [sigma S] attains
        it.  Existence of such [(val,sigma)] is the "optimal strategies" the
        problem asks for. *)
Definition is_leaf (G : sgraph) (S : {set G}) (v : G) : bool :=
  (v \in S) && (#|N(v) :&: S| <= 1).

Definition gold_total (G : sgraph) (g : G -> nat) (S : {set G}) : nat :=
  \sum_(v in S) g v.

Definition leaf_game_solution (G : sgraph) (g : G -> nat)
  (val : {set G} -> nat) (sigma : {set G} -> G) : Prop :=
  forall S : {set G},
    (~ (exists v : G, is_leaf S v) -> val S = 0) /\
    ((exists v : G, is_leaf S v) ->
       [/\ is_leaf S (sigma S),
           val S = g (sigma S) + gold_total g (S :\ sigma S) - val (S :\ sigma S) &
           (forall w : G, is_leaf S w ->
              g w + gold_total g (S :\ w) - val (S :\ w) <= val S)]).

(** Corpus row: opg:a_gold_grabbing_game
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/a_gold_grabbing_game/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/a_gold_grabbing_game.json
    English statement: (Open Problem Garden, "A gold-grabbing game")
      For every non-empty tree G (connected with |V| - 1 edges) and every assignment g of a
      non-negative amount of gold to each vertex, there exist a value function val on vertex
      subsets and a move function sigma satisfying the Bellman optimality recursion of the
      leaf-removal game: val is 0 on states with no takeable vertex, and otherwise sigma S is
      takeable, val S equals g(sigma S) plus the gold remaining in S minus sigma S minus
      val(S minus sigma S), and no other takeable vertex w gives a larger value.
    Definitions: [is_leaf S v] - v belongs to the remaining set S and has at most one
      neighbour inside S, so leaves and the last isolated vertex are takeable (this file);
      [gold_total g S] - the sum of the gold on S (this file); [leaf_game_solution g val sigma]
      - the Bellman recursion above (this file); [is_tree_card G] - connected with |E| = |V| - 1
      (this file).
    Notes: the corpus proposition is a Problem ("find optimal strategies"), not a yes/no
      claim.  The chosen rendering is the existence of an optimal-play value function together
      with an attaining move function - the standard game-theoretic meaning of "optimal
      strategies" for this finite perfect-information game.  Because the total gold in a state
      is fixed, the mover taking v guarantees g v + (total(S minus v) - val(S minus v)), which
      is the right-hand side of the recursion; so val S is the max over takeable vertices and
      sigma S attains it.  All arithmetic is on naturals, hence truncated subtraction. *)
Definition a_gold_grabbing_game_statement : Prop :=
  forall (G : sgraph) (g : G -> nat),
    0 < #|G| ->
    is_tree_card G ->
    exists (val : {set G} -> nat) (sigma : {set G} -> G),
      leaf_game_solution g val sigma.

(** ================================================================= *)
(** Corpus row: opg:bene_conjecture_graph_theoretic_form_0
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/bene_conjecture_graph_theoretic_form_0/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/bene_conjecture_graph_theoretic_form_0.json
    English statement: (Benes; Open Problem Garden, "Benes Conjecture (graph-theoretic form)")
      For every t > 0, every relation L on the t ordered positions and every d, if L is
      d-regular (every input has out-degree d and every output in-degree d), then for every
      m >= 1 such that L is externally connected in m steps (every input reaches every output
      through m copies of L), the 2m-stage network built from L is rearrangeable, i.e. every
      permutation of the t positions can be routed node-disjointly through 2m stages.
    Definitions: [stage_regular L d] - d-regularity of the stage on both sides (this file);
      [stage_reachable L m a b] / [externally_connected L m] - reachability through exactly m
      stages / from every input to every output (this file); [multistage_route L r route pi] -
      a node-disjoint routing of the permutation pi through r stages (this file);
      [rearrangeable L r] - every permutation is so routable (this file).
    Notes: a "simple regular ordered 2-stage graph" of the source is modelled as one bipartite
      layer L between two copies of the linearly ordered set of t positions, which is what the
      r-fold concatenation iterates; L^m is m concatenated copies.  The corpus row also carries
      a Problem proposition (find a sufficient condition for rearrangeability of a straight
      l-stage graph); only the Conjecture proposition is formalized. *)
Definition bene_conjecture_graph_theoretic_form_0_statement : Prop :=
  forall (t : nat) (L : rel 'I_t) (d : nat),
    0 < t ->
    stage_regular L d ->
    forall m : nat,
      1 <= m ->
      externally_connected L m ->
      rearrangeable L (2 * m).

(** ================================================================= *)
(** ** Row 12 — Weighted colouring of hexagonal graphs  (OPEN)

    Source: "Conjecture There is an absolute constant c such that for every
    hexagonal graph G and vertex weighting p : V(G) → ℕ,
    χ(G,p) ≤ (9/8) ω(G,p) + c."

    Carrier: [G : sgraph] with a weight [p : V → ℕ].  AREA primitives:
      - [hexagonal G] (hexagonal-graph): an INDUCED subgraph of the triangular
        lattice — there is an injective coordinate embedding [φ : V → ℕ×ℕ] with
        adjacency in [G] iff triangular-lattice adjacency [tri_adj] of images;
      - [weighted_clique_number p w] (weighted-clique): ω(G,p) = max over cliques
        of the total weight Σ_{v∈Q} p v (relational);
      - [weighted_chromatic_number p k] (weighted-chromatic): χ(G,p) = least [k]
        admitting a multicolouring [f : V → {set 'I_k}] with [|f v| = p v] and
        disjoint colour sets on adjacent vertices.
    The bound χ ≤ (9/8) ω + c is stated fraction-free as [8χ ≤ 9ω + 8c]. *)
Definition tri_adj (a b : nat * nat) : bool :=
  let: (x1, y1) := a in let: (x2, y2) := b in
  [|| ((x2 == x1.+1) && (y2 == y1)),
      ((x1 == x2.+1) && (y1 == y2)),
      ((x1 == x2) && (y2 == y1.+1)),
      ((x1 == x2) && (y1 == y2.+1)),
      ((x2 == x1.+1) && (y1 == y2.+1)) |
      ((x1 == x2.+1) && (y2 == y1.+1))].

Definition hexagonal (G : sgraph) : Prop :=
  exists phi : G -> nat * nat,
    injective phi /\
    (forall u v : G, u != v -> (u -- v) = tri_adj (phi u) (phi v)).

Definition weighted_clique_number (G : sgraph) (p : G -> nat) (w : nat) : Prop :=
  (exists Q : {set G}, clique Q /\ \sum_(v in Q) p v = w) /\
  (forall Q : {set G}, clique Q -> \sum_(v in Q) p v <= w).

Definition weighted_colourable (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  exists f : G -> {set 'I_k},
    (forall v : G, #|f v| = p v) /\
    (forall x y : G, x -- y -> [disjoint f x & f y]).

Definition weighted_chromatic_number (G : sgraph) (p : G -> nat) (k : nat) : Prop :=
  weighted_colourable p k /\ (forall m : nat, weighted_colourable p m -> k <= m).

(** Corpus row: opg:weighted_colouring_of_hexagonal_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/weighted_colouring_of_hexagonal_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/weighted_colouring_of_hexagonal_graphs.json
    English statement: (Open Problem Garden, "Weighted colouring of hexagonal graphs")
      There is a constant c such that for every hexagonal graph G, every vertex weighting p of
      G, every weighted chromatic number chiP of (G,p) and every weighted clique number omegaP
      of (G,p), the inequality 8 * chiP <= 9 * omegaP + 8 * c holds, which is the
      fraction-free form of chi(G,p) <= (9/8) * omega(G,p) + c.
    Definitions: [tri_adj] - adjacency of the triangular lattice on integer coordinate pairs
      (this file); [hexagonal G] - G is an induced subgraph of the triangular lattice, i.e.
      there is an injective coordinate map whose images are [tri_adj]-adjacent exactly for the
      adjacent vertices of G (this file); [weighted_clique_number p w] - w is the maximum over
      cliques Q of the total weight of Q (this file); [weighted_colourable p k] /
      [weighted_chromatic_number p k] - each vertex v receives a set of exactly p v colours out
      of k, adjacent vertices receiving disjoint sets, and k is least with this property (this
      file); [clique] - coq-graph-theory.
    Notes: the two weighted parameters are stated relationally rather than as functions, so
      the statement is conditional on both extrema being realized.  c ranges over naturals, so
      "absolute constant" is read as a non-negative integer, which is no loss for an upper
      bound. *)
Definition weighted_colouring_of_hexagonal_graphs_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (p : G -> nat) (chiP omegaP : nat),
      hexagonal G ->
      weighted_chromatic_number p chiP ->
      weighted_clique_number p omegaP ->
      8 * chiP <= 9 * omegaP + 8 * c.
