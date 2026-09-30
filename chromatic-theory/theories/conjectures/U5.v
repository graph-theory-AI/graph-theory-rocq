(** * Chromatic.conjectures.U5 — milestone U5 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of nine open/partial problems on EDGE and TOTAL colouring: strong
    edge colouring (Erdős–Nešetřil), Seymour's r-graph conjecture, the 3-edge-
    colouring conjecture, Goldberg's conjecture, a hypergraph generalization of
    Vizing's theorem, universal Steiner triple systems, acyclic edge colouring,
    the star chromatic index of (sub)cubic graphs, and Behzad's total colouring
    conjecture.

    CARRIER TYPES (chosen per row.rocq_idiom, NOT a blanket sgraph):
      - Rows 1, 7, 8 (strong / acyclic / star EDGE colouring of SIMPLE graphs):
        carrier [sgraph]; an edge colouring is modelled as a SYMMETRIC function
        [col : G -> G -> 'I_k] on adjacent vertex pairs (a simple graph has at
        most one edge per pair), avoiding a separate edge type.
      - Rows 2, 3, 4, 6, 9 (r-graphs / cubic / multigraph / total colouring):
        carrier [mgraph] = [graph unit unit] (coq-graph-theory multigraphs),
        using the raw [edge]/[source]/[target]/[incident]/[edges_at]/[edge_set]
        API, with edge- and total-chromatic numbers via base's line/total graph.
      - Row 5 (d-uniform hypergraph): a finite incidence record [hypergraph].

    CORE undirected vocabulary + the edge/total-colouring layer come from
    graph-theory-base (GTBase.base): [sgraph], [x -- y], [χ]=[chi_mem],
    ['K_n], [Delta] (Δ for sgraph), [ceil_div], [connected], [ucycleb], and the
    PROMOTED edge/total surface [mgraph] notation, [loopless], [line_graph],
    [total_graph], [chromatic_index] (χ'), [total_chromatic_number] (χ''),
    [edge_colourable], [total_colourable].  These are REUSED verbatim; no base
    primitive is redefined.  coq-graph-theory's [mgraph] module is imported
    BEFORE base (its DIRECTED [line_graph] is then shadowed by base's undirected
    one) to expose the raw multigraph edge API.

    AREA-SPECIFIC primitives introduced here (edge/total-colouring vocabulary):
      - [strong_edge_colourable] (+ [near_edge]/[diff_edge]) : strong chromatic
        index sχ' as colourability (Row 1);
      - [mDelta] : multigraph maximum degree (parallel edges counted) — a
        cross-area primitive shared with U4, tagged [@MOVE-to-base];
      - [regular_m] / [cubic] : multigraph regularity / 3-regularity (same
        degree-with-parallel-edges family as [mDelta], so likewise tagged
        [@MOVE-to-base] for the next multigraph milestone);
      - [msimple] : a simple multigraph (loopless + no parallel edges), used to
        restrict Behzad's conjecture (Row 9) to the SIMPLE-graph setting in
        which it is open (over multigraphs the Δ+2 upper bound is false);
      - [edge_boundary] / [is_r_graph] : edge cut δ(X) and Seymour r-graphs (Row 2);
      - [remove_edge] / [usimple] / [mconnected] / [subdivide_edge_s] /
        [subdivR_s] / [homeomorphic_s] : edge deletion, the underlying simple
        graph, connectivity, single-edge subdivision and the common-subdivision
        homeomorphism used for the homeomorphic cubic reduction (Row 3);
      - [overfull_parameter] : Goldberg's density parameter w(G) (Row 4);
      - [hypergraph] / [uniform_hg] / [simple_hg] / [hg_codegree_le] : finite
        d-uniform hypergraphs and codegree (Row 5);
      - [sts] / [sts_valid] / [sts_edge_colourable] / [is_universal_sts] :
        Steiner triple systems and STS-edge-colouring (Row 6);
      - [acyclic_edge_colouring] (+ [edge_colour_seq]) : Row 7;
      - [star_edge_colouring] : Row 8. *)

(* mgraph imported BEFORE base: coq-graph-theory's mgraph defines a DIRECTED `line_graph`
   (DiGraph, target=source); importing it first lets base's undirected sgraph line_graph/
   total_graph shadow it. We use mgraph for the raw edge/incident/edges_at/source/target API. *)
From GraphTheory Require Import mgraph.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    SHARED AREA PRIMITIVES
    ========================================================================== *)

(** [mDelta] (multigraph maximum degree, parallel edges counted) — PROMOTED to graph-theory-base
    (U4 ∩ U5 triggered the migration); reused here via the base export. *)

(** [r]-regularity / cubicity of a multigraph (degree = #incident edges).
    Same degree-with-parallel-edges family as [mDelta]; promote together.
    [@MOVE-to-base] *)
Definition regular_m (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.
Definition cubic (G : mgraph) : Prop := regular_m G 3.

(** Simple multigraph: loopless and no two distinct edges share an unordered
    endpoint pair (no parallel edges).  [edge_ends e] is the (≤2-element) set of
    endpoints of [e]; injectivity of [edge_ends] on a loopless graph rules out
    parallel edges, so [msimple G] is exactly "G is a simple graph presented as
    a multigraph".  Used to restrict Behzad's conjecture to simple graphs. *)
Definition edge_ends (G : mgraph) (e : edge G) : {set G} :=
  [set source e; target e].
Definition msimple (G : mgraph) : Prop :=
  loopless G /\ injective (@edge_ends G).

(** ** Underlying simple graph, edge deletion, connectivity (for Rows 3, 6) ****)

(** [madj] (base) is the underlying simple adjacency of a multigraph; we package
    it as an [sgraph] to reuse base's [connected]. *)
Lemma madj_sym (G : mgraph) : symmetric (@madj G).
Proof.
move=> x y; rewrite /madj eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[w Hw]; exists w; rewrite andbC.
Qed.
Lemma madj_irrefl (G : mgraph) : irreflexive (@madj G).
Proof. by move=> x; rewrite /madj eqxx. Qed.
Definition usimple (G : mgraph) : sgraph := SGraph (@madj_sym G) (@madj_irrefl G).
Definition mconnected (G : mgraph) : Prop := connected [set: usimple G].

(** Delete one edge (vertex type unchanged). *)
Definition remove_edge (G : mgraph) (e : edge G) : mgraph := remove_edges [set e].

(** ============================================================================
    Row 1 — Strong edge colouring (Erdős–Nešetřil) — PARTIAL.
    "A strong edge-colouring colours edges so every colour class is an INDUCED
    matching (any two vertices on distinct equicoloured edges are non-adjacent);
    sχ'(G) is the minimum number of colours.  Conjecture sχ'(G) ≤ 5Δ²/4 if Δ
    even, (5Δ²−2Δ+1)/4 if Δ odd."  Edges modelled as a symmetric [col] on
    adjacent vertex pairs; two edges {x,y},{u,v} are [near] iff they share a
    vertex or an endpoint of one is adjacent to an endpoint of the other (line-
    graph distance ≤ 1) — a strong colouring keeps NEAR distinct edges apart.
    ========================================================================== *)

Definition diff_edge (G : sgraph) (x y u v : G) : bool :=
  ~~ (((x == u) && (y == v)) || ((x == v) && (y == u))).

Definition near_edge (G : sgraph) (x y u v : G) : bool :=
  [|| x == u, x == v, y == u, y == v, x -- u, x -- v, y -- u | y -- v].

Definition strong_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> G -> 'I_k,
    (forall x y : G, col x y = col y x) /\
    (forall x y u v : G, x -- y -> u -- v ->
        diff_edge x y u v -> near_edge x y u v -> col x y != col u v).

(** Corpus row: opg:strong_edge_colouring_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/strong_edge_colouring_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/strong_edge_colouring_conjecture.json
    English statement: (Erdos and Nesetril 1989; Open Problem Garden, "Strong edge colouring conjecture")
      Every finite simple graph G with maximum degree at least 1 has a strong edge colouring using
      5*Delta^2/4 colours when Delta is even and (5*Delta^2 - 2*Delta + 1)/4 colours when Delta is
      odd, where a strong edge colouring gives distinct colours to any two distinct edges that share
      a vertex or have an endpoint of one adjacent to an endpoint of the other, i.e. every colour
      class is an induced matching.
    Definitions: [strong_edge_colourable G k] - there is a symmetric map col from ordered vertex
      pairs to ['I_k] such that any two adjacent pairs that are distinct as unordered pairs and are
      near receive different colours (this file); [diff_edge x y u v] - the unordered pairs {x,y}
      and {u,v} differ (this file); [near_edge x y u v] - the two pairs share a vertex or some
      endpoint of one is adjacent to some endpoint of the other, i.e. line-graph distance at most 1
      (this file); [Delta] (GTBase base/theories/base.v).
    Notes: Edges are modelled as a SYMMETRIC function on adjacent vertex pairs rather than as a
      separate edge type, which is faithful for simple graphs since a pair carries at most one edge.
      Both bounds are exact integers, 4 divides 5*Delta^2 for even Delta and 5*Delta^2 - 2*Delta + 1
      for odd Delta, so the truncating nat division %/ 4 loses nothing. The guard 0 < Delta G
      excludes the edgeless case, where the even branch would give the bound 0 and force a total
      function into the empty ordinal, making the statement false for a degenerate reason; the
      excluded case is trivially true mathematically. *)
Definition strong_edge_colouring_statement : Prop :=
  forall G : sgraph, 0 < Delta G ->
    strong_edge_colourable G
      (if odd (Delta G)
       then (5 * (Delta G) ^ 2 - 2 * (Delta G) + 1) %/ 4
       else (5 * (Delta G) ^ 2) %/ 4).

(** ============================================================================
    Row 2 — Seymour's r-graph conjecture — OPEN.
    "An r-graph is an r-regular G with |δ(X)| ≥ r for every X ⊆ V(G) of odd
    size.  Conjecture χ'(G) ≤ r+1 for every r-graph G."  δ(X) = edges with
    exactly one endpoint in X.
    ========================================================================== *)

Definition edge_boundary (G : mgraph) (X : {set G}) : {set edge G} :=
  [set e | (source e \in X) (+) (target e \in X)].

Definition is_r_graph (G : mgraph) (r : nat) : Prop :=
  (forall v : G, #|edges_at v| = r) /\
  (forall X : {set G}, odd #|X| -> r <= #|edge_boundary X|).

(** Corpus row: opg:seymours_r_graph_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/seymours_r_graph_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/seymours_r_graph_conjecture.json
    English statement: (Seymour 1979; Open Problem Garden, "Seymour's r-graph conjecture")
      For every r and every multigraph G that is an r-graph, that is every vertex is incident with
      exactly r edges and every vertex set of odd size has at least r edges in its edge boundary,
      the chromatic index of G is at most r.
    Definitions: [is_r_graph G r] - r-regularity counted with parallel edges together with the
      odd-cut condition |edge boundary of X| >= r for every X of odd size (this file);
      [edge_boundary X] - the edges with exactly one endpoint in X (this file); [edge_colourable G
      k] - the chromatic index of G, i.e. chi of its line graph, is at most k (GTBase
      base/theories/base.v).
    Notes: DISCREPANCY with the corpus text: the source conjecture is chi'(G) <= r + 1 for every
      r-graph, whereas the Rocq body concludes [edge_colourable G r], i.e. chi'(G) <= r. As written
      the Rocq statement is strictly stronger than Seymour's conjecture and is in fact refutable:
      the Petersen graph is a 3-graph with chromatic index 4. This is recorded in
      meta/STATEMENT_IMPROVEMENTS.md; the body is left untouched here, WP4 changes comments only. *)
Definition seymours_r_graph_statement : Prop :=
  forall (r : nat) (G : mgraph), is_r_graph G r -> edge_colourable G r.

(** ============================================================================
    Row 3 — 3-edge-colouring conjecture — OPEN.
    "G connected cubic with |V(G)|>2 admitting a 3-edge-colouring ⇒ ∃ e ∈ E(G)
    such that the cubic graph homeomorphic to G−e has a 3-edge-colouring."  The
    "cubic graph homeomorphic to G−e" is captured by [homeomorphic_s]: H is a
    cubic multigraph whose underlying simple graph is homeomorphic to that of
    G−e, where homeomorphism = common subdivision of underlying simple graphs.
    ========================================================================== *)

(** Single-edge subdivision of a simple graph: replace edge x–y by a new degree-2
    vertex [inr tt] adjacent to x and y. *)
Section SubdivS.
Variables (G : sgraph) (x y : G).
Definition sds_rel : rel (G + unit) :=
  fun a b =>
    match a, b with
    | inl u, inl v => (u -- v) && ~~ (((u == x) && (v == y)) || ((u == y) && (v == x)))
    | inl u, inr _ => (u == x) || (u == y)
    | inr _, inl v => (v == x) || (v == y)
    | inr _, inr _ => false
    end.
Lemma sds_sym : symmetric sds_rel.
Proof.
move=> a b; case: a => [u|[]]; case: b => [v|[]] //=.
rewrite sg_sym; congr (_ && _); congr (~~ _).
by case: (u == x); case: (u == y); case: (v == x); case: (v == y).
Qed.
Lemma sds_irrefl : irreflexive sds_rel.
Proof. by move=> [u|[]] //=; rewrite sgP. Qed.
Definition subdivide_edge_s : sgraph := SGraph sds_sym sds_irrefl.
End SubdivS.

(** [K] is a subdivision of [G]: reachable from [G] by finitely many single-edge
    subdivisions (up to simple-graph isomorphism [≃] = [diso]). *)
Inductive subdivR_s : sgraph -> sgraph -> Prop :=
| subdivR_s_refl (G : sgraph) : subdivR_s G G
| subdivR_s_step (G H K : sgraph) (x y : H) :
    subdivR_s G H -> (subdivide_edge_s x y ≃ K) -> subdivR_s G K.

(** Topological equivalence of simple graphs: a common subdivision. *)
Definition homeomorphic_s (G H : sgraph) : Prop :=
  exists K : sgraph, subdivR_s K G /\ subdivR_s K H.

(** Corpus row: opg:3_edge_coloring_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/3_edge_coloring_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/3_edge_coloring_conjecture.json
    English statement: (Open Problem Garden, "3-Edge-Coloring Conjecture")
      For every loopless cubic multigraph G that is connected, has more than two vertices and has a
      proper 3-edge-colouring, there are an edge e of G and a cubic multigraph H such that the
      underlying simple graph of H is homeomorphic to the underlying simple graph of G with e
      deleted, and H also has a proper 3-edge-colouring.
    Definitions: [cubic G] - every vertex is incident with exactly 3 edges, parallel edges counted
      (this file); [mconnected G] - the underlying simple graph is [connected] (this file);
      [remove_edge e] - delete the single edge e (this file); [usimple G] - the underlying simple
      graph of a multigraph, built from base's [madj] (this file); [homeomorphic_s G H] - G and H
      have a common subdivision, where [subdivR_s] is the reflexive-transitive closure of single-
      edge subdivision up to graph isomorphism (this file); [edge_colourable G 3] - chromatic index
      at most 3 (GTBase base/theories/base.v).
    Notes: The source phrase "the cubic graph homeomorphic to G-e" is encoded as an EXISTENTIAL
      over cubic multigraphs H whose underlying simple graph is homeomorphic to that of G-e, since
      suppressing the two degree-2 vertices of G-e is not a primitive here. Homeomorphism is taken
      on the underlying SIMPLE graphs, so parallel edges created by the suppression are not tracked. *)
Definition three_edge_coloring_statement : Prop :=
  forall G : mgraph,
    loopless G -> cubic G -> mconnected G -> 2 < #|G| -> edge_colourable G 3 ->
    exists (e : edge G) (H : mgraph),
      [/\ cubic H,
          homeomorphic_s (usimple (remove_edge e)) (usimple H)
        & edge_colourable H 3].

(** ============================================================================
    Row 4 — Goldberg's conjecture — OPEN.
    "w(G) = max over H ⊆ G of ⌈|E(H)| / ⌊|V(H)|/2⌋⌉.  Every G satisfies
    χ'(G) ≤ max{Δ(G)+1, w(G)}."  The max ranges over induced subgraphs (vertex
    subsets S), with |E(H)| = #|edge_set S|, |V(H)| = #|S|; ⌈·/·⌉ = ceil_div
    (ceil_div a 0 = 0, so the |S|≤1 terms vanish).
    ========================================================================== *)

Definition overfull_parameter (G : mgraph) : nat :=
  \max_(S : {set G}) ceil_div #|edge_set S| (#|S| %/ 2).

(** Corpus row: opg:goldbergs_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/goldbergs_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/goldbergs_conjecture.json
    English statement: (Goldberg 1973, also Seymour 1979; Open Problem Garden, "Goldberg's conjecture")
      Every multigraph G satisfies chi'(G) <= max(Delta(G) + 1, w(G)), where w(G) is the maximum
      over vertex subsets S of the ceiling of the number of edges inside S divided by the floor of
      |S|/2.
    Definitions: [overfull_parameter G] - the maximum over all vertex sets S of [ceil_div
      #|edge_set S| (#|S| %/ 2)] (this file); [ceil_div a b] - ceiling of a/b with ceil_div a 0 = 0
      (GTBase base/theories/base.v); [mDelta G] - maximum degree of a multigraph, parallel edges
      counted (base.v); [chromatic_index G] - chi of the line graph (base.v); [edge_set S] - the
      edges with both endpoints in S (coq-graph-theory mgraph.v).
    Notes: The source maximum ranges over all subgraphs H of G; the Rocq body ranges over INDUCED
      subgraphs, given by vertex sets S, which is equivalent since removing edges only decreases the
      numerator. The convention ceil_div a 0 = 0 makes the terms with |S| <= 1 vanish, as intended. *)
Definition goldbergs_statement : Prop :=
  forall G : mgraph,
    chromatic_index G <= maxn (mDelta G).+1 (overfull_parameter G).

(** ============================================================================
    Row 5 — A generalization of Vizing's theorem — OPEN.
    "H a simple d-uniform hypergraph; every set of d−1 points lies in ≤ r edges.
    Then ∃ an (r+d−1)-edge-colouring so that any two edges sharing d−1 vertices
    have distinct colours."
    ========================================================================== *)

Record hypergraph := Hypergraph {
  hv : finType;
  he : finType;
  hinc : he -> {set hv} }.

(** [d]-uniformity: every edge has exactly d points. *)
Definition uniform_hg (H : hypergraph) (d : nat) : Prop :=
  forall e : he H, #|hinc e| = d.
(** Simplicity: distinct edges are distinct point sets. *)
Definition simple_hg (H : hypergraph) : Prop := injective (@hinc H).
(** Codegree ≤ r: every (d−1)-set lies in at most r edges. *)
Definition hg_codegree_le (H : hypergraph) (d r : nat) : Prop :=
  forall T : {set hv H}, #|T| = d.-1 -> #|[set e | T \subset hinc e]| <= r.

(** Corpus row: opg:a_generalization_of_vizings_theorem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/a_generalization_of_vizings_theorem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/a_generalization_of_vizings_theorem.json
    English statement: (Open Problem Garden, "A generalization of Vizing's Theorem?")
      For every simple d-uniform hypergraph H with d at least 1, in which every set of d-1 points is
      contained in at most r edges, there is a colouring of the edges by r + d - 1 colours such that
      any two distinct edges whose intersection has exactly d-1 points receive different colours.
    Definitions: [hypergraph] - a record with a finite point type, a finite edge type and an
      incidence map sending each edge to its point set (this file); [uniform_hg H d] - every edge
      has exactly d points (this file); [simple_hg H] - distinct edges have distinct point sets
      (this file); [hg_codegree_le H d r] - every set of d-1 points is contained in at most r edges
      (this file).
    Notes: The number of colours r + d - 1 uses truncated nat subtraction, harmless under the
      guard 1 <= d. "Two edges which share d-1 vertices" is read as "their intersection has exactly
      d-1 points", which for d-uniform edges is the same as sharing at least d-1 points without
      being equal. *)
Definition a_generalization_of_vizings_theorem_statement : Prop :=
  forall (H : hypergraph) (d r : nat),
    1 <= d -> uniform_hg H d -> simple_hg H -> hg_codegree_le H d r ->
    exists c : he H -> 'I_(r + d - 1),
      forall e e' : he H,
        e != e' -> #|hinc e :&: hinc e'| = d.-1 -> c e != c e'.

(** ============================================================================
    Row 6 — Universal Steiner triple systems — OPEN PROBLEM.
    "Which Steiner triple systems are universal?"  An STS S is universal iff
    every (loopless) cubic graph is S-edge-colourable: edges are coloured by
    points of S so that the three edges at every vertex form a block (triple) of
    S.  We state the associated open proposition — the EXISTENCE of a universal
    STS — the property [is_universal_sts] being the object the classification
    problem asks to characterize.
    ========================================================================== *)

Record sts := STS { sts_pt : finType; sts_blk : {set {set sts_pt}} }.

(** Validity: every block is a triple, and every pair of points lies in a unique
    block. *)
Definition sts_valid (S : sts) : Prop :=
  (forall B : {set sts_pt S}, B \in sts_blk S -> #|B| = 3) /\
  (forall p q : sts_pt S, p != q ->
     exists B : {set sts_pt S},
       [/\ B \in sts_blk S, p \in B, q \in B
         & forall B' : {set sts_pt S},
             B' \in sts_blk S -> p \in B' -> q \in B' -> B' = B]).

(** [G] is S-edge-colourable: a point-colouring of edges whose three values at
    every vertex form a block (forces distinctness, hence properness, on cubic
    G). *)
Definition sts_edge_colourable (G : mgraph) (S : sts) : Prop :=
  exists c : edge G -> sts_pt S,
    forall v : G, [set c e | e in edges_at v] \in sts_blk S.

Definition is_universal_sts (S : sts) : Prop :=
  forall G : mgraph, loopless G -> cubic G -> sts_edge_colourable G S.

(** Corpus row: opg:universal_steiner_triple_systems
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/universal_steiner_triple_systems/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/universal_steiner_triple_systems.json
    English statement: (Open Problem Garden, "Universal Steiner triple systems")
      There exists a Steiner triple system S, that is a finite point set with a family of blocks of
      size three such that every pair of distinct points lies in exactly one block, which is
      universal: every loopless cubic multigraph admits a colouring of its edges by points of S such
      that at every vertex the three colours of the incident edges form a block of S.
    Definitions: [sts] - a record with a finite point type and a set of blocks (this file);
      [sts_valid S] - every block has exactly 3 points and every pair of distinct points lies in a
      unique block (this file); [sts_edge_colourable G S] - there is a map from edges to points
      whose image on the edges at each vertex is a block (this file); [is_universal_sts S] - every
      loopless cubic multigraph is S-edge-colourable (this file); [cubic] (this file).
    Notes: The corpus row is the classification PROBLEM "Which Steiner triple systems are
      universal?". The Rocq body states only the associated existence proposition, that SOME valid
      Steiner triple system is universal; it is therefore weaker than a classification and does not
      answer the problem, it only formalises the property [is_universal_sts] the problem asks to
      characterise. Requiring the three colours at a vertex to form a block forces them to be
      distinct, hence the colouring is proper on cubic graphs. *)
Definition universal_steiner_triple_systems_statement : Prop :=
  exists S : sts, sts_valid S /\ is_universal_sts S.

(** ============================================================================
    Row 7 — Acyclic edge colouring — OPEN.
    "Every simple graph with maximum degree Δ has a proper (Δ+2)-edge-colouring
    so that every cycle contains edges of at least three distinct colours."
    Cycle = vertex [ucycle]; the cycle's edge colours are read off consecutive
    pairs.
    ========================================================================== *)

Definition edge_colour_seq (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    (s : seq G) : seq 'I_k :=
  [seq col p.1 p.2 | p <- zip s (rot 1 s)].

Definition acyclic_edge_colouring (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    : Prop :=
  [/\ (forall x y : G, col x y = col y x),
      (forall x y z : G, y != z -> x -- y -> x -- z -> col x y != col x z)
    & forall s : seq G, ucycleb (--) s -> 2 < size s ->
        2 < size (undup (edge_colour_seq col s))].

(** Corpus row: opg:acyclic_edge_coloring
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/acyclic_edge_coloring/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/acyclic_edge_coloring.json
    English statement: (Fiamcik 1978, Alon, Sudakov and Zaks 2001; Open Problem Garden, "Acyclic edge-colouring")
      Every finite simple graph G has an edge colouring with Delta(G) + 2 colours that is proper,
      meaning two edges sharing a vertex get different colours, and acyclic, meaning every cycle of
      G carries at least three distinct edge colours.
    Definitions: [acyclic_edge_colouring col] - col is symmetric, gives different colours to two
      edges at a common vertex with distinct other ends, and every [ucycle] of size greater than 2
      carries more than two distinct colours (this file); [edge_colour_seq col s] - the list of
      colours of the consecutive pairs of the closed walk s, read off [zip s (rot 1 s)] (this file);
      [Delta] (GTBase base/theories/base.v).
    Notes: Edges are modelled as a symmetric colouring function on vertex pairs, faithful for
      simple graphs. The size guard 2 < size s drops the empty and single-edge [ucycle] artefacts.
      No degree guard is needed since the palette ['I_(Delta G + 2)] is always inhabited. *)
Definition acyclic_edge_coloring_statement : Prop :=
  forall G : sgraph,
    exists col : G -> G -> 'I_(Delta G + 2), acyclic_edge_colouring col.

(** ============================================================================
    Row 8 — Star chromatic index of (sub)cubic graphs — OPEN QUESTION.
    "χ_s'(G) = min colours for a proper edge colouring with no bicoloured path or
    cycle of length four.  Is χ_s'(G) ≤ 6 for every (sub)cubic graph G?"
    Length four = four edges (P5 / C4); proper colouring already forbids equal
    consecutive colours, so bicoloured ⇔ the two ends repeat the first two
    colours.
    ========================================================================== *)

Definition star_edge_colouring (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    : Prop :=
  [/\ (forall x y : G, col x y = col y x),
      (forall x y z : G, y != z -> x -- y -> x -- z -> col x y != col x z),
      (forall x0 x1 x2 x3 x4 : G,
          x0 -- x1 -> x1 -- x2 -> x2 -- x3 -> x3 -- x4 ->
          uniq [:: x0; x1; x2; x3; x4] ->
          ~ (col x0 x1 = col x2 x3 /\ col x1 x2 = col x3 x4))
    & (forall x0 x1 x2 x3 : G,
          x0 -- x1 -> x1 -- x2 -> x2 -- x3 -> x3 -- x0 ->
          uniq [:: x0; x1; x2; x3] ->
          ~ (col x0 x1 = col x2 x3 /\ col x1 x2 = col x3 x0))].

(** Corpus row: opg:star_chromatic_index_of_cubic_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/star_chromatic_index_of_cubic_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/star_chromatic_index_of_cubic_graphs.json
    English statement: (Dvorak, Mohar and Samal 2013; Open Problem Garden, "Star chromatic index of cubic graphs")
      Every finite simple graph with maximum degree at most 3 has a proper edge colouring with 6
      colours in which no path with four edges and no cycle with four edges is bicoloured;
      equivalently the star chromatic index of every subcubic graph is at most 6.
    Definitions: [star_edge_colouring G k col] - col is symmetric, proper at every vertex, and for
      every path on five distinct vertices the colours of the first and third edges differ or the
      colours of the second and fourth edges differ, with the same condition for every cycle on four
      distinct vertices (this file); [Delta] (GTBase base/theories/base.v).
    Notes: The corpus row is the QUESTION "Is it true that for every (sub)cubic graph the star
      chromatic index is at most 6?"; the Rocq body is its affirmative reading. "Length four" is
      read as four EDGES, so the forbidden bicoloured configurations are a P5 and a C4; properness
      already forbids equal consecutive colours, so being bicoloured amounts to the two stated
      colour repetitions. Subcubic is encoded as Delta <= 3, which also covers the cubic case of the
      title. *)
Definition star_chromatic_index_of_cubic_graphs_statement : Prop :=
  forall G : sgraph, Delta G <= 3 ->
    exists col : G -> G -> 'I_6, star_edge_colouring col.

(** Corpus row: opg:behzads_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/behzads_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/behzads_conjecture.json
    English statement: (Behzad 1965 and Vizing 1964; Open Problem Garden, "Total Colouring Conjecture")
      For every multigraph G that is simple, i.e. loopless and without parallel edges, and has at
      least one vertex, the total chromatic number of G is at least Delta(G) + 1 and at most
      Delta(G) + 2, which is the source's "the total chromatic number equals Delta + 1 or Delta + 2".
    Definitions: [msimple G] - G is loopless and the endpoint-pair map on edges is injective, so G
      has no parallel edges (this file); [edge_ends e] - the set of endpoints of e (this file);
      [total_chromatic_number G] - chi of the total graph of G (GTBase base/theories/base.v);
      [mDelta G] - multigraph maximum degree (base.v).
    Notes: Carrier choice is load-bearing: Behzad's conjecture is about SIMPLE graphs, and over
      multigraphs the Delta + 2 upper bound is false, as the triangle with p parallel edges per pair
      is loopless with Delta = 2p but has total chromatic number at least chi' = 3p > 2p + 2 for p
      >= 3. The guard [msimple G] restricts the statement to exactly the open conjecture while
      reusing the multigraph total-colouring machinery of base. The disjunction "Delta+1 or Delta+2"
      is stated as the equivalent two-sided bound.
      GUARD REPAIR (2026-09-24, wave E2b): the unguarded body was axiom-free refutable on the empty
      multigraph (the empty multigraph is simple with mDelta = 0 and total chromatic number 0, so
      the lower bound 1 <= 0 fails); the guard [0 < #|G|] excludes only the empty graph, where
      Behzad's lower bound Delta + 1 <= chi'' is meaningless. *)
Definition behzads_statement : Prop :=
  forall G : mgraph, msimple G -> (0 < #|G|)%N ->
    (mDelta G).+1 <= total_chromatic_number G <= (mDelta G).+2.
