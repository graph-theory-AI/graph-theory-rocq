(** * Chromatic.conjectures.X213 -- Bondy-Murty Appendix A colouring rows (wave X213, 2026-09-23) *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import U8 X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x213 vocabulary ***********************************************

    Only notions absent from coq-graph-theory and from GTBase are introduced.
    Reused from elsewhere: [χ(A)] / [ω(A)] / [clique] / [is_tree] /
    [triangle_free] (GTBase base.v and coq-graph-theory), [surface_embeddable]
    (GTBase surface.v), [has_induced] (U8.v), [x3_anticomplete] (X3.v). *)

(** A proper edge colouring of a SIMPLE graph by [k] colours, presented as a
    symmetric colour of ordered pairs: [col u v] is the colour of the edge [uv],
    and two distinct edges sharing the endpoint [u] get distinct colours.  Only
    the values on adjacent pairs are constrained, so a colouring is exactly a
    proper vertex colouring of the line graph of [G]. *)
Definition x213_proper_edge_colouring
    (G : sgraph) (k : nat) (col : G -> G -> 'I_k) : Prop :=
  (forall u v : G, col u v = col v u) /\
  (forall u v w : G, u -- v -> u -- w -> v != w -> col u v != col u w).

(** [G] is [k]-edge-colourable. *)
Definition x213_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> G -> 'I_k, x213_proper_edge_colouring col.

(** The set of colours actually used by [col] on the edges of [G]. *)
Definition x213_used_colours (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    : {set 'I_k} :=
  [set c : 'I_k | [exists u : G, [exists v : G, (u -- v) && (col u v == c)]]].

(** A KEMPE CHANGE: [col'] is obtained from [col] by choosing two colours [a],
    [b] and a set [K] of ordered pairs which is symmetric, contains only edges
    coloured [a] or [b], and is CLOSED for line-adjacency inside that two-coloured
    subgraph (no edge of [K] shares an endpoint with an [a]- or [b]-coloured edge
    outside [K]); on [K] the two colours are interchanged and elsewhere nothing
    moves.  A closed set is exactly a union of connected components of the
    [{a,b}]-coloured subgraph, i.e. of alternating paths and cycles, and a union
    of components is the composition of the single-component interchanges, so
    reachability by these steps is the same relation as reachability by the
    source's one-component-at-a-time Kempe changes. *)
Definition x213_kempe_step
    (G : sgraph) (k : nat) (col col' : G -> G -> 'I_k) : Prop :=
  exists (a b : 'I_k) (K : {set G * G}),
    [/\ forall u v : G, ((u, v) \in K) = ((v, u) \in K),
        forall u v : G, (u, v) \in K -> u -- v /\ (col u v == a) || (col u v == b),
        forall u v w : G, (u, v) \in K -> u -- w ->
          (col u w == a) || (col u w == b) -> (u, w) \in K &
        forall u v : G,
          col' u v = if (u, v) \in K
                     then (if col u v == a then b else a)
                     else col u v].

(** Reachability in at most [n] Kempe changes. *)
Fixpoint x213_kempe_reach (G : sgraph) (k n : nat) (col col' : G -> G -> 'I_k)
    {struct n} : Prop :=
  match n with
  | 0 => col = col'
  | n'.+1 =>
      col = col' \/
      exists c : G -> G -> 'I_k, x213_kempe_step col c /\ x213_kempe_reach n' c col'
  end.

(** ** X213 statements *****************************************************)

(** Corpus row: bm:bm-045
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-045/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-045.json
    English statement: (Lovasz 1968, Erdos-Lovasz Tihany conjecture, Bondy-Murty Appendix A item 45)
      Let G be a finite simple graph whose chromatic number is k and which has no clique on k
      vertices, and let k + 1 = k1 + k2 with k1 and k2 both at least two. Then G has two disjoint
      vertex sets A and B such that the subgraph induced on A has chromatic number exactly k1 and
      the subgraph induced on B has chromatic number exactly k2.
    Definitions: [χ(A)] - the chromatic number of the subgraph of G induced on the vertex set A
      (coq-graph-theory coloring.v via GTBase); [clique S] - S is pairwise adjacent
      (coq-graph-theory sgraph.v).
    Notes: "G has no k-clique" is spelled out as: every clique of G has fewer than k vertices.
      The source says "vertex-disjoint subgraphs G1, G2 with Gi k_i-chromatic"; the Rocq body asks
      for INDUCED subgraphs, which is equivalent: an induced subgraph has chromatic number at least
      that of any subgraph on the same vertices, and deleting vertices lowers the chromatic number
      by at most one at a time, so an induced subgraph with chromatic number exactly k_i can be
      carved out of any subgraph with chromatic number k_i, and conversely. Corpus status: partial
      (Stiebitz proved k1 = 2; claw-free, line-graph and even-hole-free cases are known). *)
Definition erdos_lovasz_tihany_statement : Prop :=
  forall (G : sgraph) (k k1 k2 : nat),
    χ([set: G]) = k ->
    (forall S : {set G}, clique S -> #|S| < k) ->
    k + 1 = k1 + k2 -> 2 <= k1 -> 2 <= k2 ->
    exists A B : {set G},
      [/\ [disjoint A & B], χ(A) = k1 & χ(B) = k2].

(** Corpus row: bm:bm-046
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-046/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-046.json
    English statement: (El-Zahar and Erdos 1985, Bondy-Murty Appendix A item 46)
      There is a function f of two natural arguments such that every finite simple graph G whose
      chromatic number is at least f(r,k) either has a clique on r vertices, or has two disjoint
      vertex sets A and B with no edge between them such that the subgraphs induced on A and on B
      both have chromatic number exactly k.
    Definitions: [x3_anticomplete A B] - A and B are disjoint and no edge joins A to B, so the
      subgraph induced on the union is the disjoint union of the two induced subgraphs (X3.v);
      [χ(A)] - chromatic number of the subgraph induced on A (coq-graph-theory coloring.v);
      [clique S] (coq-graph-theory sgraph.v).
    Notes: "an induced subgraph which is the disjoint union of two k-chromatic graphs" is encoded
      as an ANTICOMPLETE pair of vertex sets, each of chromatic number exactly k; the induced
      subgraph on their union is then exactly that disjoint union. The bounding function f is
      quantified before r, k and G, which is the reading of "does there exist a function f such
      that every graph of chromatic number at least f(r,k) ...". Corpus status: partial
      (Nguyen-Scott-Seymour 2023 prove a weaker variant with minimum degree on one side). *)
Definition el_zahar_erdos_statement : Prop :=
  exists f : nat -> nat -> nat,
    forall (r k : nat) (G : sgraph),
      f r k <= χ([set: G]) ->
      (exists S : {set G}, clique S /\ #|S| = r) \/
      (exists A B : {set G}, [/\ x3_anticomplete A B, χ(A) = k & χ(B) = k]).

(** Corpus row: bm:bm-050
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-050/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-050.json
    English statement: (Gyarfas, Bondy-Murty Appendix A item 50)
      For every finite tree T there is a bound c such that every triangle-free finite simple graph
      with no induced subgraph isomorphic to T has chromatic number at most c.
    Definitions: [has_induced T G] - some vertex set of G induces a copy of T (U8.v);
      [triangle_free] (GTBase base.v); [is_tree [set: T]] - T is a connected forest
      (coq-graph-theory sgraph.v via GTBase).
    Notes: The source states the conjecture over possibly INFINITE graphs: "every triangle-free
      graph of infinite chromatic number contains every finite tree as an induced subgraph". The
      Rocq body is its finite equivalent, which is the form the source's own context argues from
      ("if T-free graphs are chi-bounded, a triangle-free T-free graph has bounded chromatic
      number"). The two are equivalent: from the finite form, every finite induced subgraph of a
      triangle-free T-induced-free graph has chromatic number at most c, so by De Bruijn-Erdos the
      whole graph does and cannot have infinite chromatic number; conversely, if the finite form
      failed for T, the disjoint union of finite triangle-free T-induced-free graphs of unbounded
      chromatic number would be a triangle-free T-induced-free graph of infinite chromatic number.
      Corpus status: partial; the statement follows from the open Gyarfas-Sumner conjecture. *)
Definition triangle_free_induced_tree_chi_bounded_statement : Prop :=
  forall T : sgraph,
    is_tree [set: T] ->
    exists c : nat,
      forall G : sgraph,
        triangle_free G -> ~ has_induced T G -> χ([set: G]) <= c.

(** Corpus row: bm:bm-053
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-053/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-053.json
    English statement: (Albertson, Bondy-Murty Appendix A item 53)
      Every finite simple graph that embeds in the torus -- that is, every connected graph of
      orientable genus at most one -- has a set of at most three vertices whose deletion leaves a
      graph with chromatic number at most four.
    Definitions: [surface_embeddable 1 G] - G has a rotation system of ORIENTABLE genus at most
      one, i.e. it embeds in the torus (GTBase surface.v: [surface_euler_genus] halves
      2 + E - V - F, so its value is the orientable genus and the torus is the index one);
      [connected [set: G]] - G is connected (coq-graph-theory sgraph.v), the guard
      base/theories/surface.v asks the consumers of its Euler count to keep; [χ(A)] - chromatic
      number of the subgraph induced on A (coq-graph-theory coloring.v via GTBase).
    Notes: FIX 2026-09-23 of the defect the second-reader readback blocked the row on. The
      hypothesis used to be [surface_embeddable 2 G] alone, which is wrong twice over.
      (1) [surface_euler_genus] divides (2 + E - V - F) by two, so its value is the ORIENTABLE
      GENUS -- the torus gives 1, not 2 -- as meta/STATEMENT_IMPROVEMENTS.md already records for
      X164/X210; [surface_embeddable 2 G] therefore read "G embeds in the genus-two orientable
      surface", a strictly larger class than "toroidal", on which the body is FALSE: K_8 has
      orientable genus two, and deleting any three of its vertices leaves K_5, of chromatic
      number five. (2) [surface_euler_genus] applies one Euler-characteristic formula to the
      whole graph with no connectivity guard -- the guard base/theories/surface.v itself asks
      consumers to keep -- so a disjoint union whose component genera cancel against the
      component count, three disjoint copies of K_6 for instance, satisfied the hypothesis
      without being toroidal. The hypothesis is now [surface_embeddable 1 G] together with
      [connected [set: G]], and grounding_X213.v records both halves: the guard is satisfiable
      ([x213_toroidal_guard_K1]) and it has teeth ([x213_connected_guard_has_teeth]: the
      two-vertex edgeless graph passes the unguarded Euler count and is excluded by
      connectivity). Everything else is unchanged: the rotation-system predicate rather than
      planarity, and "three vertices whose deletion leaves a 4-colourable graph" as a set of AT
      MOST three vertices. Corpus status: open; three deletions are necessary for an infinite
      family.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition albertson_toroidal_delete_three_statement : Prop :=
  forall G : sgraph,
    surface_embeddable 1 G ->
    connected [set: G] ->
    exists S : {set G}, #|S| <= 3 /\ χ([set: G] :\: S) <= 4.

(** Corpus row: bm:bm-057
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-057/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-057.json
    English statement: (1-factorization conjecture, Bondy-Murty Appendix A item 57)
      Every finite simple graph on a positive even number n of vertices in which every vertex has
      exactly d neighbours, with n at most 2d, has a proper edge colouring with d colours.
    Definitions: [x213_proper_edge_colouring col] - col gives every ordered pair a colour, is
      symmetric, and gives distinct colours to two distinct edges sharing an endpoint (this file);
      [x213_edge_colourable G d] - such a colouring by d colours exists (this file); [regular G d]
      - every vertex has exactly d neighbours (GTBase base.v).
    Notes: The threshold d >= n/2 is cross-multiplied to n <= 2*d over the naturals. The guard
      0 < #|G| excludes the empty graph, for which the statement is degenerate. A d-edge-colouring
      of a d-regular graph is exactly a 1-factorization, the equivalent form the source's context
      records; the Rocq body keeps the edge-colouring wording of the statement text. The sharper
      Chetwynd-Hilton threshold mentioned in the context is NOT used. Corpus status: partial
      (Csaba, Kuhn, Lo, Osthus and Treglown proved it for all sufficiently large n). *)
Definition one_factorization_conjecture_statement : Prop :=
  forall (G : sgraph) (d : nat),
    0 < #|G| ->
    ~~ odd #|G| ->
    regular G d ->
    #|G| <= 2 * d ->
    x213_edge_colourable G d.

(** Corpus row: bm:bm-060
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-060/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-060.json
    English statement: (Vizing 1965, interchange conjecture, Bondy-Murty Appendix A item 60)
      For every finite simple graph G, every proper edge colouring of G with k colours and every
      number m of colours with m at most k for which G does have some proper m-edge-colouring,
      there is a finite sequence of Kempe changes leading from the given colouring to a proper
      edge colouring that uses at most m of the k colours.
    Definitions: [x213_proper_edge_colouring col] (this file); [x213_edge_colourable G m] (this
      file); [x213_kempe_step col col'] - col' interchanges two colours on a line-adjacency-closed
      set of edges coloured with those two colours, i.e. on a union of alternating paths and cycles
      (this file); [x213_kempe_reach n col col'] - col' is reachable from col in at most n Kempe
      changes (this file); [x213_used_colours col] - the colours col gives to at least one edge
      (this file).
    Notes: The source's target, "a proper edge colouring with chi'(G) colours", is stated without
      naming chi'(G): the body asks for the conclusion at EVERY achievable number m of colours, and
      chi'(G) is by definition the least such m, so the two readings coincide while no chromatic
      index has to be defined for simple graphs. The Kempe step is taken on a line-adjacency-CLOSED
      set of two-coloured edges rather than on a single alternating component; a closed set is a
      union of components, and swapping a union of components is the composition of the
      single-component swaps, so the reachability relation is unchanged. Properness of the
      intermediate colouring is required explicitly at the end of the sequence. Corpus status:
      solved (Narboni, arXiv:2302.12914, 2023), so the row is a re-provable target, not an open
      question. *)
Definition vizing_kempe_interchange_statement : Prop :=
  forall (G : sgraph) (k m : nat) (col : G -> G -> 'I_k),
    x213_proper_edge_colouring col ->
    m <= k ->
    x213_edge_colourable G m ->
    exists (n : nat) (col' : G -> G -> 'I_k),
      [/\ x213_kempe_reach n col col',
          x213_proper_edge_colouring col' &
          #|x213_used_colours col'| <= m].
