(** * Chromatic.conjectures.X218 -- chi-boundedness, multibounding and clustered-colouring rows (wave X218, 2026-09-23) *)

From GTBase Require Export base.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U8 X130 X194.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x218 vocabulary ***********************************************

    Reused instead of re-encoded: [poly_chi_bounded] (Chromatic.foundations
    chi_bounding.v, the shared "polynomially chi-bounded" wrapper of this wave),
    [has_induced] (U8.v), [has_subgraph] (GTBase common.v), [x130_frac_chi_le]
    (X130.v), [x194_treedepth_at_most] (X194.v), [clustered_colouring] (GTBase
    surface.v), [k_degenerate] / [is_forest] / [is_tree] / [connected] (GTBase and
    coq-graph-theory). *)

(** A run of vertices in which no two NON-CONSECUTIVE entries are adjacent.
    Together with [path (--)] and [uniq] this is exactly "induced path"; [x0] is
    the [nth] default, always instantiated with a vertex of the run itself. *)
Definition x218_induced_run (G : sgraph) (x0 : G) (s : seq G) : Prop :=
  forall i j : nat, j < size s -> i.+1 < j -> ~~ (nth x0 s i -- nth x0 s j).

(** A PATH-INDUCED COPY of the rooted tree [(T,r)] in [G]: an isomorphism from
    [T] onto a (not necessarily induced) subgraph of [G] -- an injective,
    edge-preserving map -- such that the image of every path of [T] with one end
    [r] is an INDUCED path of [G]. *)
Definition x218_path_induced_copy (T : sgraph) (r : T) (G : sgraph) : Prop :=
  exists phi : T -> G,
    [/\ injective phi,
        (forall x y : T, x -- y -> phi x -- phi y) &
        (forall p : seq T, path (--) r p -> uniq (r :: p) ->
           x218_induced_run (phi r) (map phi (r :: p)))].

(** The complete [d]-partite graph [K_d(t)] with all [d] parts of size [t]:
    vertices are pairs (part, index), adjacent exactly when the parts differ. *)
Definition x218_multipartite_rel (d t : nat) : rel ('I_d * 'I_t) :=
  fun x y => x.1 != y.1.
Lemma x218_multipartite_sym d t : symmetric (@x218_multipartite_rel d t).
Proof. by move=> x y; rewrite /x218_multipartite_rel eq_sym. Qed.
Lemma x218_multipartite_irrefl d t : irreflexive (@x218_multipartite_rel d t).
Proof. by move=> x; rewrite /x218_multipartite_rel eqxx. Qed.
Definition x218_complete_multipartite (d t : nat) : sgraph :=
  SGraph (@x218_multipartite_sym d t) (@x218_multipartite_irrefl d t).

(** [H] is MULTIBOUNDING: two coefficient FUNCTIONS [c] and [e] of the
    parameter [d] -- an explicit bounding function, given in the polynomial
    normal form -- such that for every [d >= 1] the polynomial [c d * t ^ e d]
    bounds the chromatic number of every [H]-free graph containing no [K_d(t)]
    SUBGRAPH, uniformly in [t >= 1].  This is the SKOLEMISED form of "for every
    [d >= 1] there is a polynomial": see the RE-ENCODING note of
    [every_forest_is_multibounding_statement]. *)
Definition x218_multibounding (H : sgraph) : Prop :=
  exists c e : nat -> nat,
    forall d : nat, 1 <= d ->
      forall (t : nat) (G : sgraph),
        1 <= t ->
        ~ has_induced H G ->
        ~ has_subgraph G (x218_complete_multipartite d t) ->
        χ([set: G]) <= c d * t ^ e d.

(** An ODD MINOR model of [H] in [G]: branch sets that are nonempty, connected
    and pairwise disjoint, together with a 2-colouring of [G] making every edge
    INSIDE a branch set bichromatic and providing, for every edge of [H], a
    MONOCHROMATIC edge between the two branch sets. *)
Definition x218_odd_minor (G H : sgraph) : Prop :=
  exists (B : H -> {set G}) (sigma : G -> bool),
    [/\ forall x : H, B x != set0,
        forall x : H, connected (B x),
        forall x y : H, x != y -> [disjoint B x & B y],
        forall (x : H) (u v : G), u \in B x -> v \in B x -> u -- v -> sigma u != sigma v &
        forall x y : H, x -- y ->
          exists u v : G, [/\ u \in B x, v \in B y, u -- v & sigma u == sigma v]].

(** CONNECTED tree-depth at most [k]: some CONNECTED graph containing [H] as a
    subgraph has tree-depth at most [k]. *)
Definition x218_connected_treedepth_at_most (H : sgraph) (k : nat) : Prop :=
  exists H' : sgraph,
    [/\ connected [set: H'], has_subgraph H' H & x194_treedepth_at_most H' k].

(** The DEFECTIVE chromatic number of a class is at most [k]: one defect bound
    [m], chosen before the graphs, such that every graph of the class has a
    [k]-colouring in which every vertex has at most [m] neighbours of its own
    colour. *)
Definition x218_defective_chromatic_class_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists m : nat,
    forall G : sgraph, F G ->
      exists col : G -> 'I_k,
        forall v : G, #|N(v) :&: [set u : G | col u == col v]| <= m.

(** The CLUSTERED chromatic number of a class is at most [k]: one clustering
    bound [c], chosen before the graphs. *)
Definition x218_clustered_chromatic_class_le (F : sgraph -> Prop) (k : nat) : Prop :=
  exists c : nat, forall G : sgraph, F G -> clustered_colouring G k c.

(** ** X218 statements *****************************************************)

(** Corpus row: arxiv:2202.10412#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.10412__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.10412__00.json
    English statement: (Chudnovsky, Scott, Seymour and Spirkl 2022, informal conjecture "every forest is good", arXiv:2202.10412)
      For every finite simple graph H that is a forest there are naturals c and d such that every
      graph with no induced subgraph isomorphic to H has chromatic number at most c times the d-th
      power of its clique number.
    Definitions: [poly_chi_bounded F] - naturals c and d, chosen before the graphs of the class,
      with chi(G) <= c * omega(G)^d for every G in the class (Chromatic.foundations
      chi_bounding.v); [has_induced H G] - some vertex set of G induces a copy of H (U8.v);
      [is_forest [set: H]] (coq-graph-theory sgraph.v via GTBase).
    Notes: "H is good" is the source's name for "the class of H-free graphs is polynomially
      chi-bounded"; the polynomial is taken in the normal form c * t^d, which is no loss over the
      naturals since a polynomial with natural coefficients of degree d is dominated by (sum of its
      coefficients) * t^d for t >= 1, and the t = 0 case is covered by 0^0 = 1. The bounding data
      depend on H only, not on the graph. This row states, for a different paper, the same
      mathematical conjecture as arxiv:2202.05557#00 in X65.v, which is encoded there with an
      arbitrary polynomial given by its coefficient list; the two readings are equivalent.
      Corpus status: partial (the case H = P5 was settled in 2025). *)
Definition every_forest_is_good_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    poly_chi_bounded (fun G : sgraph => ~ has_induced H G).

(** Corpus row: arxiv:2302.08922#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2302.08922__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2302.08922__00.json
    English statement: (Nguyen, Scott and Seymour 2023, open question after 1.2, arXiv:2302.08922)
      For every finite simple graph T that is a tree and every choice of a root vertex r of T there
      are naturals c and d such that every graph with no path-induced copy of the rooted tree (T,r)
      has chromatic number at most c times the d-th power of its clique number.
    Definitions: [x218_path_induced_copy r G] - an injective edge-preserving map from T to G such
      that the image of every path of T with one end r is an induced path of G (this file);
      [x218_induced_run x0 s] - no two non-consecutive entries of the run s are adjacent (this
      file); [poly_chi_bounded F] (Chromatic.foundations chi_bounding.v); [is_tree [set: T]]
      (coq-graph-theory sgraph.v via GTBase).
    Notes: The source asks the question in prose ("is there any hope for a comparable
      strengthening of 1.2 ... ?"); the Rocq body is the affirmative proposition. The paper's 1.2
      gives a bound depending on the clique number t; "polynomial in t" is taken in the normal
      form c * t^d, and quantifying "for every t, if omega(G) <= t then chi(G) <= c*t^d" is
      equivalent to the body's instance at t = omega(G) because the bound is monotone in t. The
      root r is part of the data: a path-induced copy is defined for a ROOTED tree. Corpus status:
      open. *)
Definition path_induced_rooted_tree_polynomial_chi_bound_statement : Prop :=
  forall (T : sgraph) (r : T),
    is_tree [set: T] ->
    poly_chi_bounded (fun G : sgraph => ~ x218_path_induced_copy r G).

(** Corpus row: arxiv:2302.08922#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2302.08922__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2302.08922__01.json
    English statement: (Nguyen, Scott and Seymour 2023, polynomial Gyarfas-Sumner, arXiv:2302.08922)
      For every finite simple graph T that is a tree there are naturals c and d such that every
      graph with no induced subgraph isomorphic to T has chromatic number at most c times the d-th
      power of its clique number.
    Definitions: [poly_chi_bounded F] (Chromatic.foundations chi_bounding.v); [has_induced T G]
      (U8.v); [is_tree [set: T]] (coq-graph-theory sgraph.v via GTBase).
    Notes: This is the Gyarfas-Sumner conjecture (U8.v's
      [graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement]) with the bounding function
      required to be polynomial in the clique number, in the normal form c * t^d. It is the
      restriction to TREES of the forest statement of arxiv:2202.05557#00 (X65.v) and of
      arxiv:2202.10412#00 above. Corpus status: partial (known for trees with no induced P5 and,
      since 2025, for P5 itself, and for bounded-boxicity classes). *)
Definition polynomial_gyarfas_sumner_tree_statement : Prop :=
  forall T : sgraph,
    is_tree [set: T] ->
    poly_chi_bounded (fun G : sgraph => ~ has_induced T G).

(** Corpus row: arxiv:2303.11766#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2303.11766__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2303.11766__00.json
    English statement: (Nguyen, Scott and Seymour 2023, Conjecture 1.6, arXiv:2303.11766)
      Every finite simple graph H that is a forest is multibounding: there are two functions c and
      e from naturals to naturals such that, for every d at least one, every t at least one and
      every graph with no induced subgraph isomorphic to H and with no subgraph isomorphic to the
      complete d-partite graph with all parts of size t, the chromatic number of that graph is at
      most c of d times the (e of d)-th power of t.
    Definitions: [x218_multibounding H] - the displayed property of H (this file);
      [x218_complete_multipartite d t] - the graph on pairs (part, index) in which two vertices are
      adjacent exactly when their parts differ, i.e. K_d(t) (this file); [has_subgraph G H] - G
      contains H as a not necessarily induced subgraph (GTBase common.v); [has_induced H G]
      (U8.v); [is_forest [set: H]] (coq-graph-theory sgraph.v via GTBase).
    Notes: K_d(t) is excluded as a SUBGRAPH, not as an induced subgraph, as in the source. The
      polynomial f(t) of the source is put in the normal form c * t^e, and its two coefficients are
      given as FUNCTIONS of d, so that the whole bounding datum c, e is chosen before d, t and G:
      the Skolemised reading of the source's "for every d >= 1 there is a polynomial f such that
      for all t >= 1 ...". The guards d >= 1 and t >= 1 are the source's; the bounding data depend
      on H and d only, never on the graph.
      RE-ENCODING (2026-09-24): explicit bounding function; the earlier forall-d-exists-c form
      needed countable choice to yield the function used by e035; equivalent classically, strictly
      stronger constructively. [grounding_X218.v] proves the new form implies the old one
      ([x218_multibounding_pointwise]) and exhibits a witness, and the re-encoded body is what
      makes the corpus edge e035 to U8's Gyarfas-Sumner statement machine-checkable
      ([implications_X218.v]).
      Corpus status: open (paths, brooms and disjoint unions of multibounding forests are
      known). *)
Definition every_forest_is_multibounding_statement : Prop :=
  forall H : sgraph,
    is_forest [set: H] ->
    x218_multibounding H.

(** Corpus row: arxiv:2308.15721#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2308.15721__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2308.15721__00.json
    English statement: (Hickingbotham, Kang, Oum, Steiner and Wood 2023, Conjecture 2, arXiv:2308.15721)
      For every finite simple graph H whose connected tree-depth is exactly k, the class of graphs
      having no odd H-minor has defective chromatic number at most k - 1 and clustered chromatic
      number at most k - 1.
    Definitions: [x218_odd_minor G H] - a minor model of H in G together with a 2-colouring of G
      making every edge inside a branch set bichromatic and giving, for every edge of H, a
      monochromatic edge between the corresponding branch sets (this file);
      [x218_connected_treedepth_at_most H k] - some connected graph containing H as a subgraph has
      tree-depth at most k (this file); [x194_treedepth_at_most] (X194.v);
      [x218_defective_chromatic_class_le F k] - one defect bound m, chosen before the graphs, with
      a k-colouring of every graph of the class in which each vertex has at most m neighbours of
      its own colour (this file); [x218_clustered_chromatic_class_le F k] - one clustering bound c,
      chosen before the graphs (this file); [clustered_colouring] (GTBase surface.v);
      [has_subgraph] (GTBase common.v).
    Notes: BLOCKED. Two primitives of the source could not be verified against the paper from the
      corpus text available here, so the body is a PLACEHOLDER encoding the best available reading
      and the row's statement leg stays blocked. (1) The odd-minor model above is the standard one
      from the literature, but the paper's own normalisation (whether the bipartition is required
      on all of G or only on the union of the branch sets, and whether the branch sets must induce
      connected BIPARTITE subgraphs) is not recorded in the row. (2) td-bar(H), the "connected
      tree-depth", is encoded as the least tree-depth of a connected graph containing H as a
      subgraph; the corpus text does not fix whether new vertices are allowed, whether the
      containment is as a subgraph or as a spanning subgraph, and which tree-depth convention
      (rooted-forest height counted in vertices, as in X194.v) the paper uses, and the conjectured
      value k - 1 is off by one under the alternative conventions. The class parameters ARE
      quantified class-uniformly, the collapse found by the 2026-07-17 audit in X138/X194. What is
      reliable in this body: the two class parameters, the equality with a single bound k - 1, and
      the domain "graphs with no odd H-minor". Corpus status: open; the paper proves the chain
      td-bar(H)-1 <= defective <= clustered <= 3*2^(td-bar(H)) - 4. The second-reader readback of
      2026-09-23 CONFIRMED and sharpened both blockers by reading the paper: td-bar(G) is defined
      there as the minimum vertex-height of a rooted tree T with V(T) = V(G) such that G is a
      subgraph of the closure of T -- the same vertex set, no new vertices -- so the placeholder's
      "some connected graph containing H as a subgraph" reading is indeed not the paper's; and the
      current arXiv version states Conjecture 2 as "chi_star <= 2*td-bar(H) - 2 AND chi_Delta =
      td-bar(H) - 1", not as the single equality the corpus statement_text records, so the corpus
      row itself should be re-checked against the paper version before the row is re-authored. *)
Definition odd_minor_free_defective_clustered_treedepth_statement : Prop :=
  forall (H : sgraph) (k : nat),
    1 <= k ->
    x218_connected_treedepth_at_most H k ->
    ~ x218_connected_treedepth_at_most H k.-1 ->
    x218_defective_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1) /\
    x218_clustered_chromatic_class_le (fun G : sgraph => ~ x218_odd_minor G H) (k - 1).

(** Corpus row: arxiv:2601.15245#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2601.15245__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2601.15245__04.json
    English statement: (Bradac, Fox, Steiner, Sudakov and Zhang, Problem 6.4, arXiv:2601.15245)
      For every r at least four and every positive q there is a threshold d0 such that, for every
      d at least d0, every finite simple graph with clique number less than r that is d-degenerate
      has fractional chromatic number at most d/q.
    Definitions: [x130_frac_chi_le G p q] - some (a:b)-fold colouring of G satisfies a*q <= p*b,
      the cross-multiplied form of "the fractional chromatic number is at most p/q" (X130.v);
      [x130_bfold_colouring] (X130.v); [k_degenerate G d] - every nonempty vertex set has a vertex
      with at most d neighbours inside it (GTBase base.v); [omega(A)] (coq-graph-theory
      coloring.v via GTBase).
    Notes: The source asks whether the maximum fractional chromatic number of K_r-free
      d-degenerate graphs is o_r(d). "o(d)" is unfolded over the rationals: for every positive
      integer q, standing for the real epsilon = 1/q, the bound epsilon*d = d/q holds for all
      large enough d, with the threshold d0 allowed to depend on r and q. "K_r-free" is taken as
      "no clique on r vertices", i.e. omega(G) < r; for a complete graph K_r this is the same as
      excluding K_r as a subgraph. The fractional chromatic number is rational and attained on a
      finite graph, so the (a:b)-fold form of X130 is faithful. The guard r >= 4 is the source's;
      for r <= 3 the answer is known to be negative. Corpus status: open, with the source's own
      lower bound of order d / log^(r-2) d. *)
Definition kr_free_degenerate_fractional_chromatic_sublinear_statement : Prop :=
  forall r : nat, 4 <= r ->
    forall q : nat, 0 < q ->
      exists d0 : nat,
        forall (d : nat) (G : sgraph),
          d0 <= d ->
          ω([set: G]) < r ->
          k_degenerate G d ->
          x130_frac_chi_le G d q.
