(** * Cycle.conjectures.U10 — milestone U10 (namespace Cycle, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of three central OPEN conjectures on perfect matchings of
    bridgeless cubic graphs:

      - Row 1 : the Berge–Fulkerson Conjecture
                (six perfect matchings double-covering the edges);
      - Row 2 : the Petersen Colouring Conjecture
                (an edge-colouring by the edges of the Petersen graph respecting
                 mutual adjacency of edge-triples);
      - Row 3 : the Fan–Raspaud "intersecting two perfect matchings" Conjecture
                (two perfect matchings whose intersection contains no odd
                 edge-cut).

    CARRIER.  The host graph [G] of each row is an undirected MULTIGRAPH, so its
    carrier is coq-graph-theory's [mgraph] = [graph unit unit] — exactly the
    object level of the sibling milestone [U6.v], whose cycle-theory vocabulary
    ([cubic], [bridgeless], [subdeg], [cut], [is_matching]) we REUSE verbatim by
    importing [U6].  Matchings are EDGE SETS [{set edge G}]; a perfect-matching
    cover / a list of matchings is a [seq {set edge G}].

    For Row 2 the codomain is THE Petersen graph, which we build concretely as
    the Kneser graph KG(5,2): vertices are the 2-element subsets of ['I_5],
    adjacency is disjointness ([petersen : sgraph]).  Its "edges" are the
    adjacent vertex pairs ([Pedge]); edge-adjacency in [G] reuses base's
    undirected [line_graph]/[line_rel] (mgraph edges sharing an endpoint).

    IMPORT ORDER: [mgraph] (and [sgraph]) are imported BEFORE [base], because
    coq-graph-theory's [mgraph] ships a DIRECTED [line_graph] that would
    otherwise shadow base's undirected one (which [U6] and this file use).

    CORE API used (verified on switch `digraph`, Rocq 9.1.1 + coq-graph-theory):
      - [edge G] : finType of edges; [source e]/[target e] : endpoints;
      - [subdeg H v] (U6) : degree of [v] inside edge set [H];
      - [cut S] (U6) : the edge cut of a vertex set [S];
      - [cubic]/[bridgeless] (U6) : loopless 3-regular / no bridge;
      - [SGraph] : sgraph constructor; [sedge]/[--] : adjacency;
      - base's [line_graph G : sgraph] with [sedge = line_rel] (edges of [G]
        sharing an endpoint).

    AREA primitives introduced here (cycle-theory specific):
      [is_perfect_matching], [perfect_matching_cover] (Row 1);
      [petersenV], [padj], [petersen], [Pedge], [psupp], [Padj], [mut_adj3],
      [cubic_bridgeless] (Row 2);
      [is_odd_edge_cut], [contains_odd_edge_cut] (Row 3). *)

From GraphTheory Require Import mgraph sgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared primitives *)

(** A PERFECT matching: every vertex meets EXACTLY one matching edge (sharpening
    U6's [is_matching], which only bounds the matching-degree by one). *)
Definition is_perfect_matching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, subdeg M v = 1.

(** Cubic and bridgeless together: the shared "bridgeless cubic graph" hypothesis
    used uniformly by all three rows.  [bridgeless] is the UNDIRECTED (cut-edge)
    notion of [Cycle.foundations.connectivity]. *)
Definition cubic_bridgeless (G : mgraph) : Prop := cubic G /\ bridgeless G.

(** ================================================================= *)
(** ** Row 1 — The Berge–Fulkerson Conjecture *)
(** OPEN.

    Source: "If G is a bridgeless cubic graph, then there exist 6 perfect
    matchings M_1,...,M_6 of G with the property that every edge of G is
    contained in exactly two of M_1,...,M_6." *)

(** A [k]-perfect-matching cover: a list of [k] perfect matchings covering every
    edge exactly twice (a "perfect-matching double cover" of [k] members). *)
Definition perfect_matching_cover (G : mgraph) (k : nat)
    (L : seq {set edge G}) : Prop :=
  [/\ size L = k,
      (forall M, M \in L -> is_perfect_matching M)
    & forall e : edge G, count (fun M : {set edge G} => e \in M) L = 2].

(** Corpus row: opg:the_berge_fulkerson_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_berge_fulkerson_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_berge_fulkerson_conjecture.json
    English statement: (Open Problem Garden, "The Berge-Fulkerson conjecture")
      For every multigraph G with at least one vertex that is cubic, that is, loopless with
      every vertex on exactly three edges, and bridgeless, there is a list of six perfect
      matchings of G, each a set of edges meeting every vertex exactly once, such that
      every edge of G belongs to exactly two members of the list, counted with
      multiplicity in the list.
    Definitions: [is_perfect_matching M] - every vertex has exactly one incident edge in M
      (U10.v); [perfect_matching_cover k L] - L has exactly k members, all perfect
      matchings, and every edge is counted exactly twice over L (U10.v);
      [cubic_bridgeless G] - cubic and bridgeless (U10.v); [cubic G] - loopless and every
      vertex has multigraph degree 3 (cycle-theory/theories/conjectures/U6.v);
      [subdeg M v] - the number of edges of M incident with v, [mdeg], [bridgeless]
      (cycle-theory/theories/foundations/connectivity.v); [loopless]
      (base/theories/base.v).
    Notes: the six matchings form a LIST, not a set, so repetitions are allowed, which
      matches the source's M_1, ..., M_6 with "every edge contained in exactly two of
      them", the count being taken over positions. The guard [0 < #|G|] excludes the empty
      graph.
      REPAIRED (foundation repair, 2026-09-23): [bridgeless], hence
      [cubic_bridgeless], now reads [is_bridge] through the UNDIRECTED [uwalk]
      of GTBase.base, so it is the textbook "no cut edge". Under the previous
      DIRECTED reading (coq-graph-theory's [eseparates] over [walk]) a cubic
      loopless multigraph could only be a disjoint union of triple-edge
      dipoles - no snark, no Petersen graph - so the hypothesis class was
      essentially empty of the conjecture's content; that is no longer the
      case. *)
Definition the_berge_fulkerson_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists L : seq {set edge G}, perfect_matching_cover 6 L.

(** ================================================================= *)
(** ** Row 2 — The Petersen Colouring Conjecture *)
(** OPEN.

    Source: "Let G be a cubic graph with no bridge.  Then there is a colouring of
    the edges of G using the edges of the Petersen graph so that any three
    mutually adjacent edges of G map to three mutually adjacent edges in the
    Petersen graph." *)

(** *** THE Petersen graph as the Kneser graph KG(5,2). *)

(** Vertices: the 2-element subsets of a 5-element set (exactly 10 of them). *)
Definition petersenV : finType := {x : {set 'I_5} | #|x| == 2}.

(** Adjacency: two 2-subsets are adjacent iff they are DISJOINT. *)
Definition padj (x y : petersenV) : bool := [disjoint val x & val y].

Lemma padj_sym : symmetric padj.
Proof. by move=> x y; rewrite /padj disjoint_sym. Qed.

Lemma padj_irrefl : irreflexive padj.
Proof.
move=> x; apply/negP; rewrite /padj -setI_eq0 setIid => /eqP Hx.
by move: (valP x); rewrite Hx cards0.
Qed.

Definition petersen : sgraph := SGraph padj_sym padj_irrefl.

(** *** Edges of the Petersen graph, and edge-adjacency. *)

(** A Petersen edge is an adjacent (ordered representative of an) vertex pair. *)
Definition Pedge : finType := {p : petersenV * petersenV | padj p.1 p.2}.

(** The unordered support (endpoint set) of a Petersen edge. *)
Definition psupp (q : Pedge) : {set petersenV} := [set (val q).1; (val q).2].

(** Two Petersen edges are ADJACENT iff they are distinct edges (distinct
    supports) sharing a vertex.  Using supports makes this independent of the
    chosen orientation of each representative. *)
Definition Padj (q r : Pedge) : bool :=
  (psupp q != psupp r) && (psupp q :&: psupp r != set0).

(** Three elements are pairwise related by [r] ("mutually adjacent").
    [@MOVE-to-base]: a carrier-agnostic mutual-adjacency-triple combinator over an
    arbitrary [rel T]; kept area-local for now (base exposes no equivalent —
    confirmed via Search over GTBase.base), migrate to graph-theory-base when a
    second area needs a mutual-adjacency triple. *)
Definition mut_adj3 (T : Type) (r : rel T) (a b c : T) : bool :=
  [&& r a b, r b c & r a c].

(** Corpus row: opg:petersen_coloring_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/petersen_coloring_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/petersen_coloring_conjecture.json
    English statement: (Open Problem Garden, "Petersen coloring conjecture")
      For every bridgeless cubic multigraph G with at least one vertex there is a map f
      from the edges of G to the edges of the Petersen graph such that whenever three edges
      of G are pairwise adjacent, that is, pairwise share an endpoint, their three images
      are pairwise adjacent edges of the Petersen graph, where two Petersen edges are
      adjacent when they are distinct and share a vertex.
    Definitions: [petersenV], [padj] and [petersen] - the Petersen graph built as the
      Kneser graph on the two-element subsets of a five-element set with disjointness as
      adjacency (U10.v); [Pedge] - an edge of the Petersen graph, given as an adjacent
      ordered pair of vertices, with [psupp] its unordered endpoint set (U10.v);
      [Padj q r] - the supports of q and r differ and meet (U10.v); [mut_adj3 r a b c] -
      a, b, c are pairwise related by r (U10.v); [cubic_bridgeless] (U10.v);
      [line_rel] - two multigraph edges share an endpoint, the adjacency of base's
      undirected line graph (base/theories/base.v).
    Notes: adjacency of Petersen edges is taken on supports, so it does not depend on the
      ordered representative chosen for an edge. The triple condition is imposed on all
      ordered triples e1, e2, e3 that are pairwise [line_rel]-adjacent; since [line_rel]
      is irreflexive on distinct edges only, a triple with repetitions cannot satisfy the
      hypothesis.
      REPAIRED (foundation repair, 2026-09-23): [bridgeless], hence
      [cubic_bridgeless], now reads [is_bridge] through the UNDIRECTED [uwalk]
      of GTBase.base, so it is the textbook "no cut edge". Under the previous
      DIRECTED reading (coq-graph-theory's [eseparates] over [walk]) a cubic
      loopless multigraph could only be a disjoint union of triple-edge
      dipoles - no snark, no Petersen graph - so the hypothesis class was
      essentially empty of the conjecture's content; that is no longer the
      case. *)
Definition petersen_coloring_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists f : edge G -> Pedge,
      forall e1 e2 e3 : edge G,
        mut_adj3 (@line_rel G) e1 e2 e3 ->
        mut_adj3 Padj (f e1) (f e2) (f e3).

(** ================================================================= *)
(** ** Row 3 — Intersecting two perfect matchings (Fan–Raspaud) *)
(** OPEN.

    Source: "Every bridgeless cubic graph has two perfect matchings M_1, M_2 so
    that M_1 ∩ M_2 does not contain an odd edge-cut." *)

(** An ODD edge-cut: a (nonempty) edge cut [cut S] of odd cardinality.  (The
    [T != set0] clause is kept for readability even though [odd #|set0| = false]
    already forces nonemptiness — see [grounding_U10.is_odd_edge_cut_neq0].) *)
Definition is_odd_edge_cut (G : mgraph) (T : {set edge G}) : Prop :=
  exists S : {set G}, [/\ T = cut S, T != set0 & odd #|T|].

(** An edge set CONTAINS an odd edge-cut iff some odd edge-cut is a subset. *)
Definition contains_odd_edge_cut (G : mgraph) (H : {set edge G}) : Prop :=
  exists T : {set edge G}, T \subset H /\ is_odd_edge_cut T.

(** Corpus row: opg:intersecting_two_perfect_matchings
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/intersecting_two_perfect_matchings/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/intersecting_two_perfect_matchings.json
    English statement: (Open Problem Garden, "The intersection of two perfect matchings")
      Every bridgeless cubic multigraph with at least one vertex has two perfect matchings
      M1 and M2 such that the intersection of M1 and M2 contains no odd edge-cut, that is,
      no subset of it is the set of edges with exactly one endpoint in some vertex set and
      of odd cardinality.
    Definitions: [is_perfect_matching M] - every vertex has exactly one incident edge in M
      (U10.v); [cubic_bridgeless] (U10.v); [is_odd_edge_cut T] - T is the edge cut of some
      vertex set, is nonempty and has odd size (U10.v); [contains_odd_edge_cut H] - some
      odd edge-cut is a subset of H (U10.v); [cut S] - the edges with exactly one endpoint
      in S (cycle-theory/theories/foundations/connectivity.v).
    Notes: following the source, which says "two perfect matchings M_1, M_2", no
      distinctness M1 different from M2 is imposed, so the two matchings may coincide; the
      resulting single-matching case is still non-trivial. The nonemptiness clause in
      [is_odd_edge_cut] is redundant, since a set of odd size is nonempty, and is kept for
      readability, see [grounding_U10.is_odd_edge_cut_neq0].
      REPAIRED (foundation repair, 2026-09-23): [bridgeless], hence
      [cubic_bridgeless], now reads [is_bridge] through the UNDIRECTED [uwalk]
      of GTBase.base, so it is the textbook "no cut edge". Under the previous
      DIRECTED reading (coq-graph-theory's [eseparates] over [walk]) a cubic
      loopless multigraph could only be a disjoint union of triple-edge
      dipoles - no snark, no Petersen graph - so the hypothesis class was
      essentially empty of the conjecture's content; that is no longer the
      case. *)
Definition intersecting_two_perfect_matchings_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic_bridgeless G ->
    exists M1 M2 : {set edge G},
      [/\ is_perfect_matching M1, is_perfect_matching M2
        & ~ contains_odd_edge_cut (M1 :&: M2)].
