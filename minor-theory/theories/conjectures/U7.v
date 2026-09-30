(** * Minor.conjectures.U7 — milestone U7 (namespace Minor, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of six open problems on graph minors and immersions.

    CORE API used (verified to load on switch `digraph`, Rocq 9.1.1 +
    coq-graph-theory + graph-theory-base):
      - [G : sgraph]; [x -- y] adjacency = [sedge x y]; [N(x)] open
        neighbourhood ({set G}); [#|N(v)|] = degree of [v];
      - [minor G H : Prop] — note the LIBRARY ORDER: [minor G H] means "G
        CONTAINS H as a minor" ([exists phi, minor_map phi]).  So "G has a K6
        minor" is [minor G 'K_6], NOT [minor 'K_6 G];
      - ['K_n] = [complete n : sgraph] : the complete graph on [n] vertices —
        the manifest's "complete-graph" primitive ALREADY exists as ['K_n], so
        no new primitive is introduced for it;
      - [k.-connected G] = [kconnected k G : Prop] (connectivity.v);
      - [α(G)] = independence number (whole graph); [α(G) <= 2] ⟺ no
        independent set of size 3;
      - [χ([set: G])] = chromatic number of the whole graph (coloring.v);
      - [induced (~: S)] : the subgraph of [G] obtained by DELETING the vertex
        set [S] (induced on the complement);
      - [regular G d] (base) : every vertex of [G] has degree exactly [d];
      - [ceil_div a b] (base) : ⌈a/b⌉.

    PLANARITY (plan G2).  coq-graph-theory-planar / coq-fourcolor are NOT
    installed.  The two rows whose statement needs planarity
    ([high_connectivity_no_k_n_statement], [jorgensens_statement]) now use the
    COMBINATORIAL predicate [wagner_planar] of base ("no K5 and no K3,3 minor"),
    which by Wagner's theorem is exactly planarity, so both rows are faithful and
    axiom-free without any planar layer.  The local helpers
    [planar_after_deleting] and [apex] keep an abstract planarity predicate as a
    PARAMETER so they can be reused should a real [planar] predicate land; the two
    statements instantiate it with [wagner_planar].  What [wagner_planar] does NOT
    capture is a fixed embedding, faces or genus, so rows about plane
    triangulations or surfaces still need the real planar layer (G2).  The other
    five rows are unconditional. *)

From GraphTheory Require Import minor connectivity coloring.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** New AREA primitives *)

(** [path_edges s] : the set of (undirected) edges traversed by the vertex
    sequence [s], i.e. the 2-element sets of consecutive entries.  Helper for
    [immersion] below.  [@MOVE-to-base] candidate (walk/edge bookkeeping). *)
Definition path_edges (G : sgraph) (s : seq G) : {set {set G}} :=
  [set e in [seq [set p.1; p.2] | p <- zip s (behead s)]].

(** [immersion G H] : "G immerses H" (G contains an immersion of H).  There is
    an injection [f] of [V(H)] into [V(G)] and, for every edge [u -- v] of [H],
    a walk [f u :: P u v] in [G] from [f u] to [f v]; these walks are pairwise
    EDGE-DISJOINT (the defining feature of an immersion, as opposed to a
    topological minor where the branch paths must also be internally
    vertex-disjoint).  Cross-area primitive (used by the colouring conjecture
    below); not present in base — defined here and tagged [@MOVE-to-base]. *)
Definition immersion (G H : sgraph) : Prop :=
  exists (f : H -> G) (P : H -> H -> seq G),
    injective f /\
    (forall u v : H, u -- v ->
        path sedge (f u) (P u v) /\ last (f u) (P u v) = f v) /\
    (forall u1 v1 u2 v2 : H, u1 -- v1 -> u2 -- v2 ->
        [set u1; v1] != [set u2; v2] ->
        [disjoint path_edges (f u1 :: P u1 v1)
                & path_edges (f u2 :: P u2 v2)]).

(** [average_degree_geq G a b] : the average degree of [G] is at least the
    rational [a/b], stated cross-multiplied to stay in [nat].  Average degree
    = (∑ deg)/|G|, so "≥ a/b" ⟺ [a * #|G| <= b * (∑ deg)].  Cross-area
    (extremal) primitive, not in base — [@MOVE-to-base]. *)
(* [average_degree_geq] now from graph-theory-base (identical). *)

(** [planar_after_deleting is_planar G k] : there is a set of [k] vertices
    whose deletion leaves a planar graph (the "apex-bounded-deletion" notion).
    AREA primitive, parametrised by an abstract planarity predicate (G2 gate).
    Intentionally NOT tagged [@MOVE-to-base]: unlike the three cross-area
    helpers above, this and [apex] depend on the abstract [is_planar] and
    cannot migrate to base until a real [planar] predicate lands (G2). *)
Definition planar_after_deleting
    (is_planar : sgraph -> Prop) (G : sgraph) (k : nat) : Prop :=
  exists S : {set G}, #|S| = k /\ is_planar (induced (~: S)).

(** [apex is_planar G] : [G] is apex — deleting a single vertex makes it
    planar ("planar plus one vertex").  AREA primitive (G2 gate). *)
Definition apex (is_planar : sgraph -> Prop) (G : sgraph) : Prop :=
  exists v : G, is_planar (induced (~: [set v])).

(** Corpus row: opg:forcing_a_k_6_minor
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/forcing_a_k_6_minor/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/forcing_a_k_6_minor.json
    English statement: (Open Problem Garden, "Forcing a K_6-minor")
      The conjunction of two conjectures.  First: every nonempty finite simple graph in
      which every vertex has degree at least 7 contains the complete graph on 6 vertices
      as a minor.  Second: every nonempty finite simple graph that is 7-connected contains
      the complete graph on 6 vertices as a minor.
    Definitions: standard
    Notes: the library argument order is [minor G H] = "G contains H as a minor", so "G has
      a K_6 minor" is [minor G 'K_6], not [minor 'K_6 G].  Minimum degree at least 7 is
      spelled [forall v, 7 <= #|N(v)|].  The [0 < #|G|] guard is a soundness guard: without
      it the empty graph satisfies the degree hypothesis vacuously yet has no K_6 minor.  It
      is redundant in the second conjunct, where [7.-connected G] already forces 7 < #|G|. *)
Definition forcing_a_k_6_minor_statement : Prop :=
  (forall G : sgraph, 0 < #|G| ->
      (forall v : G, 7 <= #|N(v)|) -> minor G 'K_6)
  /\
  (forall G : sgraph, 0 < #|G| ->
      7.-connected G -> minor G 'K_6).

(** Corpus row: opg:seagull_problem
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/seagull_problem/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/seagull_problem.json
    English statement: (Open Problem Garden, "Seagull problem")
      Every nonempty finite simple graph G on n vertices with no independent set of size 3
      contains, as a minor, the complete graph on the ceiling of n/2 vertices.
    Definitions: standard
    Notes: "no independent set of size 3" is the independence number bound [alpha(G) <= 2].
      The source's "complete graph on at least n/2 vertices" is witnessed by the strongest
      integral reading, the ceiling [ceil_div #|G| 2] (GTBase); the [0 < #|G|] guard keeps
      the empty graph out. *)
Definition seagull_statement : Prop :=
  forall G : sgraph, 0 < #|G| ->
    α(G) <= 2 -> minor G 'K_(ceil_div #|G| 2).

(** Corpus row: opg:coloring_and_immersion
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/coloring_and_immersion/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/coloring_and_immersion.json
    English statement: (Open Problem Garden, "Coloring and immersion")
      For every positive integer t and every finite simple graph G whose chromatic number is
      at least t, G immerses the complete graph on t vertices.
    Definitions: [immersion G H] - G contains an immersion of H: there is an injection f from
      the vertices of H into those of G and, for every edge uv of H, a walk in G from f(u) to
      f(v), the walks belonging to distinct edges of H being pairwise edge-disjoint
      (minor-theory/theories/conjectures/U7.v); [path_edges s] - the set of two-element vertex
      sets formed by consecutive entries of a vertex sequence, i.e. the edges that walk
      traverses (same file).
    Notes: an [sgraph] is loopless by construction (adjacency is irreflexive), so the source's
      parenthetical "loopless" needs no separate hypothesis.  Immersion is weaker than a
      topological minor: the branch walks are required to be edge-disjoint only, not
      internally vertex-disjoint. *)
Definition coloring_and_immersion_statement : Prop :=
  forall (t : nat) (G : sgraph),
    0 < t -> t <= χ([set: G]) -> immersion G 'K_t.

(** Corpus row: opg:high_connectivity_no_k_n
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/high_connectivity_no_k_n/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/high_connectivity_no_k_n.json
    English statement: (Open Problem Garden, "Highly connected graphs with no K_n minor")
      For every natural number n there is a threshold N such that every finite simple graph
      on at least N vertices that is n-connected and has no K_n minor admits a set of exactly
      n-5 vertices whose deletion leaves a planar graph.
    Definitions: [planar_after_deleting P G k] - there is a vertex set S of size exactly k such
      that the subgraph induced on the complement of S satisfies P
      (minor-theory/theories/conjectures/U7.v); [wagner_planar G] - G has neither K_5 nor the
      complete bipartite graph K_(3,3) as a minor, which by Wagner's theorem is exactly
      planarity (base/theories/base.v).
    Notes: "sufficiently large" is read as the threshold N chosen after n and before G.
      Planarity uses the combinatorial Wagner predicate, so the statement is axiom-free and
      needs no fourcolor / planar layer; it does not capture an embedding, faces or genus.
      [n - 5] is truncated natural subtraction, so for n <= 5 the conclusion degenerates to
      "G itself is planar" (deletion of the empty set) - stronger than the intended reading of
      the source, where n - 5 is negative and the problem is only meaningful for n >= 5. *)
Definition high_connectivity_no_k_n_statement : Prop :=
  forall (n : nat),
    exists N : nat,
      forall G : sgraph,
        N <= #|G| -> n.-connected G -> ~ minor G 'K_n ->
        planar_after_deleting wagner_planar G (n - 5).

(** Corpus row: opg:jorgensens_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/jorgensens_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/jorgensens_conjecture.json
    English statement: (Open Problem Garden, "Jorgensen's Conjecture")
      Every 6-connected finite simple graph with no K_6 minor is apex, that is, some single
      vertex can be deleted from it to leave a planar graph.
    Definitions: [apex P G] - there is a vertex v of G such that the subgraph induced on the
      complement of the singleton {v} satisfies P (minor-theory/theories/conjectures/U7.v);
      [wagner_planar G] - G has neither K_5 nor K_(3,3) as a minor, i.e. planarity by Wagner's
      theorem (base/theories/base.v).
    Notes: planarity is the combinatorial Wagner predicate (axiom-free, no fourcolor layer, no
      embedding/faces).  No nonemptiness guard is needed: [6.-connected G] already forces
      6 < #|G|, so the vertex whose deletion is asserted exists. *)
Definition jorgensens_statement : Prop :=
  forall (G : sgraph),
    6.-connected G -> ~ minor G 'K_6 -> apex wagner_planar G.

(** Corpus row: opg:forcing_a_2_regular_minor
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/forcing_a_2_regular_minor/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/forcing_a_2_regular_minor.json
    English statement: (Open Problem Garden, "Forcing a 2-regular minor")
      For every t at least 3, every nonempty finite simple graph G whose average degree is at
      least (4t-6)/3, that is (4/3)t - 2, contains as a minor every 2-regular graph H on
      exactly t vertices.
    Definitions: standard
    Notes: the rational degree bound is cross-multiplied to stay in the naturals:
      [average_degree_geq G a b] (GTBase) unfolds to a * #|G| <= b * (sum of the degrees), and
      (4/3)t - 2 = (4t-6)/3.  The guard [3 <= t] keeps the numerator [4*t-6] out of natural
      truncation and is harmless, since a 2-regular graph has at least 3 vertices.  The
      [0 < #|G|] guard is required for soundness: the empty graph satisfies the degree
      hypothesis vacuously (both sides are 0) yet has no nonempty minor. *)
Definition forcing_a_2_regular_minor_statement : Prop :=
  forall (t : nat) (G H : sgraph),
    3 <= t ->
    0 < #|G| ->
    average_degree_geq G (4 * t - 6) 3 ->
    regular H 2 -> #|H| = t ->
    minor G H.
