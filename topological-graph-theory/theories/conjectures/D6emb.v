(** * Topological.conjectures.D6emb — milestone D6emb (namespace Topological, plan v4)

    Statement-only formalizations (AXIOM-FREE: no Conjecture/Axiom/Parameter/
    Admitted) of three EMBEDDING / surface conjectures.  All three are stated
    against the COMPLETE, axiom-free Track-A combinatorial-topology foundation
    [Topological.foundations.embedding] (orientable rotation systems / ribbon
    graphs): [dart], [edge_perm], [embedding] (a rotation system, PROVEN
    inhabited for every [G] by [embedding_exists] — so the embedding TYPE is
    non-empty and every [forall E] / [exists E] quantifier below ranges over an
    inhabited domain; the added [triangulation] / 2-connectivity / positive-
    curvature filters are conjecture HYPOTHESES, not proven realizable),
    [face_perm]/[face_of]/[face_size] (faces =
    orbits of [face_perm = erot * edge_perm]), [triangulation], [planar_embedding]
    (genus 0), and [combinatorial_curvature]/[positive_curvature].  No metric
    geometry; no planarity stack (planar_embedding is the combinatorial genus-0
    predicate of the foundation, not the G2 four-colour planarity oracle).

    CARRIERS (per row.rocq_idiom): each row quantifies over a simple graph
    [G : sgraph] (coq-graph-theory simple graphs = simple + loopless, and the
    rotation system built on it is orientable by construction) together with an
    [embedding G] where the statement is about a chosen/every surface embedding.

    NEW AREA-SPECIFIC PRIMITIVES (all local to this file, none cross-area):
      - [antiprism n : sgraph] — the n-antiprism on ['I_n * bool] (two n-cycles
        plus the connecting triangles: top i ~ bottom i and top i ~ bottom (i+1));
      - [is_prism] / [is_antiprism] — "[G] is (isomorphic to) a prism / antiprism".
    A prism is [cycle_graph n □ 'K_2] (base's [cartesian_product]); the antiprism
    is the concrete graph above.  These are intrinsically about the
    positive-curvature classification and are NOT plausibly cross-area, so they
    stay local (not tagged [@MOVE-to-base]).  Everything else is REUSED verbatim
    from base ([cartesian_product], [cycle_graph], ['K_2], [k_connected], [N(_)],
    [connected], [≃]) or from the embedding foundation. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.foundations Require Import embedding signed_embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The n-antiprism (area-specific primitive)

    Vertices [('I_n * bool)]: the boolean flags the two n-gons ([true] = "top",
    [false] = "bottom").  Directed adjacency [anti_dir], symmetrised to
    [anti_rel]:
      - same n-gon: [i], [j] adjacent on the cycle (base's [cyc_rel]);
      - vertical rung: top [i] ~ bottom [i];
      - slanted rung:  top [i] ~ bottom [i+1] (mod n).
    Together the rungs make the connecting triangles.  Symmetrising by [anti_dir
    u v || anti_dir v u] gives symmetry for free; irreflexivity holds because the
    same-n-gon term is [cyc_rel]-irreflexive and each rung forces [true] on one
    endpoint and [false] on the other. *)

Section Antiprism.
Variable n : nat.

Definition anti_dir (u v : 'I_n * bool) : bool :=
  let: (i, a) := u in let: (j, b) := v in
  ((a == b) && cyc_rel i j)
  || (a && ~~ b && ((i == j) || (((val i).+1 %% n) == val j))).

Definition anti_rel (u v : 'I_n * bool) : bool := anti_dir u v || anti_dir v u.

Lemma anti_sym : symmetric anti_rel.
Proof. by move=> u v; rewrite /anti_rel orbC. Qed.

Lemma anti_irrefl : irreflexive anti_rel.
Proof.
by move=> [i a]; rewrite /anti_rel orbb /anti_dir eqxx cyc_irrefl /= andbN.
Qed.

Definition antiprism : sgraph := SGraph anti_sym anti_irrefl.

End Antiprism.

(** [G] is a prism = [G ≃ C_n □ K_2] for some [n > 2] (guard [2 < n] excludes the
    degenerate small cases and the K_2 / theta base). *)
Definition is_prism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ cartesian_product (cycle_graph n) 'K_2).

(** [G] is an antiprism = [G ≃ antiprism n] for some [n > 2]. *)
Definition is_antiprism (G : sgraph) : Prop :=
  exists n : nat, 2 < n /\ inhabited (G ≃ antiprism n).

(** Corpus row: opg:grunbaums_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/grunbaums_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/grunbaums_conjecture.json
    English statement: (Open Problem Garden, "Grunbaum's Conjecture")
      Corpus claim: if G is a simple loopless triangulation of an orientable surface then the
      dual of G is 3-edge-colourable.  Back-translation of the Rocq body: for every finite
      simple graph G and every rotation system E on G all of whose faces have exactly three
      darts, there is a map c from darts of G to a 3-element set that (i) gives the two darts
      of each edge the same colour and (ii) gives the three darts d, face_perm(d),
      face_perm(face_perm(d)) of every face pairwise different colours - which is exactly a
      proper 3-edge-colouring of the dual of the triangulation.
    Definitions: [dart G] - an ordered pair of adjacent vertices
      (topological-graph-theory/theories/foundations/embedding.v); [edge_perm G] - the
      dart-reversing involution, so an edge is a pair {d, edge_perm d} (same file);
      [embedding G] - an orientable rotation system, i.e. a permutation of the darts whose
      orbits are exactly the dart sets of the individual vertices (same file), PROVEN
      inhabited for every G by [embedding_exists]; [face_perm E] - the composite
      rotation * edge_perm, whose orbits are the faces (same file); [triangulation E] -
      every face orbit has exactly 3 darts (same file).
    Notes: (1) ORIENTABILITY IS LOAD-BEARING: quantifying over the general-surface layer
      [emap] (signed_embedding.v) instead of the orientable [embedding] would make the row
      classically FALSE - K6 triangulates the projective plane with the Petersen graph as
      dual, which is not 3-edge-colourable.  [embedding] is orientable by construction, which
      is exactly the source's class.  (2) STATUS CAVEAT: the OPG source records the row as
      open, but the general orientable form encoded here was REFUTED by Kochol (2009,
      polyhedral embeddings of snarks in orientable surfaces of large genus); the low-genus
      (e.g. toroidal) cases remain open.  The encoding is faithful to the source conjecture
      as stated, not to its surviving special cases.  (3) The dual is not constructed as a
      graph: "the dual is 3-edge-colourable" is rendered directly as a colouring of the
      primal darts, constant on edges and rainbow on each triangular face - legitimate
      because the dual of a triangulation is cubic and its edges are the primal edges.
      (4) The [triangulation] filter is a conjecture hypothesis, not proven realizable. *)
Definition grunbaums_statement : Prop :=
  forall (G : sgraph) (E : embedding G),
    triangulation E ->
    exists c : dart G -> 'I_3,
      (forall d : dart G, c d = c (edge_perm G d)) /\
      (forall d : dart G,
         c d <> c (face_perm E d) /\
         c (face_perm E d) <> c (face_perm E (face_perm E d)) /\
         c d <> c (face_perm E (face_perm E d))).

(** Corpus row: opg:the_circular_embedding_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/the_circular_embedding_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/the_circular_embedding_conjecture.json
    English statement: (Open Problem Garden, "The circular embedding conjecture")
      Every 2-connected finite simple graph admits an embedding in some closed surface,
      orientable or not, in which the boundary of every face is a cycle.  In the Rocq body:
      for every finite simple graph G that is 2-connected there is a signed rotation system M
      on G such that every face-tracing orbit of M visits pairwise-distinct vertices.
    Definitions: [emap G] - a rotation system together with an edge signature, i.e. a
      Mohar-Thomassen embedding scheme, covering embeddings in ALL closed surfaces
      (topological-graph-theory/theories/foundations/signed_embedding.v), proven inhabited
      for every G by [emap_exists]; [circular_emap M] - the source-vertex map is injective on
      each orbit of the signed face permutation (same file); [k_connected G 2] - more than 2
      vertices, and deleting any single vertex leaves the graph connected
      (base/theories/base.v).
    Notes: The signed layer is a deliberate correction found by the Track-A review: the
      earlier [embedding G] quantification expressed only the strictly stronger ORIENTABLE
      strong-embedding conjecture, whereas the source allows any surface.  PROXY CAVEAT
      recorded in signed_embedding.v: on graphs with degree-1 vertices [circular_emap] is
      strictly WEAKER than "every face boundary is a cycle" (a pendant edge yields a 2-flag
      orbit with distinct sources although its facial walk traverses one edge twice - K2
      satisfies [circular_emap] yet has no cycle); a 2-flag orbit forces a rotation-fixed
      dart, hence a degree-1 source, so under the [k_connected G 2] hypothesis used here
      orbit length is at least 3 and the predicate is EXACTLY "the boundary is a simple
      cycle".  Non-orientable signatures are genuinely expressible
      ([twisted_triangle_nonorientable]), so the general-surface quantifier is not
      degenerate. *)
Definition the_circular_embedding_statement : Prop :=
  forall (G : sgraph),
    k_connected G 2 ->
    exists M : emap G, circular_emap M.

(** Corpus row: opg:what_is_the_largest_graph_of_positive_curvature
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/what_is_the_largest_graph_of_positive_curvature/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/what_is_the_largest_graph_of_positive_curvature.json
    English statement: (Open Problem Garden, "What is the largest graph of positive
      curvature?")
      Corpus question: what is the largest connected planar graph of minimum degree 3 that
      has everywhere positive combinatorial curvature but is neither a prism nor an
      antiprism?  Back-translation of the Rocq body: there is a natural number Nmax such that
      every finite simple graph G carrying a genus-0 rotation system E is bounded by Nmax in
      its number of vertices, provided G is connected, every vertex has more than 2
      neighbours, the corner curvature of E is positive at every vertex, and G is neither a
      prism nor an antiprism.
    Definitions: [embedding G], [planar_embedding E] (Euler genus 0),
      [combinatorial_curvature E v] (the rational 1 - deg(v)/2 + the sum over the corners at
      v of 1/face_size) and [positive_curvature E] (positive at every vertex) - all in
      topological-graph-theory/theories/foundations/embedding.v; [antiprism n] - the
      n-antiprism on 'I_n * bool, two n-cycles plus the vertical and slanted rungs that make
      the connecting triangles (this file); [is_prism G] / [is_antiprism G] - G is isomorphic
      to [cycle_graph n] box ['K_2], respectively to [antiprism n], for some n > 2 (this
      file); [cartesian_product], [cycle_graph], [k_connected], [connected], [N(_)] are reused
      verbatim from base/theories/base.v and coq-graph-theory.
    Notes: The OPG entry is a "what is it?" PROBLEM; the encoding states the FINITENESS that
      makes "largest" meaningful - a uniform vertex bound over the whole class - rather than
      naming the extremal graph.  This is weaker than answering the problem but is the
      natural Prop-valued reading and is non-trivial (the class is conjecturally finite).
      "Planar" is here a genus-0 ROTATION SYSTEM, not base's [wagner_planar], because the
      curvature is defined from the faces of a fixed embedding.  [is_prism]/[is_antiprism]
      use graph isomorphism, so the exclusion is up to isomorphism as in the source; the
      guard n > 2 excludes the degenerate small cases.  The prism/antiprism primitives are
      intrinsically tied to this classification and stay local (not tagged @MOVE-to-base). *)
Definition what_is_the_largest_graph_of_positive_curvature_statement : Prop :=
  exists Nmax : nat,
    forall (G : sgraph) (E : embedding G),
      connected [set: G] ->
      planar_embedding E ->
      (forall v : G, 2 < #|N(v)|) ->
      positive_curvature E ->
      ~ is_prism G ->
      ~ is_antiprism G ->
      #|G| <= Nmax.
