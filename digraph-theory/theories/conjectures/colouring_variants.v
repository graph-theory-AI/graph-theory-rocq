(** * Digraph.conjectures.colouring_variants — P11: colouring variants

    Three families of "colouring" conjectures over digraphs, stated (not proved)
    on top of the core HB DiGraph -> Oriented -> Tournament stack and the
    dichromatic / stable machinery:

      1. MAJORITY COLOURING (Kreutzer, Oum, Seymour, van der Zypen, Wood,
         arXiv:1608.03040). A vertex k-colouring is "majority" when no vertex has
         more than half of its out-neighbours in its own colour class.
           - [majority_3col_statement]  (Conj 2): every digraph has one with 3 cols;
           - [majority_k1col_statement]  (Conj 9): the (k+1)-colour, (1/k)·deg⁺ form;
           - [majority_3col_tournament_statement] (Open Pb 2) and
             [majority_3col_eulerian_statement]   (Open Pb 3), the cheap variants.

      2. ORIENTED CHROMATIC NUMBER / DIGRAPH HOMOMORPHISM (Courcelle; Sopena). A
         digraph homomorphism [dhom] is an arc-preserving map; an oriented
         colouring is a [dhom] onto a tournament on the colour set, and the
         oriented chromatic number is bounded over planar oriented graphs
         ([oriented_chromatic_planar_bounded_statement]; planarity reuses
         [two_extremal.planar_sg] on the underlying simple graph).

      3. ARC-COLOURING / MONOCHROMATIC REACHABILITY (Sands–Sauer–Woodrow and the
         tournament rainbow-triangle variant). An arc colouring colours each arc;
         a monochromatic directed path is a [connect] in one colour's sub-relation.
           - [mono_reach_or_rainbow_statement] (3-arc-coloured tournament: rainbow
             triangle or a monochromatic-reachability root);
           - [sands_sauer_woodrow_statement]   (k-arc-coloured digraph: bounded
             union of stable sets reachable monochromatically from everywhere).

    All "for all X" statements guard the empty digraph where vacuity would make
    them trivially (and unfaithfully) true. Relative edges connecting the
    statements are proved as [Theorem ... Qed].
    See docs/CONJECTURES_FORMALIZATION_PLAN.md (P11). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath.
From Digraph Require Import dichromatic two_extremal classic_core.
From Digraph.foundations Require degree_balance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** 1. Majority colouring ************************************************** *)

(** The set of out-neighbours of [v] that share [v]'s colour, under a vertex
    colouring [col]. Pure function over the arc relation; works for any
    digraph. *)
Definition same_col_outnb {D : diGraphType} {k : nat}
    (col : D -> 'I_k) (v : D) : {set D} :=
  [set w | (v --> w) && (col w == col v)].

(** [col] is a MAJORITY colouring: at every vertex at most half of the
    out-neighbours share its colour. Written [2 * (#same) <= outdeg] to stay in
    [nat] (no division). *)
Definition majority_col {D : diGraphType} {k : nat} (col : D -> 'I_k) : bool :=
  [forall v : D, 2 * #|same_col_outnb col v| <= outdeg v].

(** The parametric "(1/k)·deg⁺" bound of Conjecture 9, again cleared of
    fractions: at most [outdeg v / k] same-coloured out-neighbours, i.e.
    [k * (#same) <= outdeg v]. (At [k = 2] this is exactly [majority_col].) *)
Definition kmajority_col {D : diGraphType} {m : nat} (k : nat)
    (col : D -> 'I_m) : bool :=
  [forall v : D, k * #|same_col_outnb col v| <= outdeg v].

Lemma kmajority_col2 (D : diGraphType) (col : D -> 'I_2) :
  kmajority_col 2 col = majority_col col.
Proof. by []. Qed.

(** Corpus row: arxiv:1608.03040#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.03040__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.03040__00.json
    English statement: (Kreutzer, Oum, Seymour, van der Zypen, Wood 2016, arXiv:1608.03040, Conjecture 2)
      Every finite loopless digraph has a majority 3-colouring: there is a colouring of its
      vertices by three colours such that every vertex v has at most half of its out-neighbours
      coloured like v.
    Definitions: [loopless D] - no vertex has an arc to itself (conjectures/two_extremal.v);
      [majority_col col] - at every vertex at most half of its out-neighbours carry the same
      colour as itself, written without division as 2 * #(same-coloured out-neighbours) <= outdeg
      (this file); [same_col_outnb col v] - the out-neighbours of v with the colour of v (this
      file); [outdeg v] - out-degree (core/oriented.v); ['I_3] - a three-element colour set
      (MathComp).
    Notes: the [loopless D] guard is load-bearing. [diGraphType] allows loops, and a loop at v
      makes v a same-coloured out-neighbour of itself, so the one-vertex digraph with a loop has no
      majority colouring with any number of colours
      (meta/probe_hints/majority_3col_statement.v).  The source's digraphs have no loops: its
      Theorem 1, every digraph has a majority 4-colouring, fails on that digraph.  The guard was
      added on 2026-10-25 (meta/STATEMENT_IMPROVEMENTS.md).  The empty digraph and isolated
      vertices satisfy the condition trivially. *)
Definition majority_3col_statement : Prop :=
  forall D : diGraphType, loopless D -> exists col : D -> 'I_3, majority_col col.

(** Corpus row: arxiv:1608.03040#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.03040__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.03040__01.json
    English statement: (Kreutzer, Oum, Seymour, van der Zypen, Wood 2016, arXiv:1608.03040, Conjecture 9)
      For every k >= 2 and every finite loopless digraph there is a colouring of the vertices by
      k+1 colours such that every vertex v has at most a fraction 1/k of its out-neighbours
      coloured like v, written without division as k * #(same-coloured out-neighbours of v) <=
      outdeg v.
    Definitions: [loopless D] - no vertex has an arc to itself (conjectures/two_extremal.v);
      [kmajority_col k col] - the parametric bound k * #(same-coloured out-neighbours) <= outdeg
      at every vertex (this file); [same_col_outnb col v] (this file); [outdeg v]
      (core/oriented.v); ['I_k.+1] - a colour set of size k+1 (MathComp).
    Notes: The corpus row is marked disproved (Girao, Kittipassorn, Popielarz showed k+1 colours
      do not suffice for k >= 3); the definition encodes the conjecture as originally stated,
      which is what a refutation must contradict. At k = 2 it is exactly majority colouring
      ([kmajority_col2] in this file). The [loopless D] guard is load-bearing: a loop makes a
      vertex a same-coloured out-neighbour of itself, so the one-vertex digraph with a loop
      refuted the earlier unguarded body cheaply (meta/probe_hints/majority_k1col_statement.v),
      unlike the genuine refutation, which uses loopless digraphs.  The guard was added on
      2026-10-25 (meta/STATEMENT_IMPROVEMENTS.md). *)
Definition majority_k1col_statement : Prop :=
  forall (k : nat), 2 <= k ->
    forall D : diGraphType, loopless D -> exists col : D -> 'I_k.+1, kmajority_col k col.

(** Corpus row: arxiv:1608.03040#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.03040__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.03040__03.json
    English statement: (Kreutzer, Oum, Seymour, van der Zypen, Wood 2016, arXiv:1608.03040, Open Problem 2)
      Every finite tournament has a majority 3-colouring: a colouring of its vertices by three
      colours in which every vertex has at most half of its out-neighbours coloured like itself.
    Definitions: [tournament] - a finite digraph whose arc relation is irreflexive and, for any
      two distinct vertices, holds in exactly one direction (core/tournament.v); [majority_col]
      (this file). *)
Definition majority_3col_tournament_statement : Prop :=
  forall T : tournament, exists col : T -> 'I_3, majority_col col.

(** A digraph is EULERIAN when in-degree equals out-degree at every vertex. *)
Definition indeg (D : diGraphType) (v : D) : nat := degree_balance.indeg v.
Definition eulerian (D : diGraphType) : bool :=
  degree_balance.balancedb D.

(** Corpus row: arxiv:1608.03040#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1608.03040__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1608.03040__04.json
    English statement: (Kreutzer, Oum, Seymour, van der Zypen, Wood 2016, arXiv:1608.03040, Open Problem 3)
      Every finite loopless Eulerian digraph, that is every loopless digraph in which in-degree
      equals out-degree at every vertex, has a majority 3-colouring.
    Definitions: [loopless D] - no vertex has an arc to itself (conjectures/two_extremal.v);
      [eulerian D] - in-degree equals out-degree at every vertex (this file); [indeg v] -
      in-degree (this file, also defined in conjectures/classic_core.v); [majority_col] (this
      file).
    Notes: [eulerian] encodes only the balanced-degree condition and drops the connectivity
      usually required of an Eulerian digraph, so the hypothesis is weaker and the statement
      correspondingly stronger; majority colouring is a local condition, and a balanced digraph
      is a disjoint union of connected balanced digraphs, so the two readings are equivalent.
      The [loopless D] guard is load-bearing: a looped vertex is balanced and is a same-coloured
      out-neighbour of itself, so the one-vertex digraph with a loop refuted the earlier
      unguarded body (meta/probe_hints/majority_3col_eulerian_statement.v); the source's digraphs
      have no loops.  The guard was added on 2026-10-25 as a reviewed one-way source repair of
      this migrated row (direction weaken; meta/STATEMENT_IMPROVEMENTS.md). *)
Definition majority_3col_eulerian_statement : Prop :=
  forall D : diGraphType, loopless D -> eulerian D ->
    exists col : D -> 'I_3, majority_col col.

(** *** Relative edges among the majority statements *)

(** Conjecture 9 at [k = 2] gives a 3-colouring with [2·(#same) <= deg⁺], which
    is exactly the majority condition: Conj 9 ⇒ Conj 2 (both carry the loopless guard). *)
Theorem majority_k1col_implies_majority_3col :
  majority_k1col_statement -> majority_3col_statement.
Proof.
move=> H9 D lD; have [col Hcol] := H9 2 (leqnn 2) D lD.
by exists col; exact: Hcol.
Qed.

(** The general digraph statement specialises to tournaments, which are loopless
    (their arc relation is irreflexive). *)
Theorem majority_3col_implies_tournament :
  majority_3col_statement -> majority_3col_tournament_statement.
Proof. by move=> H T; apply: (H T); exact: arcxx. Qed.

(** The general digraph statement specialises to Eulerian digraphs (both carry the
    loopless guard). *)
Theorem majority_3col_implies_eulerian :
  majority_3col_statement -> majority_3col_eulerian_statement.
Proof. by move=> H D lD _; apply: H. Qed.

(** ** 2. Oriented chromatic number / digraph homomorphism ******************* *)

(** A digraph HOMOMORPHISM [H -> T] is an arc-preserving map (every arc of [H]
    maps to an arc of [T]). Note: not required injective, not arc-reflecting —
    this is the right notion for colouring (unlike the induced embedding
    [heroes.ind_subdigraph]). *)
Definition dhom (H T : diGraphType) : Prop :=
  exists f : H -> T, forall u v : H, u --> v -> f u --> f v.

Lemma dhom_id (D : diGraphType) : dhom D D.
Proof. by exists id. Qed.

Lemma dhom_trans (D1 D2 D3 : diGraphType) :
  dhom D1 D2 -> dhom D2 D3 -> dhom D1 D3.
Proof.
case=> f Hf [g Hg]; exists (g \o f) => u v uv.
by apply: Hg; apply: Hf.
Qed.

(** [D] has an ORIENTED [k]-COLOURING when it maps homomorphically onto SOME
    tournament on [k] vertices. (A homomorphism to a tournament forces (i) a
    proper colouring of the underlying graph, since a digon would need a digon
    in the loopless tournament image, and (ii) the "no two arcs with swapped
    colour endpoints" condition, since the image arcs are consistently
    oriented.) The colour set being a tournament is the standard reformulation
    of oriented colouring. *)
Definition oriented_kcolouring (D : diGraphType) (k : nat) : Prop :=
  exists T : tournament, #|T| = k /\ dhom D T.

(** The oriented chromatic number is at most [k] (the least such [k] is the
    oriented chromatic number proper). *)
Definition ochi_le (D : diGraphType) (k : nat) : Prop :=
  oriented_kcolouring D k.

(** Oriented colourings are downward inherited by homomorphic preimages:
    if [D -> D'] and [D'] has an oriented [k]-colouring, so does [D]. *)
Theorem ochi_le_dhom (D D' : diGraphType) (k : nat) :
  dhom D D' -> ochi_le D' k -> ochi_le D k.
Proof.
move=> dDD' [T [Tk hom']]; exists T; split=> //.
exact: dhom_trans dDD' hom'.
Qed.

(** No corpus row: the boundedness form used inside this file for the relative edges (there is a
    single k that oriented-k-colours every loopless digraph with planar underlying graph); the
    corpus row opg:oriented_chromatic_number_of_planar_graphs asks for the maximum value and is
    carried by [oriented_chromatic_number_of_planar_graphs_statement] in conjectures/P9.v. *)
Definition oriented_chromatic_planar_bounded_statement : Prop :=
  exists k : nat,
    forall (D : diGraphType) (llD : loopless D),
      planar_sg (underlyingG llD) -> oriented_kcolouring D k.

(** ** 3. Arc-colouring / monochromatic reachability ************************* *)

(** A [k]-ARC-COLOURING of [D] assigns a colour in ['I_k] to each ordered pair;
    it is only consulted on actual arcs. *)
Definition arc_colouring (D : diGraphType) (k : nat) := D -> D -> 'I_k.

(** The sub-relation of arcs that carry colour [i]. *)
Definition mono_rel (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (i : 'I_k) : rel D :=
  fun u v => (u --> v) && (c u v == i).

(** [v] reaches [w] by a MONOCHROMATIC directed path in colour [i]: the
    reflexive-transitive closure of [mono_rel c i]. (Reflexive: every vertex
    reaches itself by the empty path, as in the standard convention.) *)
Definition mono_reach (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (i : 'I_k) (v w : D) : bool :=
  connect (mono_rel c i) v w.

(** [v] reaches [w] by a monochromatic path of SOME colour. *)
Definition mono_reach_any (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (v w : D) : bool :=
  [exists i : 'I_k, mono_reach c i v w].

Lemma mono_reach_refl (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (i : 'I_k) (v : D) : mono_reach c i v v.
Proof. exact: connect0. Qed.

(** A monochromatic-reachability ROOT: a vertex from which every vertex is
    reachable by a single-colour directed path (colours may differ per target). *)
Definition mono_root (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (v : D) : bool :=
  [forall w : D, mono_reach_any c v w].

(** A RAINBOW directed triangle in a 3-arc-coloured digraph: a directed
    3-cycle [a -> b -> c -> a] whose three arcs carry three DISTINCT colours. *)
Definition rainbow_triangle (D : diGraphType) (c : arc_colouring D 3) : Prop :=
  exists a b c0 : D,
    [/\ a --> b, b --> c0, c0 --> a
      & uniq [:: c a b; c b c0; c c0 a]].

(** No corpus row: the three-colour tournament variant of Sands-Sauer-Woodrow (every
    nonempty tournament whose arcs are coloured with three colours has a rainbow directed
    triangle or a vertex from which every vertex is reachable by a one-colour directed path).
    The row opg:monochromatic_reachability_vs_rainbow_triangles carries exactly this body through
    its alias [P9.monochromatic_reachability_vs_rainbow_triangles_statement]. Until 2026-10-25
    the manifest also attached to this definition the row
    opg:monochromatoc_reachability_in_arc_colored_digraphs, whose text is the general statement;
    that row is now bound to [sands_sauer_woodrow_statement] below (meta/STATEMENT_IMPROVEMENTS.md).
    The guard 0 < #|T| excludes the empty tournament, on which neither disjunct can hold. *)
Definition mono_reach_or_rainbow_statement : Prop :=
  forall (T : tournament) (c : arc_colouring T 3),
    (0 < #|T|)%N ->
    rainbow_triangle c \/ exists v : T, mono_root c v.

(** A [stable] set has no arc inside it (reuse [classic_core.stable]). A subset
    [S] is a union of at most [m] stable sets when it is covered by [m] stable
    parts. *)
Definition union_of_stables (D : diGraphType) (m : nat) (S : {set D}) : Prop :=
  exists parts : seq {set D},
    [/\ size parts <= m,
        all (fun P => stable P) parts
      & S = \bigcup_(P <- parts) P].

(** Corpus row: opg:monochromatoc_reachability_in_arc_colored_digraphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/monochromatoc_reachability_in_arc_colored_digraphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/monochromatoc_reachability_in_arc_colored_digraphs.json
    English statement: (Open Problem Garden, Monochromatic reachability in arc-colored digraphs; Sands-Sauer-Woodrow)
      For every number k of colours there is an integer f such that every finite loopless
      digraph D whose arcs are coloured with k colours has a vertex set S, the union of at most f
      stable sets, such that every vertex of D has a directed path, all of whose arcs carry one
      colour, to some vertex of S.
    Definitions: [arc_colouring D k] - a function assigning a colour in 'I_k to each ordered
      pair, read only on actual arcs (this file); [union_of_stables f S] - S is the union of at
      most f stable sets (this file); [stable S] - no arc joins two members of S (classic_core.v);
      [mono_reach_any c v s] - v reaches s in the sub-relation of the arcs of one colour,
      reflexive-transitive (this file); [loopless D] - no vertex carries a loop (two_extremal.v).
    Notes: "at most f" stable sets is equivalent to the source's "f" stable sets, since the
      empty set is stable; a vertex of S reaches itself by the empty path. The guard
      [loopless D] (added 2026-10-25) is load-bearing: [stable] counts loops inside S, so
      without it a one-vertex digraph with a loop refutes the body
      (meta/probe_hints/sands_sauer_woodrow_statement.v); loops never change monochromatic
      reachability, so the guard keeps the source's reading. For k = 0 only the empty digraph
      carries an arc colouring, a harmless degeneracy. Until 2026-10-25 this row was bound to
      [mono_reach_or_rainbow_statement] above, the three-colour tournament variant
      (meta/STATEMENT_IMPROVEMENTS.md). *)
Definition sands_sauer_woodrow_statement : Prop :=
  forall k : nat, exists f : nat,
    forall (D : diGraphType) (c : arc_colouring D k), loopless D ->
      exists S : {set D},
        [/\ union_of_stables f S
          & forall v : D, exists2 s : D, s \in S & mono_reach_any c v s].

(** *** A cheap sanity edge: the FULL vertex set is always a witnessing target
    set for monochromatic reachability, since every vertex reaches itself by the
    empty (length-0) monochromatic path. (This shows the SSW reachability clause
    is non-vacuous; the conjecture's content is bounding the target set by [f(k)]
    STABLE sets, which [setT] does not satisfy in general.) The dual statement —
    that a monochromatic-reachability ROOT [v] reaches every vertex — is recorded
    too, since it is the defining property of [mono_root]. *)
Theorem setT_is_reach_set (D : diGraphType) (k : nat) (c : arc_colouring D k) :
  (0 < k)%N ->
  forall w : D, exists2 s : D, s \in [set: D] & mono_reach_any c w s.
Proof.
move=> k_gt0 w; exists w; first by rewrite inE.
by apply/existsP; exists (Ordinal k_gt0); exact: mono_reach_refl.
Qed.

Theorem mono_root_reaches_all (D : diGraphType) (k : nat)
    (c : arc_colouring D k) (v : D) :
  mono_root c v -> forall w : D, mono_reach_any c v w.
Proof. by move=> /forallP. Qed.
