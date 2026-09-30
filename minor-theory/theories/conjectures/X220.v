(** * Minor.conjectures.X220 -- width-parameter rows (wave X220, 2026-09-23) *)

From GTBase Require Export base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x220 vocabulary ***********************************************

    Reused from elsewhere: [tw_le]/[tw_ge]/[tree_alpha_le]/[tree_mu_le]
    (Minor.foundations.width_params), [has_induced_copy]/[is_subdivision_of]/
    [subdiv_model]/[sline_graph]/[el_graph] (Minor.foundations.containment),
    [x27_hole]/[x27_even_hole_free] (X27.v), [x42_diamond] (X42.v),
    [Delta]/[triangle_free]/[cycle_graph] (GTBase), [clique]/[KB]/['K_n]/[diso]/
    [induced] (coq-graph-theory), [trunc_log] (MathComp).  Everything below is
    genuinely new. *)

(** *** Walls *************************************************************

    The elementary [t x t] wall on ['I_t * 'I_t] ([u.1] = row, [u.2] = column):
    every horizontal edge of the grid, plus the vertical edge from [(i,j)] to
    [(i+1,j)] exactly when [i + j] is even.  This is the usual brick-wall
    presentation of the wall obtained from the [t x t] grid by deleting
    alternating vertical edges. *)

Definition x220_wall_r0 (t : nat) (u v : 'I_t * 'I_t) : bool :=
  ((u.1 == v.1) && ((u.2 : nat).+1 == v.2)) ||
  [&& (u.2 : nat) == v.2, (u.1 : nat).+1 == v.1 & ~~ odd ((u.1 : nat) + u.2)].

Definition x220_wall_rel (t : nat) (u v : 'I_t * 'I_t) : bool :=
  x220_wall_r0 u v || x220_wall_r0 v u.

Lemma x220_wall_sym (t : nat) : symmetric (@x220_wall_rel t).
Proof. by move=> u v; rewrite /x220_wall_rel orbC. Qed.

Lemma x220_wall_irrefl (t : nat) : irreflexive (@x220_wall_rel t).
Proof.
move=> u; rewrite /x220_wall_rel orbb /x220_wall_r0.
by rewrite !(gtn_eqF (ltnSn _)) andbF /= andbF.
Qed.

Definition x220_wall (t : nat) : sgraph := SGraph (@x220_wall_sym t) (@x220_wall_irrefl t).

(** *** The three-path configurations theta and prism *********************

    A THETA is exactly a subdivision of ['K_2,3]: two branch vertices of degree 3
    joined by three internally disjoint paths of length at least 2.

    A PRISM is a subdivision of the 3-prism ([x220_prism3], two triangles joined
    by a perfect matching) in which the six TRIANGLE edges are left unsubdivided,
    so only the three matching edges become paths. *)

Definition x220_theta (H : sgraph) : Prop := is_subdivision_of H (KB 2 3).

Definition x220_prism3 : sgraph :=
  el_graph 6 [:: (0,1); (1,2); (0,2); (3,4); (4,5); (3,5); (0,3); (1,4); (2,5)].

Definition x220_prism (H : sgraph) : Prop :=
  exists m : subdiv_model x220_prism3 H,
    subdiv_rep m /\
    forall u v : x220_prism3,
      u -- v -> ((val u < 3) == (val v < 3)) -> sdm_path m u v = [::].

(** *** Wheels ************************************************************

    A WHEEL is a hole together with a vertex outside it having at least three
    neighbours on it; the wheel is EVEN when that number of spokes is even.
    [x220_even_wheel_free G] says no such configuration has an even number of
    spokes. *)

Definition x220_spokes (G : sgraph) (c : seq G) (v : G) : {set G} :=
  [set u : G | (u \in c) && (u -- v)].

Definition x220_even_wheel_free (G : sgraph) : Prop :=
  forall (v : G) (c : seq G),
    x27_hole c -> v \notin c -> 3 <= #|x220_spokes c v| -> odd #|x220_spokes c v|.

(** *** Clique-freeness and the subdivided claw S_{1,2,3} *****************)

(** No clique on [t] vertices (i.e. ['K_t]-free). *)
Definition x220_clique_free (G : sgraph) (t : nat) : Prop :=
  forall S : {set G}, clique S -> #|S| < t.

(** [S_{1,2,3}]: a centre with three legs of lengths 1, 2 and 3. *)
Definition x220_S123 : sgraph :=
  el_graph 7 [:: (0,1); (0,2); (2,3); (0,4); (4,5); (5,6)].

(** *** Induced biclique number *******************************************)

(** [t] is the induced biclique number of [G]: [G] has an induced ['K_t,t] and no
    induced ['K_s,s] with [s > t]. *)
Definition x220_ibn (G : sgraph) (t : nat) : Prop :=
  has_induced_copy G (KB t t) /\
  forall s : nat, has_induced_copy G (KB s s) -> s <= t.

(** *** Twin-width ********************************************************

    A [d]-contraction sequence, in its PARTITION presentation: the trigraph at
    each step is determined by the partition reached, two parts being joined by a
    RED edge when some but not all pairs between them are edges of [G].  The
    sequence starts at the partition into singletons, ends at a partition with at
    most one part, each step merges two parts, and every part always has at most
    [d] red neighbours. *)

Definition x220_red_pair (G : sgraph) (X Y : {set G}) : bool :=
  [exists x in X, exists y in Y, x -- y] && [exists x in X, exists y in Y, ~~ (x -- y)].

Definition x220_red_deg (G : sgraph) (P : {set {set G}}) (X : {set G}) : nat :=
  #|[set Y in P | (Y != X) && x220_red_pair X Y]|.

Definition x220_singletons (G : sgraph) : {set {set G}} := [set [set x] | x : G].

Definition x220_merge (G : sgraph) (P Q : {set {set G}}) : bool :=
  [exists X in P, exists Y in P, (X != Y) && (Q == (X :|: Y) |: (P :\ X :\ Y))].

Definition x220_twin_width_le (G : sgraph) (d : nat) : Prop :=
  exists s : seq {set {set G}},
    [/\ path (@x220_merge G) (x220_singletons G) s,
        #|last (x220_singletons G) s| <= 1 &
        forall P : {set {set G}},
          P \in (x220_singletons G :: s) ->
          forall X : {set G}, X \in P -> x220_red_deg P X <= d].

(** *** Graph classes: hereditary and small *******************************

    A CLASS is an isomorphism-closed predicate on finite simple graphs; it is
    HEREDITARY when closed under induced subgraphs.  It is SMALL when, for some
    constant [c] and every [n], it contains at most [n! c^n] graphs on the
    labelled vertex set ['I_n].  Labelled graphs are represented by their
    adjacency functions, and the count is phrased as a bound on the size of ANY
    set of such adjacency functions realised inside the class -- which avoids
    needing the class to be decidable. *)

Definition x220_iso_closed (C : sgraph -> Prop) : Prop :=
  forall G H : sgraph, C G -> diso G H -> C H.

Definition x220_hereditary_class (C : sgraph -> Prop) : Prop :=
  x220_iso_closed C /\ forall (G : sgraph) (S : {set G}), C G -> C (induced S).

Definition x220_represents (n : nat) (f : {ffun 'I_n * 'I_n -> bool}) (G : sgraph) : Prop :=
  exists h : 'I_n -> G, bijective h /\ forall x y : 'I_n, f (x, y) = (h x -- h y).

Definition x220_small_class (C : sgraph -> Prop) : Prop :=
  exists c : nat,
    forall (n : nat) (F : {set {ffun 'I_n * 'I_n -> bool}}),
      (forall f : {ffun 'I_n * 'I_n -> bool},
         f \in F -> exists2 G : sgraph, C G & x220_represents f G) ->
      #|F| <= n`! * c ^ n.

(** *** Shallow minors and polynomial expansion ***************************

    [H] is an [r]-SHALLOW MINOR of [G] when [H] is realised by pairwise disjoint
    branch sets each of radius at most [r] around a centre (paths measured INSIDE
    the branch set), the edges of [H] being realised by edges of [G] -- branch
    sets may of course be joined by further edges, since a shallow minor is a
    SUBGRAPH of the contraction.  A class has POLYNOMIAL EXPANSION when one
    polynomial bounds the edge density of all its shallow minors at every depth. *)

Definition x220_ball_in (G : sgraph) (B : {set G}) (c : G) (r : nat) : Prop :=
  forall v : G, v \in B ->
    exists p : seq G,
      [/\ path (--) c p, last c p = v, size p <= r & all (mem B) (c :: p)].

Definition x220_shallow_minor (G H : sgraph) (r : nat) : Prop :=
  exists (B : H -> {set G}) (ctr : H -> G),
    [/\ forall x : H, ctr x \in B x,
        forall x : H, x220_ball_in (B x) (ctr x) r,
        forall x y : H, x != y -> [disjoint B x & B y] &
        forall x y : H, x -- y -> exists u v : G, [/\ u \in B x, v \in B y & u -- v]].

Definition x220_poly_eval (p : seq nat) (x : nat) : nat :=
  foldr (fun a acc => a + x * acc) 0 p.

Definition x220_polynomial_expansion (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G ->
      forall (r : nat) (H : sgraph),
        x220_shallow_minor G H r -> #|E(H)| <= x220_poly_eval p r * #|H|.

(** *** Clique-width ******************************************************

    [k]-EXPRESSIONS over labelled graphs: a single labelled vertex, disjoint
    union, "add every edge between labels i and j" (i <> j), and "relabel i to
    j".  The vertices of an expression are its leaves in left-to-right order, so
    an expression denotes the label list [x220_cw_labels e] together with the
    adjacency [x220_cw_edge e] on positions; [x220_cw_wf k e] says only labels
    below [k] occur. *)

Inductive x220_cw_expr : Type :=
| CwLeaf of nat
| CwUnion of x220_cw_expr & x220_cw_expr
| CwJoin of nat & nat & x220_cw_expr
| CwRelab of nat & nat & x220_cw_expr.

Fixpoint x220_cw_labels (e : x220_cw_expr) : seq nat :=
  match e with
  | CwLeaf i => [:: i]
  | CwUnion a b => x220_cw_labels a ++ x220_cw_labels b
  | CwJoin _ _ a => x220_cw_labels a
  | CwRelab i j a => [seq (if l == i then j else l) | l <- x220_cw_labels a]
  end.

Fixpoint x220_cw_edge (e : x220_cw_expr) (x y : nat) : bool :=
  match e with
  | CwLeaf _ => false
  | CwUnion a b =>
      let n := size (x220_cw_labels a) in
      if (x < n) && (y < n) then x220_cw_edge a x y
      else if (n <= x) && (n <= y) then x220_cw_edge b (x - n) (y - n)
      else false
  | CwJoin i j a =>
      let L := x220_cw_labels a in
      x220_cw_edge a x y ||
      [&& x != y, x < size L, y < size L &
          ((nth 0 L x == i) && (nth 0 L y == j)) ||
          ((nth 0 L x == j) && (nth 0 L y == i))]
  | CwRelab _ _ a => x220_cw_edge a x y
  end.

Fixpoint x220_cw_wf (k : nat) (e : x220_cw_expr) : bool :=
  match e with
  | CwLeaf i => i < k
  | CwUnion a b => x220_cw_wf k a && x220_cw_wf k b
  | CwJoin i j a => [&& i < k, j < k, i != j & x220_cw_wf k a]
  | CwRelab i j a => [&& i < k, j < k & x220_cw_wf k a]
  end.

Definition x220_cw_realises (e : x220_cw_expr) (G : sgraph) : Prop :=
  exists f : G -> nat,
    [/\ injective f,
        forall v : G, f v < size (x220_cw_labels e),
        forall i : nat, i < size (x220_cw_labels e) -> exists v : G, f v = i &
        forall u v : G, (u -- v) = x220_cw_edge e (f u) (f v)].

Definition x220_clique_width_le (G : sgraph) (k : nat) : Prop :=
  exists e : x220_cw_expr, x220_cw_wf k e /\ x220_cw_realises e G.

(** ** X220 statements *****************************************************)

(** Corpus row: arxiv:2008.05504#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2008.05504__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2008.05504__01.json
    English statement: (Aboulker, Adler, Kim, Sintiari and Trotignon 2020, "On the tree-width
      of even-hole-free graphs", Conjecture 3)
      For every natural number d there is a function f from the naturals to the naturals such
      that every finite simple graph of maximum degree at most d whose treewidth is at least
      f(k) has an induced subgraph isomorphic to the k-by-k wall, or an induced subgraph
      isomorphic to the line graph of the k-by-k wall.
    Definitions: [Delta G] - maximum degree (base/theories/base.v); [tw_ge G r] - the treewidth
      of G is at least r, stated as a lower bound on every admissible width
      (minor-theory/theories/foundations/width_params.v); [x220_wall k] - the elementary k-by-k
      wall: the k-by-k grid on ['I_k * 'I_k] keeping every horizontal edge and the vertical
      edge from (i,j) to (i+1,j) exactly when i+j is even (this file);
      [sline_graph W] - the line graph of a simple graph W: its vertices are the edges of W,
      two of them adjacent when they share an endpoint
      (minor-theory/theories/foundations/containment.v); [has_induced_copy G H] - G has an
      induced subgraph isomorphic to H, i.e. an injective edge-reflecting map H -> G (the
      library's [isubgraph], same file).
    Notes: the function f depends on d and is quantified after d, as in the source ("for every
      d there is a function f_d").  "Treewidth at least f(k)" is stated negatively, as a lower
      bound on every width admitted by a tree decomposition, which avoids a minimum operator
      (the device of X201).  The wall is the elementary brick wall; the source's "(k x k)-wall"
      is this graph.  The corpus records this row as solved (Korhonen, JCTB 2023).
      Second reader (2026-09-23): [x220_wall k] has k rows and k columns, every vertex has at
      most one vertical incident edge (exactly one of [(i,j)-(i+1,j)] and [(i-1,j)-(i,j)] has
      its parity), so it is subcubic and its bounded faces are hexagonal bricks, as a wall
      must be.  Presentations of walls that index by the number of bricks rather than by rows
      and columns differ from this family only by a monotone reindexing of k, which the
      existentially quantified f absorbs, so the choice does not change the statement. *)
Definition bounded_degree_induced_wall_or_line_wall_statement : Prop :=
  forall d : nat, exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      Delta G <= d -> tw_ge G (f k) ->
      has_induced_copy G (x220_wall k) \/
      has_induced_copy G (sline_graph (x220_wall k)).

(** Corpus row: arxiv:2109.01310#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2109.01310__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2109.01310__00.json
    English statement: (Abrishami, Chudnovsky, Hajebi and Spirkl 2021, Conjecture 1.10)
      For every natural number t there is a constant c such that every finite simple graph G
      that has no induced complete graph on t vertices, no induced complete bipartite graph
      with both sides of size t, no induced subgraph isomorphic to a subdivision of the t-by-t
      wall and no induced subgraph isomorphic to the line graph of such a subdivision has
      treewidth at most c times one plus the base-2 logarithm of the number of vertices of G,
      rounded down.
    Definitions: [has_induced_copy G H] - G has an induced subgraph isomorphic to H
      (minor-theory/theories/foundations/containment.v); [is_subdivision_of W K] - W IS a
      subdivision of K: W carries a subdivision model of K that covers every vertex of W and
      whose subdivision paths carry every edge of W (same file); [x220_wall t] - the
      elementary t-by-t wall (this file); [sline_graph W] - the line graph of W
      (minor-theory/theories/foundations/containment.v); [tw_le G k] - treewidth at most k, a
      tree decomposition with all bags of size at most k+1
      (minor-theory/theories/foundations/width_params.v); ['K_t], ['K_t,t] ([KB t t]) - the
      complete and complete bipartite graphs (coq-graph-theory); [trunc_log 2 n] - the base-2
      logarithm rounded down (MathComp).
    Notes: the logarithmic envelope is [c * (trunc_log 2 #|G|).+1]; the successor absorbs the
      rounding of [trunc_log] so the bound is equivalent, up to the constant c which is
      existentially quantified, to the source's "tw(G) <= c log|V(G)|" (the device of X201).
      The four exclusions are INDUCED, as in the source.  Subdivisions of the wall are
      quantified as arbitrary graphs W that are subdivisions of the wall, rather than built by
      a subdivision operator, so that every subdivision pattern is covered. *)
Definition four_family_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G 'K_t ->
      ~ has_induced_copy G (KB t t) ->
      (forall W : sgraph, is_subdivision_of W (x220_wall t) -> ~ has_induced_copy G W) ->
      (forall W : sgraph, is_subdivision_of W (x220_wall t) ->
         ~ has_induced_copy G (sline_graph W)) ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

(** Corpus row: arxiv:2203.06775#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2203.06775__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2203.06775__00.json
    English statement: (Abrishami, Chudnovsky, Hajebi and Spirkl 2022, Conjecture 1.6)
      For every natural number t there is a constant c such that every finite simple graph
      with no induced four-cycle, no induced diamond, no induced theta, no induced prism, no
      even wheel and no clique on t vertices has treewidth at most c.
    Definitions: [has_induced_copy G H] - G has an induced subgraph isomorphic to H
      (minor-theory/theories/foundations/containment.v); [cycle_graph 4] - the four-cycle
      (base/theories/base.v); [x42_diamond] - the diamond, K4 minus an edge
      (minor-theory/theories/conjectures/X42.v); [x220_theta H] - H is a theta, i.e. a
      subdivision of the complete bipartite graph K_2,3, equivalently two vertices joined by
      three internally disjoint paths of length at least two (this file); [x220_prism H] - H is
      a prism, i.e. a subdivision of the 3-prism [x220_prism3] in which the six triangle edges
      are left unsubdivided, equivalently two disjoint triangles joined by three pairwise
      disjoint paths (this file); [x220_spokes c v] - the neighbours of v on the hole c, and
      [x220_even_wheel_free G] - every hole c and vertex v outside it with at least three
      neighbours on c has an ODD number of them (this file); [x220_clique_free G t] - every
      clique of G has fewer than t vertices (this file); [x27_hole c] - c is an induced cycle
      on more than three vertices (minor-theory/theories/conjectures/X27.v); [tw_le G c] -
      treewidth at most c (minor-theory/theories/foundations/width_params.v).
    Notes: the source's class C*_t is the (C_4, diamond, theta, prism, even wheel, K_t)-free
      class, all exclusions being INDUCED; pyramids are NOT excluded, which is what
      distinguishes C*_t from C_t.  Theta and prism are the three-path configurations
      3PC(x,y) and 3PC(triangle,triangle): they are encoded as subdivisions of K_2,3 and of
      the 3-prism, the latter with the triangle edges kept unsubdivided, which is exactly the
      usual definition.  A wheel is required to have at least three spokes; "even wheel-free"
      says every wheel has an odd number of spokes.
      Second reader (2026-09-23): the source's own definitions are finer than the
      sentence above.  There a WHEEL (H,w) is a hole H together with a vertex w having at
      least three PAIRWISE NONADJACENT neighbours on H, a LINE WHEEL is a hole together with
      a vertex whose neighbourhood on it is the union of two disjoint edges, and an EVEN WHEEL
      is a line wheel, or a wheel whose number of spokes is even.  [x220_even_wheel_free]
      forbids instead EVERY hole plus outside vertex whose number of spokes is even and at
      least three, which is a strictly different predicate on general graphs.  On the graphs
      this statement quantifies over the two agree exactly, so the encoded class is C*_t:
      given a hole H, a vertex v outside it and an even number k >= 4 of spokes, either the
      spokes contain three pairwise nonadjacent vertices, and (H,v) is a wheel with an even
      number of spokes, hence an even wheel; or they do not, and then they form at most two
      maximal arcs of H of length at most two each -- two disjoint edges, i.e. a line wheel --
      or a single arc of exactly four consecutive hole vertices, whose first three together
      with v induce a diamond and are therefore excluded by the diamond-free hypothesis (an
      arc of five or more vertices, and three or more arcs, always contain three pairwise
      nonadjacent spokes).  Conversely a line wheel has four spokes and a wheel has at least
      three, so both are caught by [x220_even_wheel_free].  Also: at t = 0 and t = 1 the
      [x220_clique_free] hypothesis is unsatisfiable resp. forces the empty graph, so those
      two instances are vacuous; the source quantifies over t > 0. *)
Definition theta_prism_even_wheel_free_bounded_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G (cycle_graph 4) ->
      ~ has_induced_copy G x42_diamond ->
      (forall H : sgraph, x220_theta H -> ~ has_induced_copy G H) ->
      (forall H : sgraph, x220_prism H -> ~ has_induced_copy G H) ->
      x220_even_wheel_free G ->
      x220_clique_free G t ->
      tw_le G c.

(** Corpus row: arxiv:2305.16258#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2305.16258__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2305.16258__01.json
    English statement: (Abrishami, Alecu, Chudnovsky, Hajebi and Spirkl 2023, Conjecture 1.7)
      For every natural number t there is a constant c such that every finite simple graph
      with no even hole and no clique on t vertices has treewidth at most c times one plus the
      base-2 logarithm of its number of vertices, rounded down.
    Definitions: [x27_even_hole_free G] - G has no induced cycle of even length on more than
      three vertices (minor-theory/theories/conjectures/X27.v); [x220_clique_free G t] - every
      clique of G has fewer than t vertices (this file); [tw_le G k] - treewidth at most k
      (minor-theory/theories/foundations/width_params.v); [trunc_log 2 n] - the base-2
      logarithm rounded down (MathComp).
    Notes: "logarithmic treewidth" for the class is read, as the class notes record, as one
      constant c per t with tw(G) <= c log|V(G)| for every member; the finite envelope is
      [c * (trunc_log 2 #|G|).+1], the successor absorbing the rounding of [trunc_log].  The
      corpus records this row as solved (Chudnovsky, Gartland, Hajebi, Lokshtanov and Spirkl,
      arXiv:2402.14211). *)
Definition even_hole_kt_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      x27_even_hole_free G -> x220_clique_free G t ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

(** Corpus row: arxiv:2305.16258#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2305.16258__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2305.16258__00.json
    English statement: (Abrishami, Alecu, Chudnovsky, Hajebi and Spirkl 2023, Conjecture 1.6)
      There is a constant k such that every finite simple graph with no even hole and no
      induced diamond has tree-independence number at most k.
    Definitions: [x27_even_hole_free G] - G has no induced cycle of even length on more than
      three vertices (minor-theory/theories/conjectures/X27.v); [x42_diamond] - the diamond,
      K4 minus an edge (minor-theory/theories/conjectures/X42.v); [has_induced_copy G H] - G
      has an induced subgraph isomorphic to H
      (minor-theory/theories/foundations/containment.v); [tree_alpha_le G k] - tree-independence
      number at most k: some tree decomposition has independence number at most k in every bag
      (minor-theory/theories/foundations/width_params.v).
    Notes: "bounded tree-alpha for the class" is one constant valid for every member, so the
      existential quantifier on k precedes the universal quantifier on G.  The corpus records
      this row as partial (the constant bound is known for the smaller pyramid-free
      subclass). *)
Definition even_hole_diamond_free_bounded_tree_alpha_statement : Prop :=
  exists k : nat,
    forall G : sgraph,
      x27_even_hole_free G -> ~ has_induced_copy G x42_diamond -> tree_alpha_le G k.

(** Corpus row: arxiv:2511.03864#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.03864__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.03864__00.json
    English statement: (Alon, Milanic and Rzazewski 2025, Question 5.2)
      For every positive natural number m there is a polynomial p with natural coefficients
      such that, for every natural number t, every finite simple graph with no induced complete
      bipartite subgraph with both sides of size t and with induced matching treewidth at most
      m has tree-independence number at most p(t).
    Definitions: [has_induced_copy G H] - G has an induced subgraph isomorphic to H
      (minor-theory/theories/foundations/containment.v); [tree_mu_le G m] - induced matching
      treewidth at most m: some tree decomposition bounds by m the size of every induced
      matching of G for which one bag contains at least one endpoint of each of its edges
      (minor-theory/theories/foundations/width_params.v); [induced_matching M] - a set of edges,
      pairwise disjoint, with no edge of G between the ends of two distinct members (same
      file); [tree_alpha_le G k] - tree-independence number at most k (same file);
      [x220_poly_eval p t] - Horner evaluation of the coefficient list p at t (this file);
      ['K_t,t] ([KB t t]) - the complete bipartite graph (coq-graph-theory).
    Notes: a polynomial is a list of NATURAL coefficients, evaluated by Horner's rule; this
      suffices for an upper bound.  The source's "K_{t,t}-free" is INDUCED-K_{t,t}-free, as
      the paper's own conventions section states.  The positivity hypothesis on m is kept as
      in the source.  Quantifier order: the polynomial depends on m only, not on t or G. *)
Definition tree_mu_ktt_free_polynomial_tree_alpha_statement : Prop :=
  forall m : nat, 0 < m ->
    exists p : seq nat,
      forall (t : nat) (G : sgraph),
        ~ has_induced_copy G (KB t t) ->
        tree_mu_le G m ->
        tree_alpha_le G (x220_poly_eval p t).

(** Corpus row: arxiv:2511.03864#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2511.03864__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2511.03864__01.json
    English statement: (Alon, Milanic and Rzazewski 2025, Question 5.3)
      For every natural number m there is a polynomial p with natural coefficients such that
      every finite simple graph whose induced matching treewidth is at most m and whose induced
      biclique number is t has tree-independence number at most p(t).
    Definitions: [tree_mu_le G m] - induced matching treewidth at most m
      (minor-theory/theories/foundations/width_params.v); [x220_ibn G t] - t is the induced
      biclique number of G: G has an induced complete bipartite subgraph with both sides of
      size t, and none with both sides of size larger than t (this file); [tree_alpha_le G k] -
      tree-independence number at most k
      (minor-theory/theories/foundations/width_params.v); [x220_poly_eval p t] - Horner
      evaluation of the coefficient list p at t (this file); [has_induced_copy G H] - G has an
      induced subgraph isomorphic to H
      (minor-theory/theories/foundations/containment.v).
    Notes: "classes of graphs with bounded induced matching treewidth" is modelled by the
      classes [fun G => tree_mu_le G m] for a fixed m, which are exactly the maximal such
      classes, so quantifying over m is equivalent to quantifying over all classes of bounded
      induced matching treewidth.  The induced biclique number is defined as in the source
      (the largest t with an induced K_{t,t}); it is a relational definition, so it carries its
      own maximality clause.  The corpus records an equivalent_to edge (e072) to row
      arxiv:2511.03864#00. *)
Definition bounded_tree_mu_polynomial_biclique_tree_alpha_statement : Prop :=
  forall m : nat,
    exists p : seq nat,
      forall (G : sgraph) (t : nat),
        tree_mu_le G m -> x220_ibn G t -> tree_alpha_le G (x220_poly_eval p t).

(** Corpus row: arxiv:2006.09877#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2006.09877__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2006.09877__00.json
    English statement: (Bonnet, Geniet, Kim, Thomasse and Watrigant 2020, "Twin-width II", the
      Small Conjecture)
      Every hereditary class of finite simple graphs that is small has bounded twin-width: if a
      class is closed under isomorphism and under induced subgraphs, and for some constant c
      contains at most n factorial times c to the n graphs on the labelled vertex set of size
      n for every n, then one number d bounds the twin-width of all its members.
    Definitions: [x220_iso_closed C] and [x220_hereditary_class C] - C is closed under
      isomorphism, and under taking induced subgraphs (this file); [x220_represents f G] - the
      adjacency function f on ['I_n] is the adjacency of G along some bijection, i.e. f is a
      labelling of G on n vertices (this file); [x220_small_class C] - for some c and every n,
      every set of adjacency functions on ['I_n] all of which label members of C has at most
      n! * c^n elements (this file); [x220_red_pair X Y] - some but not all pairs between the
      parts X and Y are edges, and [x220_red_deg P X] - the number of parts of P joined to X by
      a red pair (this file); [x220_merge P Q] - Q is obtained from P by merging two of its
      parts, and [x220_twin_width_le G d] - a sequence of merges from the partition into
      singletons down to at most one part, along which every part always has red degree at most
      d (this file).
    Notes: twin-width is presented by CONTRACTION SEQUENCES in their partition form: the
      trigraph reached after a sequence of contractions is determined by the partition of the
      vertex set, a pair of parts being red exactly when it is neither complete nor anticomplete,
      so no separate trigraph type is needed.  The sequence ends at a partition with at most one
      part, which also covers the empty graph.  Smallness counts LABELLED graphs, as in the
      source (not graphs up to isomorphism); it is stated as a bound on every set of adjacency
      functions realised in the class, which avoids requiring the class to be decidable.  The
      corpus records this row as DISPROVED (Bonnet, Geniet, Tessera and Thomasse,
      arXiv:2204.12330). *)
Definition small_hereditary_class_bounded_twin_width_statement : Prop :=
  forall C : sgraph -> Prop,
    x220_hereditary_class C -> x220_small_class C ->
    exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

(** Corpus row: arxiv:2006.09877#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2006.09877__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2006.09877__01.json
    English statement: (Bonnet, Geniet, Kim, Thomasse and Watrigant 2020, "Twin-width II", open
      question following the Small Conjecture)
      Every class of finite simple graphs with polynomial expansion has bounded twin-width: if
      one polynomial with natural coefficients bounds, for every member G, every depth r and
      every r-shallow minor H of G, the number of edges of H by that polynomial evaluated at r
      times the number of vertices of H, then one number d bounds the twin-width of all members
      of the class.
    Definitions: [x220_ball_in B c r] - every vertex of B is reachable from c by a walk of at
      most r steps staying inside B (this file); [x220_shallow_minor G H r] - H is an r-shallow
      minor of G: pairwise disjoint branch sets of radius at most r around centres, whose edges
      realise all edges of H (this file); [x220_poly_eval p r] - Horner evaluation of the
      coefficient list p at r (this file); [x220_polynomial_expansion C] - one such polynomial
      works for every member, depth and shallow minor (this file); [x220_twin_width_le G d] -
      twin-width at most d (this file); [E(H)] - the edge set of H (coq-graph-theory).
    Notes: polynomial expansion is the bounded greatest-reduced-average-density condition,
      stated as an edge-density bound on all shallow minors rather than through a maximum, so
      no maximum operator is needed.  A shallow minor is allowed to be a SUBGRAPH of the
      contraction (only the edges of H must be realised), as in the standard definition.  The
      polynomial has natural coefficients, which suffices for an upper bound. *)
Definition polynomial_expansion_bounded_twin_width_statement : Prop :=
  forall C : sgraph -> Prop,
    x220_polynomial_expansion C ->
    exists d : nat, forall G : sgraph, C G -> x220_twin_width_le G d.

(** Corpus row: arxiv:2001.01607#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2001.01607__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2001.01607__02.json
    English statement: (Pilipczuk, Sintiari, Thomasse and Trotignon 2020, open question)
      There is a natural number k such that every finite simple graph with no triangle and no
      induced subgraph isomorphic to the subdivided claw S(1,2,3) has clique-width at most k.
    Definitions: [triangle_free G] - no three pairwise adjacent vertices
      (base/theories/base.v); [x220_S123] - the subdivided claw S(1,2,3): a centre with three
      legs of lengths 1, 2 and 3, on seven vertices (this file); [has_induced_copy G H] - G has
      an induced subgraph isomorphic to H
      (minor-theory/theories/foundations/containment.v); [x220_cw_expr] - the syntax of
      k-expressions: a labelled vertex, disjoint union, adding all edges between two distinct
      labels, and relabelling (this file); [x220_cw_labels e] and [x220_cw_edge e] - the label
      list and the adjacency on positions denoted by an expression (this file);
      [x220_cw_wf k e] - every label occurring in e is below k, and each join uses two DISTINCT
      labels (this file); [x220_cw_realises e G] - a bijection between the vertices of G and
      the positions of e turning the adjacency of G into the adjacency denoted by e (this
      file); [x220_clique_width_le G k] - some well-formed k-expression realises G (this file).
    Notes: clique-width is presented by k-expressions over labelled graphs, the standard
      definition; the vertices of an expression are its leaves in left-to-right order, so the
      denotation of an expression is a label list plus an adjacency on positions, and a graph
      is realised when some bijection with the positions is an isomorphism.  S(1,2,3) has seven
      vertices; the claw would be S(1,1,1). *)
Definition triangle_s123_free_bounded_clique_width_statement : Prop :=
  exists k : nat,
    forall G : sgraph,
      triangle_free G -> ~ has_induced_copy G x220_S123 ->
      x220_clique_width_le G k.
