(** * Minor.conjectures.X147 -- v2 fat-minor/quasi-isometry row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X147 vocabulary ***********************************************)

(** The source's distances (arXiv:2509.09035 v2, l.100-103) are infinite between components, while
    [graph_dist] (GTBase) truncates at [#|G|] there; so every distance condition below is guarded by
    reachability, [connect (--)].  [x147_far c X Y]: dist_G(X, Y) > c, unreachable pairs counting as
    infinitely far. *)
Definition x147_far (G : sgraph) (c : nat) (X Y : {set G}) : Prop :=
  forall a b : G, a \in X -> b \in Y -> connect (--) a b -> c < graph_dist a b.

(** [G] contains [H] as a [c]-fat minor (l.115-125): branch sets for the vertices AND the edges of
    [H], non-null, connected (induced connectivity of the vertex set, GraphTheory's [connected]) and
    pairwise disjoint; each edge's set has an edge of [G] to the set of each of its two ends; every
    two sets are more than [c] apart except a vertex and an edge incident with it. *)
Definition x147_c_fat_minor (G H : sgraph) (c : nat) : Prop :=
  exists (etaV : H -> {set G}) (etaE : {set H} -> {set G}),
    [/\ forall h : H, etaV h != set0 /\ connected (etaV h),
        forall e : {set H}, e \in E(H) -> etaE e != set0 /\ connected (etaE e),
        [/\ forall h1 h2 : H, h1 != h2 -> [disjoint etaV h1 & etaV h2],
            forall e1 e2 : {set H}, e1 \in E(H) -> e2 \in E(H) -> e1 != e2 -> [disjoint etaE e1 & etaE e2]
          & forall (h : H) (e : {set H}), e \in E(H) -> [disjoint etaV h & etaE e]],
        forall u v : H, u -- v -> exists x y : G, [/\ x \in etaV u, y \in etaE [set u; v] & x -- y]
      & [/\ forall h1 h2 : H, h1 != h2 -> x147_far c (etaV h1) (etaV h2),
            forall e1 e2 : {set H}, e1 \in E(H) -> e2 \in E(H) -> e1 != e2 -> x147_far c (etaE e1) (etaE e2)
          & forall (h : H) (e : {set H}), e \in E(H) -> h \notin e -> x147_far c (etaV h) (etaE e)]].

(** [phi] is an (L,C)-quasi-isometry (l.105-113): ONE map with (i) the upper bound where dist_G is
    finite, (ii) the lower bound where dist_H is finite and (iii) a C-dense image; each "if the
    distance is finite then the bound" reads "reachable -> reachable and the bound", which is exact
    because a finite bound makes the distance finite. *)
Definition x147_quasi_isometry (G Q : sgraph) (L C : nat) (phi : G -> Q) : Prop :=
  [/\ forall u v : G, connect (--) u v ->
        connect (--) (phi u) (phi v) /\ graph_dist (phi u) (phi v) <= L * graph_dist u v + C,
      forall u v : G, connect (--) (phi u) (phi v) ->
        connect (--) u v /\ graph_dist u v <= L * graph_dist (phi u) (phi v) + C
    & forall y : Q, exists v : G, connect (--) (phi v) y /\ graph_dist (phi v) y <= C].

Definition x147_quasi_isometric_to_H_minor_free (G H : sgraph) (L C : nat) : Prop :=
  exists (Q : sgraph) (phi : G -> Q), ~ minor Q H /\ x147_quasi_isometry L C phi.

(** Sanity: a vertex is at distance 0 from itself; the identity is a (1,0)-quasi-isometry (the
    conclusion is satisfiable); sets in different components are far for every [c] (the infinity
    convention); the empty graph and a single vertex are c-fat minors of every graph (of every
    nonempty graph); an edge is NOT a c-fat minor of an edge (three disjoint nonempty sets do not fit
    on two vertices), so fatness has teeth even for [c = 0]. *)
Lemma x147_graph_dist_refl (G : sgraph) (x : G) : graph_dist x x = 0.
Proof.
rewrite /graph_dist; case: ex_minnP => m hm hmin.
apply/eqP; rewrite -leqn0; apply: hmin.
by rewrite /= inE eqxx.
Qed.

Lemma x147_id_quasi_isometry (G : sgraph) : x147_quasi_isometry 1 0 (@id G).
Proof.
split.
- by move=> u v huv; rewrite mul1n addn0.
- by move=> u v huv; rewrite mul1n addn0.
- by move=> y; exists y; rewrite connect0 x147_graph_dist_refl.
Qed.

Lemma x147_far_unreachable (G : sgraph) (c : nat) (X Y : {set G}) :
  (forall a b : G, a \in X -> b \in Y -> ~~ connect (--) a b) -> x147_far c X Y.
Proof.
by move=> h a b ha hb hab; move: (h a b ha hb); rewrite hab.
Qed.

Lemma x147_K0_fat_minor (G : sgraph) (c : nat) : x147_c_fat_minor G 'K_0 c.
Proof.
exists (fun _ => set0), (fun _ => set0); split;
  [by case=> [[]] | by move=> e /edgesP [[[] //]] | split => [[[]]//|e1 e2 /edgesP [[[] //]]|[[]]//] | by case=> [[]] |
   split => [[[]]//|e1 e2 /edgesP [[[] //]]|[[]]//]].
Qed.

Lemma x147_K1_fat_minor (G : sgraph) (c : nat) (x0 : G) : x147_c_fat_minor G 'K_1 c.
Proof.
have noedge : forall e : {set 'K_1}, e \in E('K_1) -> False.
  by move=> e /edgesP [x [y [_]]]; rewrite (ord1 x) (ord1 y).
have noadj : forall (u v : 'K_1), u -- v -> False by move=> u v; rewrite (ord1 u) (ord1 v).
have nodiff : forall (h1 h2 : 'K_1), h1 != h2 -> False by move=> h1 h2; rewrite (ord1 h1) (ord1 h2) eqxx.
exists (fun _ => [set x0]), (fun _ => set0); split.
- by move=> h; split; [apply/set0Pn; exists x0; rewrite inE | exact: connected1].
- by move=> e /noedge.
- by split=> [h1 h2 /nodiff|e1 e2 /noedge|h e /noedge].
- by move=> u v /noadj.
- by split=> [h1 h2 /nodiff|e1 e2 /noedge|h e /noedge].
Qed.

Lemma x147_K2_not_fat_minor_K2 (c : nat) : ~ x147_c_fat_minor 'K_2 'K_2 c.
Proof.
move=> [etaV [etaE [hV hE [dVV _ dVE] _ _]]].
pose e : {set 'K_2} := [set ord0; ord_max].
have he : e \in E('K_2) by rewrite in_edges.
have [a ha] := set0Pn _ (hV ord0).1.
have [b hb] := set0Pn _ (hV ord_max).1.
have [x hx] := set0Pn _ (hE e he).1.
have ab : a != b.
  by apply/eqP => eab; move: (disjointFr (dVV ord0 ord_max isT) ha); rewrite eab hb.
have ax : a != x.
  by apply/eqP => eax; move: (disjointFr (dVE ord0 e he) ha); rewrite eax hx.
have bx : b != x.
  by apply/eqP => ebx; move: (disjointFr (dVE ord_max e he) hb); rewrite ebx hx.
move: ab ax bx; case: a {ha} => [[|[|?]] ?] //; case: b {hb} => [[|[|?]] ?] //; case: x {hx} => [[|[|?]] ?] //.
Qed.

(** ** X147 statements *****************************************************)

(** Corpus row: studies:std_georgakopoulos_papasoglu_conjecture_fat_minors
    Site: none
    Review: none
    English statement: (Georgakopoulos and Papasoglu, conjecture on fat minors, as stated in
      arXiv:2509.09035, l.138-140)
      For every finite simple graph H and every integer c >= 0 there are L, C >= 0 such that every
      finite simple graph G that does not contain H as a c-fat minor admits an (L,C)-quasi-
      isometry to a graph with no H minor.
    Definitions: [x147_c_fat_minor G H c] - branch sets of G for the vertices and the edges of H,
      non-null, connected (induced connectivity of each vertex set), pairwise disjoint, each edge's
      set joined by an edge of G to the sets of both its ends, every two of them more than c apart
      except a vertex and an edge incident with it (this file); [x147_far G c X Y] - every
      reachable pair from X and Y is more than c apart (this file); [x147_quasi_isometry L C phi]
      - one map with the upper and the lower bound on reachable pairs and a C-dense image (this
      file); [x147_quasi_isometric_to_H_minor_free G H L C] - some graph Q with no H minor and an
      (L,C)-quasi-isometry from G to Q (this file); [minor Q H] - GraphTheory's minor;
      [graph_dist x y] - the graph metric, truncated at the number of vertices for unreachable
      pairs (base/theories/graph_metric.v), used only on reachable pairs here; [connect (--)] -
      reachability.
    Notes: PARTIAL: finite graphs only; the source allows infinite graphs (v2 l.98), and the
      finite statement follows from the source's but is not known to be equivalent to it.
      RE-ENCODED 2026-10-26 (coordination/PROGRAMME.md A1; record meta/STATEMENT_IMPROVEMENTS.md;
      the row is frozen by no migration family; Lancelot's routing and Marcol's design review,
      2026-10-26).  The earlier body had two decoupled maps with upper bounds only where the source
      has one map with the lower bound and a dense image; branch sets for the vertices of H only,
      adjacent ones touching, where the source has branch sets for edges too and every pair apart
      but a vertex and an incident edge; and the truncated distance where the source has infinity.
      The source (arXiv:2509.09035 v2, the pin's version, e-print sha256 ced7846b, as3.tex sha256
      2b46754a): l.105-113 the quasi-isometry, l.115-125 the c-fat minor; v4 (sha256 c39407c6)
      l.129-136 makes explicit that each edge's set touches the sets of both its ends.  A finite G
      loses nothing by a finite target: given an H-minor-free Q and an (L,C)-quasi-isometry, keep the
      image, one shortest Q-path between every two image points and, for each vertex on them, a
      path of length <= C to the image; that finite subgraph of Q has the same distances between
      image points, a C-dense image, and no H minor.  Natural L, C are equivalent to the source's
      real ones, every bound being monotone.  The source itself states this conjecture as a "False
      conjecture" (l.138-140): Davies, Hickingbotham, Illingworth and McCarty disproved it in general
      with an H containing a K_15 (l.148-150), and v4 (l.233-237) adds the octahedron
      (Albrechtsen, Distel and Georgakopoulos); these are recorded as the source's statements, the
      row's upstream status remaining open. *)
Definition georgakopoulos_papasoglu_fat_minor_quasi_isometry_statement : Prop :=
  forall (H : sgraph) (c : nat),
    exists L C : nat,
      forall G : sgraph,
        ~ x147_c_fat_minor G H c ->
        x147_quasi_isometric_to_H_minor_free G H L C.
