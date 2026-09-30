(** * Cycle.foundations.connectivity — shared multigraph connectivity vocabulary

    The GENERAL (carrier-agnostic) multigraph CONNECTIVITY layer of cycle theory,
    factored out of the conjecture files U6 / U10 / D1 (which all rebuilt the same
    primitives independently).  Everything here is plain [mgraph] vocabulary built
    on top of base's edge/walk API ([edges_at], [incident], [source]/[target],
    [uwalk]); no flow-, cycle-cover-, face- or D1-specific notions
    live here (those stay in their conjecture files).

    Contents (dependency-ordered):
      - degrees:        [ends_at], [subdeg], [mdeg], [subgraph_kregular];
      - connectivity:   [walk_in], [mconnected], [connected_del_edges],
                        [connected_del_verts], [two_connected], [edge_connected],
                        [H_inc], [subgraph_connected];
      - circuits:       [is_circuit];
      - cuts / bridges: [cut], [uwalk_cons], [uwalk_one], [ueseparates], [is_bridge],
                        [bridgeless], [uwalk_crosses];
      - 2-edge-conn.:   [two_edge_connected].

    CARRIER CONVENTION (undirected multigraphs).  Throughout cycle-theory an
    [mgraph] ENCODES an UNDIRECTED multigraph: each undirected edge is carried by
    exactly ONE arc, and the [source]/[target] split of that arc is a reference
    orientation with no mathematical content.  Every notion defined here (and in
    U6 / U10 / D1 / X212 / X228 on top of it) must therefore be invariant under
    reversing an arc:
      - degrees ([subdeg], [mdeg]) count ARC ENDS at the vertex, which is
        symmetric in [source]/[target] AND gives a loop the textbook degree 2 —
        and [subgraph_kregular], [U6.even_subgraph], [U6.two_factor],
        [U6.is_matching], [U6.cubic], [U10.is_perfect_matching] inherit both
        properties.  [edges_at]/[incident] are symmetric too but count a loop
        ONCE, so they are NOT a degree; they survive only where an incidence
        set, not a degree, is meant ([H_inc], [U6.transition2_system]);
      - [cut S] is an exclusive-or of the two endpoints, hence symmetric;
      - connectivity ([mconnected], [walk_in], [connected_del_edges],
        [connected_del_verts], [subgraph_connected], [is_circuit]) goes through
        base's [uwalk], which traverses each arc in EITHER direction;
      - bridges go through [ueseparates] below, the [uwalk] analogue of
        coq-graph-theory's [eseparates].
    The one place where a DIRECTED reading would silently be wrong is
    [mgraph.edges x y] = [set e | (source e == x) && (target e == y)], which
    counts arcs in ONE direction only: an undirected multiplicity between [x]
    and [y] must always be read as [#|edges x y| + #|edges y x|] (this is what
    [U6.simple_mgraph] does).  The single DELIBERATE exception in the package is
    [U6.is_eulerian_tour], which keeps coq-graph-theory's directed [walk]; that
    reading is argued for in the doc block of the row that uses it.

    IMPORT ORDER: [mgraph] is imported BEFORE [base], because coq-graph-theory's
    [mgraph] ships a DIRECTED [line_graph] that would otherwise shadow base's
    undirected one (base re-exports the line/total-graph vocabulary).  [base]
    provides the [mgraph] notation ([graph unit unit]), [uwalk], [edges_at],
    [incident], [source]/[target]. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Degrees and subgraph degrees

    TEXTBOOK (undirected) degree: we count ARC ENDS at [v], not edges incident
    with [v], so a LOOP contributes 2.  Counting incident edges ([edges_at])
    would give a loop degree 1 and break the classical facts that a single loop
    is a circuit of length 1 and an element of the cycle space, and that the
    degree sum is twice the number of edges.  The count is symmetric in
    [source]/[target] (reversing an arc swaps its two contributions), as the
    carrier convention above demands.  On a LOOPLESS carrier it agrees with the
    incidence count, [subdeg_loopless] below. *)

(** The [H]-edges whose [b]-end is [v] ([b = false]: [source], [b = true]:
    [target]).  [subdeg] adds the two. *)
Definition ends_at (G : mgraph) (H : {set edge G}) (b : bool) (v : G)
    : {set edge G} :=
  [set e in H | endpoint b e == v].

(** Degree of [v] inside the subgraph given by edge set [H]: its number of
    [H]-arc-ends, so a loop of [H] at [v] counts twice. *)
Definition subdeg (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|ends_at H false v| + #|ends_at H true v|.

(** Multigraph degree of [v]: its degree in the whole edge set. *)
Definition mdeg (G : mgraph) (v : G) : nat := subdeg [set: edge G] v.

(** [incident] spelled out on the two ends. *)
Lemma incidentE (G : mgraph) (v : G) (e : edge G) :
  incident v e = (source e == v) || (target e == v).
Proof.
rewrite /incident; apply/existsP/orP => [[b hb]|].
- by case: b hb => hb; [right | left].
- by case=> h; [exists false | exists true].
Qed.

Lemma ends_atU (G : mgraph) (H : {set edge G}) (v : G) :
  ends_at H false v :|: ends_at H true v = edges_at v :&: H.
Proof. by apply/setP => e; rewrite !inE -andb_orr incidentE andbC. Qed.

(** A LOOP of [H] at [v] is the only edge in both halves. *)
Lemma ends_atI (G : mgraph) (H : {set edge G}) (v : G) :
  ends_at H false v :&: ends_at H true v
  = [set e in H | (source e == v) && (target e == v)].
Proof. by apply/setP => e; rewrite !inE andbACA andbb. Qed.

(** Degree = incidences + loops: the "a loop counts twice" identity. *)
Lemma subdegE (G : mgraph) (H : {set edge G}) (v : G) :
  subdeg H v
  = #|edges_at v :&: H| + #|[set e in H | (source e == v) && (target e == v)]|.
Proof. by rewrite /subdeg -cardsUI ends_atU ends_atI. Qed.

(** On a loopless carrier the two conventions agree. *)
Lemma subdeg_loopless (G : mgraph) (H : {set edge G}) (v : G) :
  loopless G -> subdeg H v = #|edges_at v :&: H|.
Proof.
move=> ll; rewrite subdegE.
suff -> : [set e in H | (source e == v) && (target e == v)] = set0.
  by rewrite cards0 addn0.
apply/setP => e; rewrite !inE andbC.
case: (boolP ((source e == v) && (target e == v))) => // /andP[/eqP se /eqP te].
by move: (ll e); rewrite se te eqxx.
Qed.

Lemma mdeg_loopless (G : mgraph) (v : G) :
  loopless G -> mdeg v = #|edges_at v|.
Proof. by move=> ll; rewrite /mdeg (subdeg_loopless _ _ ll) setIT. Qed.

(** The [b]-half of a single-edge set is that set when [e]'s [b]-end is [v]. *)
Lemma ends_at1 (G : mgraph) (e : edge G) (b : bool) (v : G) :
  endpoint b e = v -> ends_at [set e] b v = [set e].
Proof.
move=> he; apply/setP => f; rewrite !inE.
case E: (f == e) => //=.
by move/eqP: E => ->; rewrite he eqxx.
Qed.

(** A loop at [v] contributes 2 to [v]'s degree. *)
Lemma subdeg_loop (G : mgraph) (e : edge G) (v : G) :
  source e = v -> target e = v -> subdeg [set e] v = 2.
Proof.
move=> se te; rewrite /subdeg.
by rewrite (@ends_at1 _ e false v se) (@ends_at1 _ e true v te) cards1.
Qed.

(** Monotonicity, the empty and the full edge set. *)
Lemma ends_at_sub (G : mgraph) (H K : {set edge G}) (b : bool) (v : G) :
  H \subset K -> ends_at H b v \subset ends_at K b v.
Proof.
move=> /subsetP sHK; apply/subsetP => e.
by rewrite !inE => /andP[/sHK -> ->].
Qed.

Lemma subdeg_sub (G : mgraph) (H K : {set edge G}) (v : G) :
  H \subset K -> (subdeg H v <= subdeg K v)%N.
Proof. by move=> sHK; rewrite leq_add // subset_leq_card // ends_at_sub. Qed.

Lemma subdeg_mdeg (G : mgraph) (H : {set edge G}) (v : G) :
  (subdeg H v <= mdeg v)%N.
Proof. by rewrite /mdeg subdeg_sub // subsetT. Qed.

Lemma subdeg0 (G : mgraph) (v : G) : subdeg (@set0 (edge G)) v = 0.
Proof.
rewrite /subdeg; suff e0 : forall b, ends_at (@set0 (edge G)) b v = set0.
  by rewrite !e0 cards0.
by move=> b; apply/setP => e; rewrite !inE.
Qed.

(** A vertex of positive degree witnesses an edge. *)
Lemma mdeg_gt0_edge (G : mgraph) (v : G) :
  (0 < mdeg v)%N -> (0 < #|edge G|)%N.
Proof.
rewrite /mdeg /subdeg addn_gt0 -cardsT.
by case/orP => /card_gt0P[e _]; apply/card_gt0P; exists e; rewrite inE.
Qed.

(** [k]-regular subgraph: every vertex has [H]-degree [0] or [k]
    (so its support is a disjoint union of [k]-regular pieces). *)
Definition subgraph_kregular (G : mgraph) (H : {set edge G}) (k : nat) : Prop :=
  forall v : G, subdeg H v = 0 \/ subdeg H v = k.

(** ** Connectivity at the multigraph level (via [uwalk]) *)

(** Walk restricted to edges of [H]. *)
Definition walk_in (G : mgraph) (H : {set edge G}) (x y : G) (w : seq (edge G)) : bool :=
  uwalk x y w && all (fun e => e \in H) w.

(** Whole-graph (vertex) connectivity. *)
Definition mconnected (G : mgraph) : Prop :=
  forall x y : G, exists w, uwalk x y w.

(** Connectivity using only edges OUTSIDE the edge set [S] (i.e. of [G - E(S)]). *)
Definition connected_del_edges (G : mgraph) (S : {set edge G}) : Prop :=
  forall x y : G, exists w, uwalk x y w /\ all (fun e => e \notin S) w.

(** Connectivity after deleting the vertex set [Z] (walks avoiding [Z]). *)
Definition connected_del_verts (G : mgraph) (Z : {set G}) : Prop :=
  forall x y : G, x \notin Z -> y \notin Z ->
    exists w, uwalk x y w /\ all (fun e => (source e \notin Z) && (target e \notin Z)) w.

(** 2-(vertex-)connected: at least 3 vertices, and connected after deleting any one. *)
Definition two_connected (G : mgraph) : Prop :=
  (3 <= #|G|)%N /\ forall z : G, connected_del_verts [set z].

(** [k]-edge-connected: deleting fewer than [k] edges keeps the graph connected. *)
Definition edge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, (#|E| < k)%N -> connected_del_edges E.

(** A subgraph [H] is incident at [x]: some [H]-edge meets [x]. *)
Definition H_inc (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].

(** A subgraph [H] is connected: any two [H]-incident vertices are joined by an
    [H]-walk. *)
Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, H_inc H x -> H_inc H y -> exists w, walk_in H x y w.

(** ** Circuits *)

(** A circuit (single cycle): a nonempty, connected, 2-regular edge set. *)
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** ** Edge cuts and bridges *)

(** The edge cut of a vertex set [S]: edges with exactly one endpoint in [S]. *)
Definition cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** UNDIRECTED edge separator: every UNDIRECTED walk from [x] to [y] meets [E].
    This is coq-graph-theory's [eseparates] with the DIRECTED [walk] replaced by
    base's [uwalk] (each arc traversable in either direction) — the fix of the
    [source]->[target] bias, per the carrier convention above. *)
Definition ueseparates (G : mgraph) (x y : G) (E : {set edge G}) : Prop :=
  forall w : seq (edge G), uwalk x y w -> exists2 f, f \in E & f \in w.

(** [e] is a bridge (= a CUT EDGE): every UNDIRECTED walk between its endpoints
    uses [e]; equivalently, [e] is not on any cycle and deleting it separates
    its two endpoints.  A loop is never a bridge (the empty walk joins its
    endpoints). *)
Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  ueseparates (source e) (target e) [set e].

Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ is_bridge e.

(** Prepending one edge to an undirected walk, in either reference direction. *)
Lemma uwalk_cons (G : mgraph) (x y : G) (f : edge G) (w : seq (edge G)) :
  source f = x -> uwalk (target f) y w -> uwalk x y (f :: w).
Proof. by move=> <- h; rewrite /= eqxx h. Qed.

Lemma uwalk_cons_rev (G : mgraph) (x y : G) (f : edge G) (w : seq (edge G)) :
  target f = x -> uwalk (source f) y w -> uwalk x y (f :: w).
Proof. by move=> <- h; rewrite /= eqxx h orbT. Qed.

(** One-edge undirected walks (either reference direction). *)
Lemma uwalk_one (G : mgraph) (x y : G) (f : edge G) :
  source f = x -> target f = y -> uwalk x y [:: f].
Proof. by move=> <- <-; rewrite /= !eqxx. Qed.

Lemma uwalk_one_rev (G : mgraph) (x y : G) (f : edge G) :
  target f = x -> source f = y -> uwalk x y [:: f].
Proof. by move=> <- <-; rewrite /= !eqxx orbT. Qed.

(** Unfolding lemma: a bridge is an edge on every undirected walk between its
    endpoints. *)
Lemma is_bridgeP (G : mgraph) (e : edge G) :
  is_bridge e <-> (forall w : seq (edge G), uwalk (source e) (target e) w -> e \in w).
Proof.
split=> [br w wk|h w wk]; last by exists e; rewrite ?inE ?h.
by have [f]:= br w wk; rewrite inE => /eqP ->.
Qed.

(** The working criterion for NON-bridges: an undirected detour avoiding [e]. *)
Lemma not_bridge_detour (G : mgraph) (e : edge G) (w : seq (edge G)) :
  uwalk (source e) (target e) w -> e \notin w -> ~ is_bridge e.
Proof. by move=> wk /negP ne /is_bridgeP/(_ w wk). Qed.

(** A loop is never a bridge. *)
Lemma loop_not_bridge (G : mgraph) (e : edge G) :
  source e = target e -> ~ is_bridge e.
Proof. by move=> st; apply: (not_bridge_detour (w := [::])); rewrite //= st eqxx. Qed.

(** CROSSING LEMMA: an undirected walk between two vertices separated by [S]
    must use an edge of the cut [cut S].  (Used by [implications_U6] to turn
    bridgelessness into "every cut around an edge has size at least two".) *)
Lemma uwalk_crosses (G : mgraph) (S : {set G}) (w : seq (edge G)) (x y : G) :
  uwalk x y w -> (x \in S) != (y \in S) ->
  exists2 f, f \in w & f \in cut S.
Proof.
elim: w x y => [|e w IH] x y /=; first by move=> /eqP <-; rewrite eqxx.
have main (a b : G) : a = x -> uwalk b y w ->
    ((a \in S) (+) (b \in S)) = ((source e \in S) (+) (target e \in S)) ->
    (x \in S) != (y \in S) ->
    exists2 f, f \in e :: w & f \in cut S.
  move=> ax Hw Hab Hne.
  case Hcmp: ((b \in S) == (x \in S)).
  - have Hne' : (b \in S) != (y \in S) by rewrite (eqP Hcmp).
    have [f Hfw Hfc] := IH b y Hw Hne'.
    by exists f => //; rewrite inE Hfw orbT.
  - exists e; first by rewrite inE eqxx.
    rewrite inE -Hab ax.
    by move/negbT: Hcmp; case: (x \in S); case: (b \in S).
move=> /orP[] /andP[/eqP Hs Hw] Hne.
- exact: (main (source e) (target e)).
- by apply: (main (target e) (source e)) => //; rewrite addbC.
Qed.

(** ** Two-edge-connectivity *)

(** 2-edge-connected = connected and bridgeless. *)
Definition two_edge_connected (G : mgraph) : Prop :=
  mconnected G /\ bridgeless G.
