(** * Digraph.conjectures.two_extremal — P12: the 2-extremal characterization

    The hardest P12 cluster: Aboulker–Aubian–Charbit, "Digraph Colouring and
    Arc-Connectivity" (arXiv:2304.04690), §9.  A digraph is [k_extremal] when it is
    strong, loopless, its underlying graph is 2-connected, and its dichromatic
    number meets the arc-connectivity bound  χ⃗(D) = λ(D) + 1 = k+1  (the bound
    χ⃗(D) ≤ λ(D)+1 ≤ Δ_max(D)+1 of Neumann-Lara holds always; "extremal" = equality).
    [two_extremal] is [k_extremal] at k = 2.  This file STATES (does not prove):

      1. the building blocks: underlying simple graph of a loopless digraph
         ([underlyingG]), the digon graph ([digonG], spanning subgraph of digon
         edges), self-contained 2-connectivity ([two_connected_sg]), max local
         arc-connectivity λ(D) via minimum dicuts ([local_arc_conn] / [arc_conn]),
         and the χ⃗ machinery reused from [dichromatic] ([chi_vec_eq]);
         then [k_extremal] and [two_extremal];
      2. CONJECTURE-P : every 2-extremal digraph has PLANAR underlying graph,
         planarity via Wagner ([planar_sg] = no [sg_minor] of ['K_5] / ['K_3,3]);
      3. the 3-connected / generalised-wheel reduction statements: the digon graph
         is a forest, the no-digon-free-cut (= digon graph spanning-tree) crux,
         the H6 "no full cover" 2-dicolourability lemma, and
         [three_connected_generalised_wheel];
      4. the directed Hajós join construction ([dhajos], Def 1.5 — faithful: delete
         uv₁, v₂w, identify v₁=v₂, add uw) and the symmetric odd cycle base; and
         Conjecture 9.2 itself, [conj_9_2], stated modulo an abstract
         [in_H2 : diGraphType -> Prop] (the 2-Hajós tree join / Def 9.1 plane-tree +
         even-B-parity machinery is the BLOCKED piece — see notes), together with
         the implication edges  9.2 ⟹ CONJECTURE-P  and  9.2 ⟹ the 3-connected case.

    All degenerate cases are guarded: [k_extremal] forces looplessness (so the
    underlying graph is a genuine [sgraph]) and strongness/2-connectivity which give
    [0 < #|D|].  See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P12) and the team docs
    problems/two_extremal_digraphs/docs/{planarity_of_2extremal,three_connected_wheel,
    no_full_cover_lemma,conditional_l_literature}.md for the verbatim definitions. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Looplessness *)

(** A digraph is loopless when it has no loop [v --> v].  This is the standing
    assumption of the whole paper ("loopless digraph, digons allowed"); it is what
    makes the underlying simple graph well-defined. *)
Definition loopless (D : diGraphType) : Prop := irreflexive (@arc D).

(** ** Underlying simple graph of a loopless digraph

    Forget arc directions: [u] and [v] are adjacent iff [u --> v] or [v --> u].
    Building an [sgraph] requires irreflexivity, supplied by a looplessness proof. *)

Section Underlying.
Variable D : diGraphType.

Definition uADJ : rel D := fun u v => (u --> v) || (v --> u).
Fact uADJ_sym : symmetric uADJ.
Proof. by move=> u v; rewrite /uADJ orbC. Qed.
Lemma uADJ_irr (llD : loopless D) : irreflexive uADJ.
Proof. by move=> u; rewrite /uADJ (llD u). Qed.

(** The underlying [sgraph] [U(D)] of the loopless digraph [D]. *)
Definition underlyingG (llD : loopless D) : sgraph :=
  SGraph uADJ_sym (uADJ_irr llD).

(** ** Digon graph [F_D]

    The spanning subgraph of [U(D)] keeping exactly the DIGON edges: [u] and [v]
    are [F_D]-adjacent iff both [u --> v] and [v --> u].  (Same vertex set as [D].) *)

Definition digonADJ : rel D := fun u v => (u --> v) && (v --> u).
Fact digonADJ_sym : symmetric digonADJ.
Proof. by move=> u v; rewrite /digonADJ andbC. Qed.
Lemma digonADJ_irr (llD : loopless D) : irreflexive digonADJ.
Proof. by move=> u; rewrite /digonADJ (llD u). Qed.

Definition digonG (llD : loopless D) : sgraph :=
  SGraph digonADJ_sym (digonADJ_irr llD).

End Underlying.

(** ** Self-contained 2-connectivity of a simple graph

    [G] is 2-connected when it has at least 3 vertices, is connected, and has no
    cut-vertex (deleting any single vertex keeps it connected).  We use graph-theory's
    subset-relative [connected]; [G − v] is [connected [set~ v]].  (graph-theory's own
    [kconnected] lives in a module the interop does not re-export, so we re-state it.) *)

Definition two_connected_sg (G : sgraph) : Prop :=
  [/\ (2 < #|G|)%N,
      connected [set: G]
    & forall v : G, connected [set~ v]].

(** ** Maximum local arc-connectivity λ(D)

    For a vertex set [S], [outcut S] is the number of arcs leaving [S] (from [S] to
    its complement).  The local arc-connectivity λ(u,v) — by Menger, the maximum
    number of arc-disjoint directed u→v paths — equals the minimum size of a u-v
    DICUT: the least [outcut S] over [S] with [u ∈ S], [v ∉ S].  λ(D) is the maximum
    of λ(u,v) over ordered pairs [u ≠ v] (the paper's "maximum local
    arc-connectivity", p.7). *)

Section ArcConnectivity.
Variable D : diGraphType.
Implicit Types (u v : D) (S : {set D}).

(** Number of arcs from [S] to its complement (the dicut [δ⁺(S)]). *)
Definition outcut S : nat :=
  #|[set p : D * D | [&& p.1 \in S, p.2 \notin S & p.1 --> p.2]]|.

(** [S] separates [u] from [v]: a u-v dicut. *)
Definition uv_dicut u v S : bool := (u \in S) && (v \notin S).

(** Local arc-connectivity λ(u,v) = minimum dicut size over u-v separators.
    For [u ≠ v] the family of separators is non-empty ([S = [set u]] works), and the
    cap [#|D * D|.+1] dominates every [outcut S] (which counts ⊆ all ordered pairs),
    so the [\big[minn/_]] yields exactly the genuine minimum. *)
Definition local_arc_conn u v : nat :=
  \big[minn/(#|{: D * D}|.+1)]_(S in [set S0 : {set D} | uv_dicut u v S0]) outcut S.

(** Maximum local arc-connectivity λ(D) over ordered distinct pairs. *)
Definition arc_conn : nat :=
  \max_(p in [set q : D * D | q.1 != q.2]) local_arc_conn p.1 p.2.

End ArcConnectivity.

(** ** Exact dichromatic number χ⃗(D) = m (via [dicolorableb])

    [dicolorableb D k] is "χ⃗(D) ≤ k".  Equality χ⃗(D) = m (for [m ≥ 1]) is
    "m-dicolourable but not (m-1)-dicolourable". *)
Definition chi_vec_eq (D : diGraphType) (m : nat) : Prop :=
  (0 < m)%N /\ dicolorableb D m /\ ~~ dicolorableb D m.-1.

(** ** k-extremal and 2-extremal

    [k_extremal llD D k]  (paper, p.7, l.178-182, verbatim): [D] is strong, its
    underlying graph is 2-connected, and χ⃗(D) = λ(D) + 1 = k+1.  Looplessness is
    threaded as the EXPLICIT argument [llD : loopless D] (standing paper hypothesis,
    and required to form [underlyingG]); this lets statements use [underlyingG llD]
    without eliminating an existential into [Type].  All degeneracies are guarded:
    2-connectivity forces [2 < #|D|]. *)
Definition k_extremal (D : diGraphType) (llD : loopless D) (k : nat) : Prop :=
  [/\ strongb D,
      two_connected_sg (underlyingG llD),
      arc_conn D = k
    & chi_vec_eq D k.+1].

(** 2-extremal = k-extremal at k = 2. *)
Definition two_extremal (D : diGraphType) (llD : loopless D) : Prop :=
  k_extremal llD 2.

(** ** Planarity (Wagner): no ['K_5] and no ['K_3,3] minor

    Self-contained graph-minor relation (graph-theory's [minor_rmap]; its [minor]
    module is not re-exported).  A [sg_minor_rmap] is a branch-set assignment: to each
    vertex of [H] a non-empty connected vertex set of [G], pairwise disjoint, with a
    [G]-edge between the branch sets of every [H]-edge. *)

Definition sg_minor_rmap (G H : sgraph) (phi : H -> {set G}) : Prop :=
  [/\ (forall x : H, phi x != set0),
      (forall x : H, connected (phi x)),
      (forall x y : H, x != y -> [disjoint phi x & phi y])
    & (forall x y : H, x -- y ->
         exists p : G * G, [/\ p.1 \in phi x, p.2 \in phi y & p.1 -- p.2])].

Definition sg_minor (G H : sgraph) : Prop := exists phi, @sg_minor_rmap G H phi.

(** A simple graph is planar (Wagner's theorem, taken here as the DEFINITION of
    planarity) iff it has neither ['K_5] nor ['K_3,3] as a minor. *)
Definition planar_sg (G : sgraph) : Prop :=
  ~ sg_minor G 'K_5 /\ ~ sg_minor G 'K_3,3.

(** Corpus row: derived:drv_twoext_conjp
    Site: none
    Review: none
    English statement: (Aboulker, Aubian, Charbit 2023, Digraph Colouring and Arc-Connectivity, arXiv:2304.04690 section 9; corpus derived row Conjecture P)
      For every finite loopless digraph D that is 2-extremal, the underlying simple graph U(D)
      is planar. D is 2-extremal when it is strongly connected, U(D) is 2-connected, lambda(D) =
      2 and the dichromatic number of D is exactly 3.
    Definitions: [loopless D] - the arc relation is irreflexive (this file); [underlyingG llD] -
      the underlying simple graph U(D), where u and v are adjacent when D has an arc in either
      direction (this file); [digonG llD] - the spanning simple graph F_D whose edges are the
      pairs joined by a digon, i.e. by arcs in both directions (this file); [arc_conn D] - the
      maximum over ordered pairs (u,v) of distinct vertices of the minimum size of a u-v dicut,
      which by Menger is lambda(D), the maximum number of pairwise arc-disjoint directed u-v
      paths (this file); [dicolorableb D k] - the vertex set splits into k parts each inducing
      an acyclic subdigraph, i.e. the dichromatic number is at most k
      (conjectures/dichromatic.v); [strongb D] - strong connectivity (invariants/strong.v);
      [two_connected_sg G] - more than two vertices, connected, and connected after deleting any
      single vertex (this file); [chi_vec_eq D m] - dichromatic number exactly m, encoded as m
      >= 1, m-dicolourable and not (m-1)-dicolourable (this file); [k_extremal llD k] /
      [two_extremal llD] - strong, U(D) 2-connected, lambda(D) = k and dichromatic number k+1,
      at k = 2 (this file); [planar_sg G] - no K_5 minor and no K_3,3 minor (this file).
    Notes: Planarity is taken in the Wagner form (no K_5 and no K_3,3 minor) so the file
      compiles without coq-fourcolor; minors use the branch-set map [sg_minor_rmap] of this
      file. Looplessness is threaded as an explicit argument llD rather than existentially
      quantified, so that U(D) can be formed inside the statement. *)
Definition conjecture_P : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    two_extremal llD -> planar_sg (underlyingG llD).

(** ** §3 — the 3-connected / generalised-wheel reduction statements *)

(** 3-vertex-connectivity (no 2-cut): connected, [≥ 4] vertices, and deleting any
    two vertices keeps it connected. *)
Definition three_connected_sg (G : sgraph) : Prop :=
  [/\ (3 < #|G|)%N,
      connected [set: G]
    & forall u v : G, connected (~: [set u; v])].

(** F_D-is-a-forest lemma (PROVED in the team docs as an unconditional structural
    fact; stated here as a target): the digon graph of every 2-extremal digraph is a
    forest. *)
Definition two_extremal_digonG_forest : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    two_extremal llD -> is_forest [set: digonG llD].

(** Corpus row: derived:drv_twoext_step1
    Site: none
    Review: none
    English statement: (Aboulker, Aubian, Charbit 2023, arXiv:2304.04690 section 9; corpus derived row Step 1, the open crux of the ledger)
      For every finite loopless digraph D, if D is 2-extremal (strongly connected, U(D)
      2-connected, lambda(D) = 2 and dichromatic number 3) and U(D) is 3-connected, then the
      digon graph F_D is connected on the whole vertex set; equivalently, since F_D is a forest
      for 2-extremal digraphs, F_D is a spanning tree of U(D), and equivalently D has no
      digon-free vertex cut.
    Definitions: [loopless D] - the arc relation is irreflexive (this file); [underlyingG llD] -
      the underlying simple graph U(D), where u and v are adjacent when D has an arc in either
      direction (this file); [digonG llD] - the spanning simple graph F_D whose edges are the
      pairs joined by a digon, i.e. by arcs in both directions (this file); [arc_conn D] - the
      maximum over ordered pairs (u,v) of distinct vertices of the minimum size of a u-v dicut,
      which by Menger is lambda(D), the maximum number of pairwise arc-disjoint directed u-v
      paths (this file); [dicolorableb D k] - the vertex set splits into k parts each inducing
      an acyclic subdigraph, i.e. the dichromatic number is at most k
      (conjectures/dichromatic.v); [strongb D] - strong connectivity (invariants/strong.v);
      [two_extremal llD] (this file); [three_connected_sg G] - more than three vertices,
      connected, and connected after deleting any two vertices (this file); [connected [set: G]]
      - connectivity of the whole vertex set (coq-graph-theory connectivity.v).
    Notes: The spanning-tree phrasing of the source is stated in its connected form; the
      companion forest half is the separate target [two_extremal_digonG_forest] in this file. *)
Definition three_connected_digonG_connected : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    two_extremal llD ->
    three_connected_sg (underlyingG llD) -> connected [set: digonG llD].

(** H6 / no-full-cover (the colouring crux, [no_full_cover_lemma.md]): a 3-connected,
    λ(D) = 2, Eulerian digraph whose digon graph is DISCONNECTED is 2-dicolourable
    (χ⃗ ≤ 2).  [Eulerian] here = in-degree equals out-degree at every vertex (the
    single-arc subdigraph is balanced).  Guarded by looplessness and [0 < #|D|]. *)
Definition Eulerian (D : diGraphType) : Prop :=
  forall v : D, indeg v = outdeg v.

(** Corpus row: derived:drv_twoext_h6
    Site: none
    Review: none
    English statement: (Aboulker, Aubian, Charbit 2023, arXiv:2304.04690 section 9; corpus derived row H6, the criticality barrier / no-full-cover lemma)
      For every finite loopless digraph D with at least one vertex, if D is strongly connected,
      Eulerian (in-degree equals out-degree at every vertex), lambda(D) = 2, U(D) is 3-connected
      and the digon graph F_D is disconnected (equivalently D has a digon-free cut), then D is
      2-dicolourable, i.e. its dichromatic number is at most 2.
    Definitions: [loopless D] - the arc relation is irreflexive (this file); [underlyingG llD] -
      the underlying simple graph U(D), where u and v are adjacent when D has an arc in either
      direction (this file); [digonG llD] - the spanning simple graph F_D whose edges are the
      pairs joined by a digon, i.e. by arcs in both directions (this file); [arc_conn D] - the
      maximum over ordered pairs (u,v) of distinct vertices of the minimum size of a u-v dicut,
      which by Menger is lambda(D), the maximum number of pairwise arc-disjoint directed u-v
      paths (this file); [dicolorableb D k] - the vertex set splits into k parts each inducing
      an acyclic subdigraph, i.e. the dichromatic number is at most k
      (conjectures/dichromatic.v); [strongb D] - strong connectivity (invariants/strong.v);
      [Eulerian D] - in-degree equals out-degree at every vertex (this file);
      [three_connected_sg G] (this file); [indeg v] (conjectures/classic_core.v); [outdeg v]
      (core/oriented.v).
    Notes: The contrapositive is the statement of the row: under 3-connectivity, Eulerian and
      lambda = 2, dichromatic number 3 forces F_D connected, so this is the barrier form of Step
      1 for Eulerian digraphs. *)
Definition H6_no_full_cover : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    (0 < #|D|)%N -> strongb D -> Eulerian D ->
    arc_conn D = 2 ->
    three_connected_sg (underlyingG llD) ->
    ~ connected [set: digonG llD] ->
    dicolorableb D 2.

(** A generalised wheel (Def 9.1, [A = ∅] case): the underlying graph is a wheel-like
    plane graph — a [hub] set inducing a tree spanning all but a rim, plus a directed
    rim cycle through the leaves.  The faithful inductive Def-9.1 form needs the
    plane-tree / even-leaf-parity machinery (BLOCKED, see §4).  We expose the named
    target [three_connected_generalised_wheel] modulo an abstract
    [generalised_wheel : diGraphType -> Prop] predicate (the blocked structural piece),
    so the 9.2 ⟹ base-case edge is stateable. *)
Section GeneralisedWheel.
Variable generalised_wheel : diGraphType -> Prop.

(** The 3-connected case of Conjecture 9.2 (base case of CONJECTURE-P): every
    3-connected 2-extremal digraph is a generalised wheel. *)
Definition three_connected_generalised_wheel : Prop :=
  forall (D : diGraphType) (llD : loopless D),
    two_extremal llD ->
    three_connected_sg (underlyingG llD) -> generalised_wheel D.

End GeneralisedWheel.

(** ** §4 — the directed Hajós join, the symmetric odd cycle base, and Conjecture 9.2 *)

(** Directed Hajós join (Def 1.5, verbatim): given [uv₁ ∈ A(D₁)] and [v₂w ∈ A(D₂)],
    delete [uv₁] and [v₂w], identify [v₁] and [v₂] into a new vertex [v], and add the
    arc [uw].  We realise the identification on the carrier [D₁ + D₂] with [inr v₂]
    deleted: the surviving copy [inl v₁] of the merged vertex inherits ALL of [v₂]'s
    in- and out-arcs (rerouted), the deleted arcs are excised, and [u → w] is added. *)
Section DHajos.
Variables (D1 D2 : diGraphType).
Variables (u v1 : D1) (v2 w : D2).

Definition dhcar : Type := { x : (D1 + D2)%type | x != inr v2 }.
HB.instance Definition _ := Finite.on dhcar.

Definition dh_rel (x y : dhcar) : bool :=
  match val x, val y with
  | inl a, inl b =>
      (* inside D₁, minus the deleted arc u → v₁ *)
      arc a b && ~~ ((a == u) && (b == v1))
  | inl a, inr b =>
      (* the merged vertex inl v₁ also plays v₂: its D₂-out-arcs v₂ → b survive
         (minus the deleted v₂ → w); plus the added arc u → w *)
      [|| (a == v1) && arc v2 b && ~~ (b == w)
        | (a == u) && (b == w) ]
  | inr a, inl b =>
      (* a → v₂ in D₂ is rerouted to a → inl v₁ (the merged vertex) *)
      (b == v1) && arc a v2
  | inr a, inr b =>
      (* inside D₂, minus the deleted arc v₂ → w *)
      arc a b && ~~ ((a == v2) && (b == w))
  end.

HB.instance Definition _ := HasArc.Build dhcar dh_rel.

(** The directed Hajós join [D₁ ▽ D₂] (w.r.t. [u v₁], [v₂ w]) as a [diGraphType]. *)
Definition dhajos : diGraphType := dhcar.

End DHajos.

(** Symmetric (bidirected) cycle [C̃_n] on ['I_n]: every consecutive pair [i],[i+1]
    is a digon.  The base members of [H₂] are the symmetric ODD cycles. *)
Section SymCycle.
Variable n : nat.
(** Consecutive-vertex adjacency on ['I_n] via nat successor modulo [n] (no ring
    instance needed): [i] and [i+1 mod n] are joined, in both directions (a digon). *)
Definition symcyc_rel (x y : 'I_n) : bool :=
  (val y == (val x).+1 %% n) || (val x == (val y).+1 %% n).
Definition symcyc : Type := 'I_n.
HB.instance Definition _ := Finite.on symcyc.
HB.instance Definition _ := HasArc.Build symcyc symcyc_rel.
Definition sym_cycle : diGraphType := symcyc.
End SymCycle.

(** A symmetric odd cycle: [sym_cycle n] with [n ≥ 3] odd. *)
Definition symmetric_odd_cycle (D : diGraphType) : Prop :=
  exists n : nat, [/\ (3 <= n)%N, odd n & dgiso D (sym_cycle n)].

(** [H₂], the class of 2-extremal digraphs conjectured in §9, is the smallest class
    containing the symmetric odd cycles and closed under directed Hajós join AND the
    2-Hajós tree join (Def 9.1).  The directed-Hajós-join closure and the base are
    faithfully captured below; the 2-Hajós TREE join (Def 9.1: a plane tree with an
    edge partition [(A,B)] whose every leaf-to-leaf path has an EVEN number of
    [B]-edges, [A]-edges replaced by blocks [Dᵢ], [B]-edges by digons, plus a rim
    cycle through the leaves) is the BLOCKED piece — it requires plane-tree embedding
    + leaf-parity infrastructure that has no faithful one-file form.  We therefore
    state [conj_9_2] PARAMETRICALLY over an abstract membership predicate [in_H2],
    constrained by the two faithful closure axioms it must satisfy; the tree-join
    closure is left to the abstract predicate and flagged as the blocked content. *)

Section Conjecture92.
Variable in_H2 : diGraphType -> Prop.

(** Faithful constraints on any correct [in_H2]: it contains the symmetric odd cycles
    and is closed under directed Hajós join.  (The third closure — under the 2-Hajós
    tree join of Def 9.1 — is the blocked piece, not expressible here, and is folded
    into [in_H2] as an opaque hypothesis.) *)
Definition in_H2_contains_base : Prop :=
  forall D : diGraphType, symmetric_odd_cycle D -> in_H2 D.

Definition in_H2_closed_dhajos : Prop :=
  forall (D1 D2 : diGraphType) (u v1 : D1) (v2 w : D2),
    (u --> v1) -> (v2 --> w) -> in_H2 D1 -> in_H2 D2 ->
    in_H2 (dhajos u v1 v2 w).

(** Conjecture 9.2 (verbatim, p.33): a digraph is 2-extremal iff it is in [H₂].
    Quantified over the looplessness proof [llD] (every digraph in the paper is
    loopless; the forward direction is for any such witness). *)
Definition conj_9_2 : Prop :=
  forall (D : diGraphType) (llD : loopless D), two_extremal llD <-> in_H2 D.

End Conjecture92.

(** ** Implication edges (relative theorems, provable WITHOUT resolving any conjecture) *)

(** Conjecture 9.2 ⟹ CONJECTURE-P.  Given an abstract [in_H2] satisfying 9.2 and the
    PROVED (team docs, [planarity_of_2extremal.md]) fact that membership in [H₂]
    yields a planar underlying graph (here supplied as the hypothesis [H2_planar],
    the proved [H₂ ⇒ planar] direction), every 2-extremal digraph is in [H₂] hence
    planar.  This edge is RELATIVE: it does not prove 9.2, only that 9.2 (plus the
    proved easy direction [H₂ ⇒ planar]) forces CONJECTURE-P. *)
Theorem conj_9_2_implies_conjecture_P
    (in_H2 : diGraphType -> Prop) :
  conj_9_2 in_H2 ->
  (forall (D : diGraphType) (llD : loopless D),
     in_H2 D -> planar_sg (underlyingG llD)) ->
  conjecture_P.
Proof.
move=> C92 H2_planar D llD te.
by apply: H2_planar; apply/(C92 D llD).
Qed.

(** Conjecture 9.2 ⟹ the 3-connected case (base case of CONJECTURE-P).  Given that
    membership in [H₂] together with 3-connectivity yields a generalised wheel (the
    PROVED assembly step, team docs [three_connected_wheel.md]: a 3-connected member
    is empty-A, hence a generalised wheel — supplied here as [H2_gw]), 9.2 forces
    every 3-connected 2-extremal digraph to be a generalised wheel. *)
Theorem conj_9_2_implies_three_connected_gw
    (in_H2 : diGraphType -> Prop) (generalised_wheel : diGraphType -> Prop) :
  conj_9_2 in_H2 ->
  (forall (D : diGraphType) (llD : loopless D),
     in_H2 D ->
     three_connected_sg (underlyingG llD) -> generalised_wheel D) ->
  three_connected_generalised_wheel generalised_wheel.
Proof.
move=> C92 H2_gw D llD te tc.
by apply: (H2_gw D llD) => //; apply/(C92 D llD).
Qed.

(** H6 (no full cover) ⟹ the 3-connected digon-graph-connected crux, under the
    standing 2-extremal side facts (strong, Eulerian, λ=2) for a 3-connected
    2-extremal digraph.  RELATIVE: it threads the proved structural facts (supplied
    as hypotheses) through the colouring lemma, with no resolution of 9.2.  The proof
    is by contradiction: a disconnected digon graph would, by H6, give χ⃗ ≤ 2,
    contradicting χ⃗ = 3 of a 2-extremal digraph. *)
Theorem H6_implies_three_connected_digonG_connected :
  H6_no_full_cover ->
  (forall (D : diGraphType) (llD : loopless D),
     two_extremal llD -> Eulerian D) ->
  three_connected_digonG_connected.
Proof.
move=> H6 side D llD te tc.
have eul : Eulerian D := side D llD te.
case: te => str _ lam chi.
have n0 : (0 < #|D|)%N.
  by case: tc => h3 _ _; apply: leq_trans h3.
case: (@connectedP _ [set: digonG llD]) => [//|nconn].
have c2 : dicolorableb D 2 by apply: (H6 D llD).
by case: chi => _ [_] /negP; case; exact: c2.
Qed.
