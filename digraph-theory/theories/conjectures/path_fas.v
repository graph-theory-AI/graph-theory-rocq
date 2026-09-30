(** * Digraph.conjectures.path_fas — P4: Path-FAS / degreewidth / linear-forest orderings

    The Path-FAS family of Aboulker–Aubian–Lopes, "Finding forest-orderings of
    tournaments is NP-complete" (arXiv:2402.10782), Problem 4.4, together with the
    degreewidth decomposition (Davot–Isenmann–Roy–Thiebaut, arXiv:2212.06007) used to
    attack it.  This file states the MATHEMATICAL PREDICATES only — no complexity
    wrapper (no "in P / NP-complete").

    Background reduction (path_matching_fas/docs/path_fas.md): a tournament [T] has a
    *path-FAS* (a feedback arc set whose underlying undirected graph is a linear forest)
    iff some vertex order has back-arc graph a linear forest.  Both directions are stated
    here; their equivalence is the open formalization target.

    New primitives on top of [core/order.v]'s backedge graph:
      - [sdeg]          : the degree of a vertex in a simple graph (graph-theory [sgraph]).
      - [linear_forest] : a simple graph that is acyclic AND has maximum degree ≤ 2
                          (a disjoint union of paths).
      - [backdeg p v]   : the back-degree of [v] under order [p] (number of back-arcs
                          incident to [v] = degree of [v] in the backedge graph).
      - [maxbackdeg p]  : the maximum back-degree over all vertices.
      - [Delta_star T]  : the degreewidth Δ*(T) = min over orders of [maxbackdeg]
                          (a realized minimum, via the [arg min] idiom of [omegabar]).

    Directed-cycle vocabulary (reusing [dicycle] from dipath.v):
      - [di3cycle] / [di4cycle] : directed cycles of length exactly 3 / 4.
      - a [linear_forest]-shaped arc set HITTING every directed 3- and 4-cycle.

    Statements:
      - [has_LFO T]            : ∃ order whose back-arc graph is a linear forest.
      - [has_pathFAS T]        : ∃ a feedback arc set whose underlying graph is a
                                 linear forest (FAS formulation of Problem 4.4).
      - [pathFAS_iff_LFO]      : the reduction has_pathFAS T ↔ has_LFO T (open target).
      - [LFO_iff_34transversal]: has_LFO T ↔ ∃ linear-forest arc set hitting every
                                 directed 3- and 4-cycle (the equivalence target).
      - [matchingFAS_iff_dw1]  : has_matchingFAS T ↔ Δ*(T) ≤ 1 (sparse-tournament fact).
      - [minimal_LFO_no_infinite] : for every N there is a vertex-minimal LFO-NO
                                 tournament on more than N vertices.

    One PROVED relative edge (independent of any conjecture):
      - [has_LFO_Delta_star_le2] : has_LFO T → Δ*(T) ≤ 2  (the degreewidth split).
    See docs/CONJECTURES_FORMALIZATION_PLAN.md §4 (P4). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath.
From Digraph Require Import tournament order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Degree in a simple graph and the linear-forest predicate *)

Section SimpleGraphDegree.
Variable G : sgraph.

(** Degree of [x]: the number of its neighbours in [G]. *)
Definition sdeg (x : G) : nat := #|[set y | x -- y]|.

End SimpleGraphDegree.

(** A *linear forest* is a simple graph that is a forest (acyclic) of maximum degree
    ≤ 2, i.e. a disjoint union of paths.  We use graph-theory's [is_forest] for
    acyclicity (over the full vertex set) and bound every vertex degree by [2]. *)
Definition linear_forest (G : sgraph) : Prop :=
  is_forest [set: G] /\ (forall x : G, sdeg x <= 2).

(** ** Back-degree and degreewidth Δ* of a tournament under an order *)

Section Degreewidth.
Variable T : tournament.

(** The back-degree of [v] under order [p]: the number of back-arcs incident to [v].
    This is exactly the degree of [v] in the backedge (simple) graph [backedge p]. *)
Definition backdeg (p : {perm T}) (v : T) : nat := sdeg (v : backedge p).

(** The maximum back-degree over all vertices, for a fixed order. *)
Definition maxbackdeg (p : {perm T}) : nat := \max_(v : T) backdeg p v.

(** The degreewidth Δ*(T): the minimum over all vertex orders of the maximum
    back-degree.  Realized as a genuine minimum via the [arg min] idiom (cf.
    [omegabar]); the witnessing permutation [1%g] makes the argument non-vacuous. *)
Definition Delta_star : nat :=
  maxbackdeg [arg min_(p < (1%g : {perm T})) maxbackdeg p].

Lemma Delta_star_min (p : {perm T}) : (Delta_star <= maxbackdeg p)%N.
Proof. by rewrite /Delta_star; case: arg_minnP => // q _; apply. Qed.

Lemma Delta_star_witness : {p : {perm T} | Delta_star = maxbackdeg p}.
Proof. by rewrite /Delta_star; eexists. Qed.

(** A pointwise back-degree bound under [p] bounds [maxbackdeg p]. *)
Lemma maxbackdeg_leP (p : {perm T}) (k : nat) :
  (forall v : T, backdeg p v <= k)%N -> (maxbackdeg p <= k)%N.
Proof. by move=> H; apply/bigmax_leqP=> v _; apply: H. Qed.

End Degreewidth.

(** ** Directed 3- and 4-cycles (reusing [dicycle]) *)

(** A directed cycle of length exactly [3] (a directed triangle). *)
Definition di3cycle (D : diGraphType) (c : seq D) : bool := dicycle c && (size c == 3).

(** A directed cycle of length exactly [4]. *)
Definition di4cycle (D : diGraphType) (c : seq D) : bool := dicycle c && (size c == 4).

(** ** Linear-forest ordering (LFO) and the path-FAS reduction target *)

(** [has_LFO T]: there is a total vertex order whose back-arc (simple) graph is a
    linear forest.  This is the working formalization of Path-FAS Problem 4.4
    (path_matching_fas/docs/path_fas.md). *)
Definition has_LFO (T : tournament) : Prop :=
  exists p : {perm T}, linear_forest (backedge p).

(** ** Feedback arc sets and the path-shaped FAS formulation *)

Section FAS.
Variable T : tournament.

(** An arc set [F] (a set of ordered pairs) is a set of genuine arcs of [T]. *)
Definition is_arcset (F : {set T * T}) : bool := [forall e in F, arc e.1 e.2].

(** [c] (a directed cycle, read cyclically) uses an arc of [F]: some consecutive
    pair of [c] (with the wrap-around pair [last,first]) lies in [F].  [zip c (rot 1 c)]
    is the list of consecutive ordered pairs of the cyclic sequence [c]. *)
Definition cycle_uses (F : {set T * T}) (c : seq T) : bool :=
  has (fun e => e \in F) (zip c (rot 1 c)).

(** A *feedback arc set*: a set of arcs meeting every directed cycle.  Removing [F]
    leaves an acyclic digraph (every [dicycle] of [T] uses an arc of [F]). *)
Definition is_FAS (F : {set T * T}) : Prop :=
  is_arcset F /\ forall c : seq T, dicycle c -> cycle_uses F c.

(** The underlying *simple* graph of an arc set [F]: vertices adjacent iff some
    arc of [F] joins them (in either direction).  The explicit [u != v] guard makes
    this unconditionally irreflexive (and is harmless on genuine arc sets, which
    never contain a loop).  This is where "the FAS forms a path / linear forest"
    lives — Path-FAS asks this simple graph to be a linear forest. *)
Definition farc_rel (F : {set T * T}) : rel T :=
  [rel u v | (u != v) && (((u, v) \in F) || ((v, u) \in F))].

Fact farc_sym (F : {set T * T}) : symmetric (farc_rel F).
Proof. by move=> u v; rewrite /farc_rel /= eq_sym orbC. Qed.

Fact farc_irrefl (F : {set T * T}) : irreflexive (farc_rel F).
Proof. by move=> u; rewrite /farc_rel /= eqxx. Qed.

Definition farc_graph (F : {set T * T}) : sgraph :=
  SGraph (@farc_sym F) (@farc_irrefl F).

End FAS.

(** ** The Path-FAS statement (Problem 4.4) and its reduction to LFO *)

(** [has_pathFAS T]: [T] has a feedback arc set whose underlying simple graph is a
    linear forest (a "path-shaped" FAS, generalizing matching-FAS).  This is the
    literal Problem 4.4 predicate. *)
Definition has_pathFAS (T : tournament) : Prop :=
  exists F : {set T * T}, is_FAS F /\ linear_forest (farc_graph F).

(** No corpus row: the reduction target of the Path-FAS family (Aboulker, Aubian, Lopes, Finding
    forest-orderings of tournaments is NP-complete, arXiv:2402.10782, Problem 4.4): a tournament
    has a feedback arc set whose underlying simple graph is a linear forest if and only if some
    vertex ordering has a linear-forest back-arc graph. The corpus carries no row for Problem
    4.4 or its reduction; this is the working formalisation target of
    problems/path_matching_fas. *)
Definition pathFAS_iff_LFO_statement : Prop :=
  forall T : tournament, has_pathFAS T <-> has_LFO T.

(** ** Matching-FAS and the degreewidth-1 (sparse-tournament) characterization *)

(** [has_matchingFAS T]: a feedback arc set whose underlying simple graph is a
    *matching* — a forest of maximum degree ≤ 1 (no two arcs of [F] share a
    vertex).  (A matching is in particular a linear forest, so matching-FAS ⟹
    path-FAS.) *)
Definition matching (G : sgraph) : Prop :=
  is_forest [set: G] /\ (forall x : G, sdeg x <= 1).

Definition has_matchingFAS (T : tournament) : Prop :=
  exists F : {set T * T}, is_FAS F /\ matching (farc_graph F).

(** No corpus row: the sparse-tournament fact of Davot, Isenmann, Roy and Thiebaut
    (arXiv:2212.06007): a tournament has a feedback arc set whose underlying simple graph is a
    matching if and only if its degreewidth is at most 1. A known theorem stated here uniformly
    with the Path-FAS targets, not a corpus conjecture row. *)
Definition matchingFAS_iff_dw1_statement : Prop :=
  forall T : tournament, has_matchingFAS T <-> (Delta_star T <= 1)%N.

(** ** The 3-and-4-cycle transversal equivalence (the equivalence target) *)

(** A *directed-3/4-cycle transversal* by an arc set: a set of arcs [F] that meets
    every directed triangle and every directed 4-cycle of [T] (a weaker hitting
    requirement than a full FAS, which must meet ALL directed cycles). *)
Definition hits_34cycles (T : tournament) (F : {set T * T}) : Prop :=
  (forall c : seq T, di3cycle c -> cycle_uses F c) /\
  (forall c : seq T, di4cycle c -> cycle_uses F c).

(** No corpus row: the equivalence target of problems/path_matching_fas (a tournament has a
    linear-forest ordering if and only if some arc set whose underlying simple graph is a linear
    forest hits every directed 3-cycle and every directed 4-cycle); an internal characterisation
    goal of the Path-FAS attack, with no corpus row. *)
Definition LFO_iff_34transversal_statement : Prop :=
  forall T : tournament,
    has_LFO T <->
    (exists F : {set T * T}, linear_forest (farc_graph F) /\ hits_34cycles F).

(** ** Infinitely many vertex-minimal LFO-NO tournaments *)

(** [T] is *LFO-NO* if it has no linear-forest ordering. *)
Definition LFO_no (T : tournament) : Prop := ~ has_LFO T.

(** [T] is *vertex-minimal* LFO-NO: it is LFO-NO, yet deleting ANY single vertex
    yields a tournament that DOES have a linear-forest ordering. *)
Definition minimal_LFO_no (T : tournament) : Prop :=
  LFO_no T /\ forall v : T, has_LFO (del_tournament v).

(** No corpus row: an internal Path-FAS target of problems/path_matching_fas: for every N there
    is a vertex-minimal tournament without a linear-forest ordering on more than N vertices, so
    the minimal obstructions do not form a finite family. No corpus row. *)
Definition minimal_LFO_no_infinite_statement : Prop :=
  forall N : nat, exists T : tournament, minimal_LFO_no T /\ (N < #|T|)%N.

(** ** A PROVED relative edge: the degreewidth split [has_LFO ⟹ Δ* ≤ 2]

    Independent of any conjecture: if an order's back-arc graph is a linear forest,
    that very order has maximum back-degree ≤ 2, so the degreewidth is ≤ 2
    (path_matching_fas/docs/degreewidth_direction.md).  Contrapositive: Δ*(T) ≥ 3 is
    a global NO-certificate for Path-FAS. *)
Theorem has_LFO_Delta_star_le2 (T : tournament) :
  has_LFO T -> (Delta_star T <= 2)%N.
Proof.
case=> p [_ degp]; apply: (leq_trans (Delta_star_min p)).
by apply: maxbackdeg_leP=> v; rewrite /backdeg; apply: degp.
Qed.
