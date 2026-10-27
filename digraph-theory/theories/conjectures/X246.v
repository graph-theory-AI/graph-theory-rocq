(** * Digraph.conjectures.X246 -- wave X246: heroes, avoidable digraphs, long cycles in vertex
    transitive digraphs, near-acyclic r-free digraphs (2026-10-27)

    A six-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier). Rows:
    arxiv:2202.13306#01 (heroes in Forb_ind(K_1 + F)), arxiv:2510.11311#00 and #01 (avoidable
    digraphs), arxiv:2602.16333#00 and #03 (vertex transitive digraphs) and arxiv:2204.01938#00
    (r-free digraphs). Shared vocabulary is reused: [ind_free], [K1] and [c3sub]
    (conjectures/heroes.v), [oriented_dg] (conjectures/heroes_dichotomy.v),
    [dichromatic_bounded] (conjectures/dichromatic.v), [contains_subdigraph] (conjectures/unvd.v),
    [digraph_sum] (constructions/digraph_sum.v), [outdeg], [outsel] and [induced_digraph]
    (core/oriented.v, core/digraph.v), [dipath] and [dicycle] (core/dipath.v),
    [vertex_transitiveb] (constructions/automorphism.v) and [X2.weakly_connected] (the notion of
    the sibling row arxiv:2602.16333#02). The sources are the Mac's deposit
    coordination/sources/x246-source-mac-20261027; the grounding certificates are in
    grounding_X246.v. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath heroes heroes_dichotomy dichromatic unvd.
From Digraph Require Import digraph_sum.
From Digraph Require automorphism X2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x246 vocabulary ************************************************* *)

(** AVOIDABLE (arXiv:2510.11311, TeX l.59): there is d : nat -> nat such that every LOOPLESS
    host (the source's arcs are pairs u != v, l.92; digons are allowed) of minimum out-degree at
    least d k contains an F-free subdigraph of minimum out-degree at least k. A subdigraph on a
    vertex set S is an out-selection f on [induced_digraph S] ([outsel f] keeps the arcs that
    [f] selects, so every subdigraph on S arises), F-free = no copy of F as a (not necessarily
    induced) subdigraph. As X221's [x221_eulerian_avoidable_sub], the guards S != set0 (an empty
    subdigraph is F-free with a vacuous minimum out-degree) and 0 < #|D| (the empty host has
    no minimum out-degree) are load-bearing. *)
Definition x246_avoidable (F : diGraphType) : Prop :=
  exists d : nat -> nat,
    forall (k : nat) (D : diGraphType),
      irreflexive (@arc D) -> (0 < #|D|)%N -> (forall v : D, (d k <= outdeg v)%N) ->
      exists (S : {set D}) (f : induced_digraph S -> {set induced_digraph S}),
        [/\ S != set0, (forall v : outsel f, (k <= outdeg v)%N)
          & ~ contains_subdigraph F (outsel f)].

(** The orientation [b] of the cycle on 'I_n: the edge {i, i+1 mod n} is oriented i -> i+1
    when [b i] and i+1 -> i otherwise; for n >= 3 the 2^n vectors give every orientation of
    C_n, with no loop and no digon. The alias takes [b] as a real parameter, so distinct
    orientations are distinct types (outsel's lesson, core/oriented.v). *)
Definition x246_cycle_or (n : nat) (b : 'I_n -> bool) : Type := 'I_n.

Section CycleOrientation.
Variables (n : nat) (b : 'I_n -> bool).
HB.instance Definition _ := Finite.on (x246_cycle_or b).

Definition x246_cycle_or_rel (i j : 'I_n) : bool :=
  (b i && (val j == (val i).+1 %% n)) || (~~ b j && (val i == (val j).+1 %% n)).

HB.instance Definition _ := HasArc.Build (x246_cycle_or b) x246_cycle_or_rel.
End CycleOrientation.

(** A HEIGHT FUNCTION (arXiv:2510.11311, TeX l.87): h(v) = h(u) + 1 on every arc (u, v). The
    source's h maps into the integers; on a finite digraph a nat-valued one is the same notion
    up to subtracting the minimum. A digraph with a height function has no loop and no
    directed cycle. *)
Definition x246_height (F : diGraphType) : Prop :=
  exists h : F -> nat, forall u v : F, u --> v -> h v = (h u).+1.

(** R-FREE (arXiv:2204.01938, TeX l.245 and Definition 5.3, l.602-603): no directed cycle of
    length at most r; a [dicycle] has as many arcs as vertices. *)
Definition x246_r_free (r : nat) (D : diGraphType) : Prop :=
  forall c : seq D, dicycle c -> (r < size c)%N.

(** beta(D) <= 1 (arXiv:2204.01938, TeX l.189: beta is the size of a minimum feedback arc set):
    a set F of at most one ordered pair meets every directed cycle, read cyclically (the shape
    of path_fas.v's cycle_uses, whose is_FAS lives in a Section over tournaments). *)
Definition x246_fas_le1 (D : diGraphType) : Prop :=
  exists F : {set D * D}, (#|F| <= 1)%N /\
    forall c : seq D, dicycle c -> has (fun e => e \in F) (zip c (rot 1 c)).

(** ** X246 statements ******************************************************* *)

(** Corpus row: arxiv:2202.13306#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.13306__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.13306__01.json
    English statement: (Aboulker, Aubian, Charbit, Heroes in oriented complete multipartite
      graphs, arXiv:2202.13306v2, Question 5.4)
      Let H and F be oriented digraphs such that Delta(1,1,H) is a hero in Forb_ind(F) and H is
      a hero in Forb_ind(K_1 + F). Then Delta(1,1,H) is a hero in Forb_ind(K_1 + F).
    Definitions: [dichromatic_bounded C] - one bound B dicolours every member of C
      (conjectures/dichromatic.v); "X is a hero in C" is [dichromatic_bounded] of the X-free
      members of C; [ind_free X D] - no induced copy of X in D (conjectures/heroes.v);
      [oriented_dg D] - no loop and no digon (conjectures/heroes_dichotomy.v); [c3sub K1 K1 H]
      - blocks K1 => K1 => H => K1 (conjectures/heroes.v); [digraph_sum K1 F] - the disjoint
      union K_1 + F (constructions/digraph_sum.v).
    Notes: The paper's digraphs have no digons, loops or multi-arcs (TeX l.327), so the ambient
      class is [oriented_dg] and H, F are oriented; H-free means induced (l.349), a hero in C is
      bounded dichromatic number on the H-free members of C (l.350), K_1 + F is the disjoint
      union (l.353), and Delta(1,H_1,H_2) is x => H_1 => H_2 => x (l.340), so Delta(1,1,H) is
      exactly [c3sub K1 K1 H]. The paper defines Delta(1,H_1,H_2) for tournaments only; for an
      oriented H that is not a tournament the encoded implication holds trivially (F nonempty:
      every tournament is H-free and (K_1+F)-free, and tournaments have unbounded dichromatic
      number, so the second hypothesis fails; F empty: K_1 + F = K_1 and the conclusion's class
      is the empty digraph), so quantifying over every oriented H adds no row. The question is
      stated (l.1121-1123) as a statement to be decided; the affirmative form is encoded.
      Literature status: open at the pin (pinned status open). *)
Definition delta11_hero_transfer_k1_plus_statement : Prop :=
  forall H F : diGraphType, oriented_dg H -> oriented_dg F ->
    dichromatic_bounded
      (fun D => [/\ oriented_dg D, ind_free F D & ind_free (c3sub K1 K1 H) D]) ->
    dichromatic_bounded
      (fun D => [/\ oriented_dg D, ind_free (digraph_sum K1 F) D & ind_free H D]) ->
    dichromatic_bounded
      (fun D => [/\ oriented_dg D, ind_free (digraph_sum K1 F) D & ind_free (c3sub K1 K1 H) D]).

(** Corpus row: arxiv:2510.11311#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2510.11311__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2510.11311__00.json
    English statement: (Christoph, Janzer, Petrova, Steiner, Extending Thomassen's conjecture
      to directed graphs, arXiv:2510.11311v1, Conjecture 6.1)
      All orientations of odd cycles are avoidable.
    Definitions: [x246_avoidable F] (this file); [x246_cycle_or b] - the orientation b of the
      cycle on 'I_n (this file).
    Notes: The odd cycles are C_n for odd n >= 3, written as the one guard "odd n && 2 < n";
      every orientation is one vector b. Avoidable as in the paper (TeX l.59, the hosts and the
      F-free subdigraph as recorded at [x246_avoidable]). The paper proves the cases C_3 and C_5
      (Theorem 1.1, l.64-66); they are instances of the row, not a resolution of it.
      Literature status: open at the pin (pinned status open). *)
Definition odd_cycle_orientations_avoidable_statement : Prop :=
  forall (n : nat) (b : 'I_n -> bool), odd n && (2 < n)%N -> x246_avoidable (x246_cycle_or b).

(** Corpus row: arxiv:2510.11311#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2510.11311__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2510.11311__01.json
    English statement: (Christoph, Janzer, Petrova, Steiner, Extending Thomassen's conjecture
      to directed graphs, arXiv:2510.11311v1, Question 6.2)
      Every digraph which allows a height function is not avoidable.
    Definitions: [x246_height F] and [x246_avoidable F] (this file).
    Notes: The question (TeX l.341-343) is encoded in its affirmative form. The digraphs proved
      non-avoidable in the paper (one-directed complete bipartite digraphs, oriented trees)
      allow a height function (l.340). The empty and the one-vertex digraph have a height
      function and are contained in every nonempty subdigraph, so they are not avoidable, as
      the affirmative form says. Literature status: open at the pin (pinned status open). *)
Definition height_function_not_avoidable_statement : Prop :=
  forall F : diGraphType, x246_height F -> ~ x246_avoidable F.

(** Corpus row: arxiv:2602.16333#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2602.16333__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2602.16333__00.json
    English statement: (Bucic, Hendrey, Mohar, Steiner, Yepremyan, Long cycles in vertex
      transitive digraphs, arXiv:2602.16333v1, Conjecture 4.1)
      There is eps > 0 such that for infinitely many n some connected vertex transitive digraph
      of order n has perimeter gap at least eps n.
    Definitions: [X2.weakly_connected D] - the underlying graph is connected
      (conjectures/X2.v); [automorphism.vertex_transitiveb D] - the automorphism group is
      transitive on vertices (constructions/automorphism.v); [dicycle] (core/dipath.v).
    Notes: The perimeter gap is the number of vertices minus the length of a longest directed
      cycle (TeX l.150; l.116-117). Connected means the underlying graph is connected, which
      coincides with strong connectivity for vertex transitive digraphs (l.180). eps = 1/m and
      "gap >= n/m" is written m * size c + n <= m * n for every dicycle c, so it bounds the
      circumference (no subtraction; m = 0 forces n = 0, so no 0 < m guard is needed); a
      connected vertex transitive digraph on at least 2 vertices has a dicycle, so for N >= 2
      the inequality is never vacuous. "Infinitely many n" is an order at least N for every N.
      Loops are harmless: vertex transitivity puts loops on all vertices or none, and deleting
      them keeps both properties and only removes constraints. Literature status: open at the
      pin (pinned status open); the paper proves a (1 - o(1)) ln n gap only. *)
Definition vertex_transitive_linear_perimeter_gap_statement : Prop :=
  exists m : nat, forall N : nat, exists D : diGraphType,
    [/\ (N <= #|D|)%N, X2.weakly_connected D, automorphism.vertex_transitiveb D &
        forall c : seq D, dicycle c -> (m * size c + #|D| <= m * #|D|)%N].

(** Corpus row: arxiv:2602.16333#03
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2602.16333__03/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2602.16333__03.json
    English statement: (Bucic, Hendrey, Mohar, Steiner, Yepremyan, Long cycles in vertex
      transitive digraphs, arXiv:2602.16333v1, Question 4.4)
      There is C > 0 such that in any vertex transitive digraph the length of a longest path is
      at most C times the length of a longest directed cycle.
    Definitions: [automorphism.vertex_transitiveb D] (constructions/automorphism.v);
      [dipath x s] - the directed path x :: s, of size s arcs (core/dipath.v); [dicycle c] - a
      directed cycle of size c arcs (core/dipath.v).
    Notes: The question (TeX l.483-485) is encoded in its affirmative form, C a natural number
      (a real C by its ceiling). Its lead-in (l.481) speaks of connected digraphs, the question
      of any vertex transitive digraph: the two agree, since each component of a vertex
      transitive digraph is vertex transitive and holds its paths and cycles. Lengths count
      arcs (a cycle "has length four", l.173); counting a path's vertices instead changes C at
      most by a factor 2 on paths with an arc. The guard 0 < size s only drops the arcless
      case, where no cycle exists; a path with an arc forces a dicycle in a vertex transitive
      digraph. Loops are harmless (deleting them keeps vertex transitivity, every path and every
      longer cycle). Literature status: open at the pin (pinned status open). *)
Definition vertex_transitive_path_cycle_ratio_statement : Prop :=
  exists C : nat, forall D : diGraphType, automorphism.vertex_transitiveb D ->
    forall (x : D) (s : seq D), dipath x s -> (0 < size s)%N ->
      exists c : seq D, dicycle c /\ (size s <= C * size c)%N.

(** Corpus row: arxiv:2204.01938#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2204.01938__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2204.01938__00.json
    English statement: (Fox, Himwich, Mani, Extremal results on feedback arc sets in digraphs,
      arXiv:2204.01938v2, introduction)
      Every r-free digraph on n vertices with r > 2n/3 is at most one arc away from being
      acyclic.
    Definitions: [x246_r_free r D] - no directed cycle of length at most r (this file;
      Definition 5.3, TeX l.602-603); [x246_fas_le1 D] - beta(D) <= 1 (this file; l.189).
    Notes: The pinned text is the introduction's (TeX l.251: r-free with r > 2n/3) and is
      encoded as such (Lancelot's decision (92)). The numbered Conjecture 5.6 (l.627-629) says
      "(r-1)-free" with the same inequality: it is strictly STRONGER (every r-free digraph is
      (r-1)-free, so 5.6 implies this row), and Remark 5.7's tightness example ((r-1)-free at
      r = 2n/3 with beta = 2, l.631-633) concerns 5.6, not this row. The paper's digraphs are
      oriented (l.185); r-freeness with 3r > 2n excludes loops and digons, so no guard is
      needed. Literature status: SOLVED BEFORE the corpus pin (pinned status solved, confidence
      medium): K. Lum, "Extremal Structural Results for Feedback Arc Sets and Graph Inversions",
      MIT PRIMES research paper (MIT's index item 466, 12 January 2026; the Mac's deposit
      coordination/sources/x246-lum-mac-20261027), Theorem 1.5 (p.2): an (r-1)-free digraph on
      n vertices with r > floor(2n/3) has beta <= 1 (proof in Section 2.1, pp.4-5; oriented
      digraphs and the same r-free, p.1). For an integer r the threshold is r > 2n/3, so the
      theorem is Conjecture 5.6 and implies this row. A research paper of the MIT PRIMES
      programme, not peer-reviewed; the proof is not independently verified here. *)
Definition r_free_two_thirds_one_arc_from_acyclic_statement : Prop :=
  forall (r : nat) (D : diGraphType), (2 * #|D| < 3 * r)%N -> x246_r_free r D -> x246_fas_le1 D.
