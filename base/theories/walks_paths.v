(** * GTBase.walks_paths — vertex sequences, walks and paths

    Batch B of the library migration (meta/LIBRARY_MIGRATION_PLAN.md, section 15)
    gathers the reusable finite path and cycle vocabulary of the corpus in this
    module, one concept family per reviewed change: the vertex set of a raw
    vertex sequence, [seq_vertices] (registry
    meta/library_primitives/path-vertices.json), the internal vertices of a
    sequence, [seq_interior] and [seq_inner] (registry
    meta/library_primitives/internal-vertices.json, section "Internal vertices"
    below), the consecutive entries of a sequence, [seq_consecutive] (registry
    meta/library_primitives/consecutive-in-path.json, section "Consecutive
    entries" below), the cyclically consecutive entries of a sequence,
    [seq_cyclic_consecutive] and [seq_cyclic_consecutiveb] (registry
    meta/library_primitives/consecutive-in-cycle.json, section "Cyclically
    consecutive entries" below), set-to-set simple paths, [seq_set_path]
    (registry meta/library_primitives/set-path.json, section "Set-to-set simple
    paths" below), nonempty simple paths, [seq_simple_path] (registry
    meta/library_primitives/simple-path.json, section "Simple whole-sequence
    paths" below), simple walks with the empty sequence accepted,
    [seq_simple_walk] (registry meta/library_primitives/is-path.json, section
    "Simple walks of a sequence" below), and the edges traversed by a sequence,
    [seq_edge_list], [seq_edge_set] and [seq_index_edge_set] (registry
    meta/library_primitives/path-edges.json, section "Edges traversed by a
    sequence" below), and genuine cycles of a relation, [seq_cycle] and
    [seq_cycleb] (registry meta/library_primitives/genuine-cycle.json, section
    "Genuine cycles of a sequence" below).

    Upstream audit (2026-10-02; MathComp 2.5.0, coq-graph-theory 0.9.7).
    - MathComp [finset.v] writes the set spanned by an arbitrary sequence [s] as
      [[set:: s]], with [set_nil], [set_seq1] and [set_cons]; the comprehension
      [[set v | v \in s]] denotes the same set.
    - coq-graph-theory [digraph.v] packages walks as [Path x y]: a tail sequence
      [val p] together with a proof of [pathp x y (val p)].  Its vertex list
      [nodes p] is [locked (x :: val p)], so it always contains [x] and exists
      only for genuine walks; the library writes the vertex set of [p] as
      [[set z in p]] (see [interior] and [connected_path]).  coq-graph-theory has
      no name for the vertex set of a RAW sequence.
    The corpus helpers are applied to arbitrary sequences, with no walk,
    uniqueness or nonemptiness premise, so [seq_vertices] is MathComp's sequence
    support [[set:: s]] itself, and [seq_vertices_nodes] / [seq_vertices_val]
    state its exact correspondence with the packaged upstream paths: the
    head-plus-tail convention [x :: s] of [nodes] is [seq_vertices (x :: s)].

    Specification of [seq_vertices s], every clause proved below:
    - membership: [(v \in seq_vertices s) = (v \in s)];
    - degenerate sequences: [[::]] gives [set0], [[:: v]] gives [[set v]], and
      [seq_vertices s == set0] holds exactly when [s] is empty;
    - repeated vertices are counted once and the order of [s] is irrelevant:
      invariance under [undup], [rev], [rot] and permutations, and
      [#|seq_vertices s| = size (undup s)], so [#|seq_vertices s| = size s]
      holds exactly when [s] is [uniq];
    - a head-plus-tail sequence [x :: s] contains its head [x] and its last
      vertex [last x s], so it is never empty.
    No walk, path, uniqueness or nonemptiness premise is part of the definition:
    such conditions belong to the predicates that use it. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The vertex set of a sequence *)

Section SeqVertices.
Variable T : finType.
Implicit Types (s : seq T) (u v x : T) (A : {set T}).

(** The set of the vertices occurring in [s]: MathComp's support [[set:: s]]. *)
Definition seq_vertices s : {set T} := [set:: s].

(** The comprehension form, used verbatim by the corpus-local copies. *)
Lemma seq_verticesE s : seq_vertices s = [set v | v \in s].
Proof. by []. Qed.

Lemma in_seq_vertices s v : (v \in seq_vertices s) = (v \in s).
Proof. by rewrite inE. Qed.

Lemma seq_vertices_nil : seq_vertices [::] = set0.
Proof. exact: set_nil. Qed.

Lemma seq_vertices_seq1 v : seq_vertices [:: v] = [set v].
Proof. exact: set_seq1. Qed.

Lemma seq_vertices_cons v s : seq_vertices (v :: s) = v |: seq_vertices s.
Proof. exact: set_cons. Qed.

Lemma seq_vertices_rcons s v : seq_vertices (rcons s v) = v |: seq_vertices s.
Proof. by apply/setP => u; rewrite !inE mem_rcons inE. Qed.

Lemma seq_vertices_cat s1 s2 :
  seq_vertices (s1 ++ s2) = seq_vertices s1 :|: seq_vertices s2.
Proof. by apply/setP => u; rewrite !inE mem_cat. Qed.

(** Only the membership predicate of [s] matters. *)
Lemma eq_seq_vertices s1 s2 : s1 =i s2 -> seq_vertices s1 = seq_vertices s2.
Proof. by move=> eq12; apply/setP => u; rewrite !inE eq12. Qed.

Lemma seq_vertices_eqP s1 s2 :
  reflect (s1 =i s2) (seq_vertices s1 == seq_vertices s2).
Proof.
apply: (iffP eqP) => [eq12 u|]; last exact: eq_seq_vertices.
by rewrite -!in_seq_vertices eq12.
Qed.

Lemma perm_seq_vertices s1 s2 :
  perm_eq s1 s2 -> seq_vertices s1 = seq_vertices s2.
Proof. by move/perm_mem; exact: eq_seq_vertices. Qed.

Lemma seq_vertices_rev s : seq_vertices (rev s) = seq_vertices s.
Proof. exact/eq_seq_vertices/mem_rev. Qed.

Lemma seq_vertices_rot n s : seq_vertices (rot n s) = seq_vertices s.
Proof. exact/eq_seq_vertices/mem_rot. Qed.

(** Repeated vertices are counted once. *)
Lemma seq_vertices_undup s : seq_vertices (undup s) = seq_vertices s.
Proof. exact/eq_seq_vertices/mem_undup. Qed.

Lemma seq_vertices_eq0 s : (seq_vertices s == set0) = (s == [::]).
Proof.
case: s => [|v s]; first by rewrite seq_vertices_nil eqxx.
by apply/negbTE/set0Pn; exists v; rewrite in_seq_vertices mem_head.
Qed.

Lemma card_seq_vertices s : #|seq_vertices s| = size (undup s).
Proof.
rewrite (eq_card (in_seq_vertices s)) -(eq_card (mem_undup s)).
exact/card_uniqP/undup_uniq.
Qed.

Lemma card_seq_vertices_le s : #|seq_vertices s| <= size s.
Proof. by rewrite card_seq_vertices size_undup. Qed.

Lemma card_seq_verticesP s : reflect (#|seq_vertices s| = size s) (uniq s).
Proof. by rewrite (eq_card (in_seq_vertices s)); exact: card_uniqP. Qed.

Lemma sub_seq_vertices s1 s2 :
  {subset s1 <= s2} -> seq_vertices s1 \subset seq_vertices s2.
Proof. by move=> sub; apply/subsetP => u; rewrite !in_seq_vertices; exact: sub. Qed.

Lemma seq_vertices_subsetP s A :
  reflect {subset s <= A} (seq_vertices s \subset A).
Proof.
apply: (iffP subsetP) => sub v; first by rewrite -in_seq_vertices; exact: sub.
by rewrite in_seq_vertices; exact: sub.
Qed.

Lemma seq_vertices_disjointP s A :
  reflect (forall v, v \in s -> v \notin A) [disjoint seq_vertices s & A].
Proof. by rewrite (eq_disjoint (in_seq_vertices s)) disjoint_has; exact: hasPn. Qed.

(** The head-plus-tail convention [x :: s] (that of [nodes]) is never empty. *)
Lemma seq_vertices_head x s : x \in seq_vertices (x :: s).
Proof. by rewrite in_seq_vertices mem_head. Qed.

Lemma seq_vertices_last x s : last x s \in seq_vertices (x :: s).
Proof. by rewrite in_seq_vertices mem_last. Qed.

End SeqVertices.

Lemma seq_vertices_map (aT rT : finType) (f : aT -> rT) (s : seq aT) :
  seq_vertices (map f s) = f @: seq_vertices s.
Proof.
apply/setP => y; rewrite in_seq_vertices; apply/mapP/imsetP => -[x xs ->];
  by exists x; rewrite ?in_seq_vertices in xs *.
Qed.

(** ** Correspondence with the packaged paths of coq-graph-theory *)

Section UpstreamPaths.
Variables (G : relType) (x y : G).

(** The vertex set of a packaged path [p] is the support of its vertex list. *)
Lemma seq_vertices_nodes (p : Path x y) : seq_vertices (nodes p) = [set z in p].
Proof. by apply/setP => z; rewrite [RHS]inE in_seq_vertices mem_path. Qed.

(** The same set in the head-plus-tail form [x :: val p]. *)
Lemma seq_vertices_val (p : Path x y) : seq_vertices (x :: val p) = [set z in p].
Proof. by rewrite -nodesE seq_vertices_nodes. Qed.

End UpstreamPaths.

Lemma seq_vertices_idp (G : relType) (x : G) : seq_vertices (nodes (idp x)) = [set x].
Proof. by rewrite nodesE seq_vertices_seq1. Qed.

Lemma seq_vertices_edgep (G : relType) (x y : G) (xy : x -- y) :
  seq_vertices (nodes (edgep xy)) = [set x; y].
Proof. by rewrite nodesE seq_vertices_cons seq_vertices_seq1. Qed.

(** ** Grounding

    Small models over ['I_3], with the three vertices [o0], [o1], [o2]: the
    empty sequence, a singleton, a repeated vertex, a permuted sequence, an
    absent vertex and an empty-tail head-plus-tail sequence. *)

Section Grounding.
Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma seq_vertices_ground_nil : seq_vertices ([::] : seq 'I_3) = set0.
Proof. exact: seq_vertices_nil. Qed.

Lemma seq_vertices_ground_seq1 : seq_vertices [:: o1] = [set o1].
Proof. exact: seq_vertices_seq1. Qed.

(** A repeated vertex counts once: three entries, two vertices. *)
Lemma seq_vertices_ground_repeat : seq_vertices [:: o0; o1; o0] = [set o0; o1].
Proof. by apply/setP => z; rewrite in_seq_vertices !inE orbA orbC orbA orbb orbC. Qed.

Lemma seq_vertices_ground_repeat_card :
  #|seq_vertices [:: o0; o1; o0]| = 2 /\ size [:: o0; o1; o0] = 3.
Proof. by rewrite card_seq_vertices. Qed.

Lemma seq_vertices_ground_repeat_not_uniq :
  #|seq_vertices [:: o0; o1; o0]| != size [:: o0; o1; o0].
Proof. by apply/eqP/card_seq_verticesP. Qed.

Lemma seq_vertices_ground_perm : seq_vertices [:: o0; o1] = seq_vertices [:: o1; o0].
Proof. by apply: perm_seq_vertices. Qed.

(** Negative examples: an absent vertex, and the empty sequence versus a
    singleton. *)
Lemma seq_vertices_ground_absent : o2 \notin seq_vertices [:: o0; o1; o0].
Proof. by rewrite in_seq_vertices. Qed.

Lemma seq_vertices_ground_nil_neq : seq_vertices ([::] : seq 'I_3) != seq_vertices [:: o0].
Proof. by apply/seq_vertices_eqP => /(_ o0); rewrite inE. Qed.

(** Membership is decided by computation on the sequence. *)
Lemma seq_vertices_ground_compute :
  [&& o0 \in seq_vertices [:: o2; o0], o2 \in seq_vertices [:: o2; o0]
    & o1 \notin seq_vertices [:: o2; o0]].
Proof. by rewrite !in_seq_vertices. Qed.

(** The head-plus-tail convention with an empty tail is the singleton head. *)
Lemma seq_vertices_ground_head_tail_nil : seq_vertices (o2 :: [::]) = [set o2].
Proof. exact: seq_vertices_seq1. Qed.

End Grounding.

(** ** Internal vertices of a sequence

    [seq_interior x y s] is the set of the vertices of [s] other than [x] and
    [y]: the raw-sequence counterpart of coq-graph-theory's [interior p], which
    for a packaged [p : Path x y] is [[set z in p] :\: [set x; y]]
    ([seq_interior_nodes]).  The two endpoints are given, not read off [s], and
    there is no walk, uniqueness or nonemptiness premise.  [seq_inner s] instead
    removes the first and the last entry of a nonempty [s], and is [set0] on the
    empty sequence; on a packaged path it is again [interior p]
    ([seq_inner_nodes]).

    Specification, every clause proved below:
    - membership: [(z \in seq_interior x y s) = [&& z \in s, z != x & z != y]]
      and [(z \in seq_inner s) = [&& z \in s, z != head z s & z != last z s]];
    - degenerate inputs: no internal vertex in [[::]]; [[:: v]] keeps [v] in
      [seq_interior x y] unless [v] is an endpoint, and [seq_inner [:: v]] is
      [set0];
    - repeated vertices count once and the order of [s] is irrelevant for
      [seq_interior]; equal endpoints remove one value; absent endpoints remove
      nothing; the head-plus-tail sequence [x :: s] has the same internal
      vertices as [s];
    - endpoints are removed as VALUES: an endpoint value that occurs again
      inside [s] is not internal.  A positional notion (dropping the first and
      the last position) differs exactly there. *)

Section SeqInterior.
Variable T : finType.
Implicit Types (s : seq T) (a v x y z : T).

(** The vertices of [s] other than the endpoints [x] and [y]. *)
Definition seq_interior x y s : {set T} := seq_vertices s :\: [set x; y].

(** The vertices of [s] other than its first and its last entry. *)
Definition seq_inner s : {set T} :=
  if s is a :: t then seq_interior a (last a t) s else set0.

Lemma in_seq_interior x y s z :
  (z \in seq_interior x y s) = [&& z \in s, z != x & z != y].
Proof. by rewrite !inE negb_or andbC andbA. Qed.

Lemma seq_interior_sub x y s : seq_interior x y s \subset seq_vertices s.
Proof. exact: subsetDl. Qed.

Lemma seq_interiorC x y s : seq_interior x y s = seq_interior y x s.
Proof. by rewrite /seq_interior setUC. Qed.

Lemma seq_interior_nil x y : seq_interior x y [::] = set0.
Proof. by rewrite /seq_interior seq_vertices_nil set0D. Qed.

Lemma seq_interior_seq1 x y v :
  seq_interior x y [:: v] = if (v == x) || (v == y) then set0 else [set v].
Proof.
apply/setP => z; rewrite in_seq_interior mem_seq1.
case: ifP => [|/norP[vx vy]]; last by rewrite inE; case: (z =P v) => [->|] //=; rewrite vx vy.
by case/orP=> /eqP <-; rewrite inE; case: (z =P _) => [->|] //=; rewrite ?eqxx ?andbF.
Qed.

(** The head-plus-tail convention [x :: s] does not change the interior. *)
Lemma seq_interior_head x y s : seq_interior x y (x :: s) = seq_interior x y s.
Proof.
apply/setP => z; rewrite !in_seq_interior inE.
by case: (altP (z =P x)) => [->|]; rewrite ?eqxx ?andbF.
Qed.

Lemma seq_interior_rcons x y s : seq_interior x y (rcons s y) = seq_interior x y s.
Proof.
apply/setP => z; rewrite !in_seq_interior mem_rcons inE.
by case: (altP (z =P y)) => [->|]; rewrite ?eqxx ?andbF.
Qed.

Lemma eq_seq_interior x y s1 s2 :
  s1 =i s2 -> seq_interior x y s1 = seq_interior x y s2.
Proof. by move/eq_seq_vertices => e; rewrite /seq_interior e. Qed.

Lemma seq_interior_undup x y s : seq_interior x y (undup s) = seq_interior x y s.
Proof. exact/eq_seq_interior/mem_undup. Qed.

(** Equal endpoints remove one value; absent endpoints remove nothing. *)
Lemma seq_interior_xx x s : seq_interior x x s = seq_vertices s :\ x.
Proof. by rewrite /seq_interior setUid. Qed.

Lemma seq_interior_absent x y s :
  x \notin s -> y \notin s -> seq_interior x y s = seq_vertices s.
Proof.
move=> xs ys; apply/setP => z; rewrite in_seq_interior in_seq_vertices.
by case: (boolP (z \in s)) => //= zs; rewrite (memPn xs) ?(memPn ys).
Qed.

Lemma in_seq_inner s z :
  (z \in seq_inner s) = [&& z \in s, z != head z s & z != last z s].
Proof.
case: s => [|a t]; first by rewrite /seq_inner inE.
by rewrite /seq_inner in_seq_interior.
Qed.

Lemma seq_inner_nil : seq_inner [::] = set0.
Proof. by []. Qed.

Lemma seq_inner_seq1 v : seq_inner [:: v] = set0.
Proof. by rewrite /= seq_interior_seq1 eqxx. Qed.

Lemma seq_inner_cons a t : seq_inner (a :: t) = seq_interior a (last a t) (a :: t).
Proof. by []. Qed.

Lemma seq_inner_sub s : seq_inner s \subset seq_vertices s.
Proof. by case: s => [|a t] /=; [rewrite sub0set | exact: seq_interior_sub]. Qed.

End SeqInterior.

(** Correspondence with the interior of the library's packaged paths. *)
Section UpstreamInterior.
Variables (G : relType) (x y : G).

Lemma seq_interior_nodes (p : Path x y) : seq_interior x y (nodes p) = interior p.
Proof. by rewrite /seq_interior seq_vertices_nodes. Qed.

Lemma seq_interior_val (p : Path x y) : seq_interior x y (x :: val p) = interior p.
Proof. by rewrite -nodesE seq_interior_nodes. Qed.

Lemma seq_inner_nodes (p : Path x y) : seq_inner (nodes p) = interior p.
Proof. by rewrite nodesE /= path_last -nodesE seq_interior_nodes. Qed.

End UpstreamInterior.

(** *** Grounding of the internal vertices

    The same three vertices [o0], [o1], [o2] of ['I_3]: the empty sequence, an
    endpoint and a non-endpoint singleton, a path, an endpoint value repeated
    inside the sequence, equal endpoints, absent endpoints, and the head-plus-tail
    form; then [seq_inner] on the empty, singleton, path and closed-walk
    sequences. *)

Section InteriorGrounding.
Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma seq_interior_ground_nil : seq_interior o0 o1 [::] = set0.
Proof. exact: seq_interior_nil. Qed.

Lemma seq_interior_ground_seq1_endpoint : seq_interior o0 o1 [:: o0] = set0.
Proof. by rewrite seq_interior_seq1. Qed.

Lemma seq_interior_ground_seq1_inner : seq_interior o0 o1 [:: o2] = [set o2].
Proof. by rewrite seq_interior_seq1. Qed.

Lemma seq_interior_ground_path : seq_interior o0 o2 [:: o0; o1; o2] = [set o1].
Proof. by apply/setP => z; rewrite in_seq_interior !inE; case: z => [[|[|[|]]] ?]. Qed.

(** An endpoint value repeated inside the sequence is not internal: removing the
    first and the last position of [[:: o0; o0; o1]] would keep [o0]. *)
Lemma seq_interior_ground_repeated_endpoint : seq_interior o0 o1 [:: o0; o0; o1] = set0.
Proof. by apply/setP => z; rewrite in_seq_interior !inE; case: z => [[|[|[|]]] ?]. Qed.

Lemma seq_interior_ground_equal_endpoints : seq_interior o0 o0 [:: o0; o1; o0] = [set o1].
Proof. by apply/setP => z; rewrite in_seq_interior !inE; case: z => [[|[|[|]]] ?]. Qed.

Lemma seq_interior_ground_absent_endpoints : seq_interior o0 o0 [:: o1; o2] = [set o1; o2].
Proof. by rewrite seq_interior_absent // seq_vertices_cons seq_vertices_seq1. Qed.

Lemma seq_interior_ground_head_tail : seq_interior o0 o2 (o0 :: [:: o1; o2]) = [set o1].
Proof. by rewrite seq_interior_head; apply/setP => z; rewrite in_seq_interior !inE; case: z => [[|[|[|]]] ?]. Qed.

Lemma seq_inner_ground_nil : seq_inner ([::] : seq 'I_3) = set0.
Proof. exact: seq_inner_nil. Qed.

Lemma seq_inner_ground_seq1 : seq_inner [:: o1] = set0.
Proof. exact: seq_inner_seq1. Qed.

Lemma seq_inner_ground_path : seq_inner [:: o0; o1; o2] = [set o1].
Proof. exact: seq_interior_ground_path. Qed.

Lemma seq_inner_ground_closed_walk : seq_inner [:: o0; o1; o0] = [set o1].
Proof. exact: seq_interior_ground_equal_endpoints. Qed.

End InteriorGrounding.

(** ** Consecutive entries of a sequence

    [seq_consecutive s u v] states that [u] and [v] are adjacent entries of the
    raw sequence [s], in either order: the pair [(u, v)] or the pair [(v, u)]
    occurs in [zip s (behead s)], the list of the pairs of adjacent entries of
    [s].  The codomain is [Prop]; [seq_consecutiveP] reflects it to MathComp's
    [infix [:: u; v] s || infix [:: v; u] s]: two values are consecutive exactly
    when [[:: u; v]] or [[:: v; u]] occurs contiguously in [s].

    Upstream audit (2026-10-02; MathComp 2.5.0, coq-graph-theory 0.9.7).
    MathComp's [path e x s] asks every adjacent pair of [x :: s] to satisfy
    [e], and [infix] (with [infixP] and [infix_rev]) decides contiguous
    occurrence; neither library names the relation "u and v are adjacent
    entries of s".  coq-graph-theory's packaged [Path x y] has no such notion
    either: its vertex list [nodes p] is a MathComp path of the edge relation,
    so its consecutive entries are adjacent ([seq_consecutive_nodes]).

    Specification, every clause proved below:
    - pair form: [((u, v) \in zip s (behead s)) = infix [:: u; v] s]
      ([mem_zip_behead]) and the reflection [seq_consecutiveP];
    - symmetry in [u] and [v];
    - degenerate sequences: the empty and the one-entry sequences have no
      consecutive pair, [[:: x; y]] relates exactly [x] and [y], and a repeated
      adjacent entry relates a value to itself ([seq_consecutive_repeat]);
    - recursion on [[:: x, y & s]], invariance under [rev], monotonicity under
      [cons], [rcons], concatenation and [map], and both values occur in [s];
    - the pair closing a cyclic sequence (its last and first entries) is not
      consecutive unless it also occurs adjacently;
    - no graph-edge, path, uniqueness or distinct-endpoint premise: on a
      MathComp path consecutive entries are related ([seq_consecutive_path]),
      but on a raw sequence they need not be. *)

Section SeqConsecutive.
Variable T : eqType.
Implicit Types (s : seq T) (u v x y : T).

(** [u] and [v] are adjacent entries of [s], in either order. *)
Definition seq_consecutive s u v : Prop :=
  ((u, v) \in zip s (behead s)) \/ ((v, u) \in zip s (behead s)).

Lemma mem_zip_behead s u v : ((u, v) \in zip s (behead s)) = infix [:: u; v] s.
Proof.
elim: s => [|x s IH]; first by rewrite infixs0.
case: s IH => [|y s] IH; first by rewrite /= andbF.
rewrite [zip _ _]/= in_cons xpair_eqE infix_consl -IH.
by case: s {IH} => [|z s]; rewrite /= ?andbT.
Qed.

Lemma seq_consecutiveP s u v :
  reflect (seq_consecutive s u v) (infix [:: u; v] s || infix [:: v; u] s).
Proof. by rewrite -!mem_zip_behead; apply: orP. Qed.

Lemma seq_consecutiveE s u v :
  seq_consecutive s u v <-> infix [:: u; v] s \/ infix [:: v; u] s.
Proof. by rewrite /seq_consecutive !mem_zip_behead. Qed.

Lemma seq_consecutive_sym s u v : seq_consecutive s u v <-> seq_consecutive s v u.
Proof. by split=> -[]; [right | left | right | left]. Qed.

Lemma seq_consecutive_nil u v : ~ seq_consecutive [::] u v.
Proof. by case. Qed.

Lemma seq_consecutive_seq1 x u v : ~ seq_consecutive [:: x] u v.
Proof. by case. Qed.

Lemma seq_consecutive_cons2 x y s u v :
  seq_consecutive [:: x, y & s] u v <->
  [\/ u = x /\ v = y, u = y /\ v = x | seq_consecutive (y :: s) u v].
Proof.
rewrite /seq_consecutive /= !in_cons !xpair_eqE.
split=> [[/orP[/andP[/eqP-> /eqP->]|uv]|/orP[/andP[/eqP-> /eqP->]|vu]]|].
- by constructor 1.
- by constructor 3; left.
- by constructor 2.
- by constructor 3; right.
case=> [[-> ->]|[-> ->]|[uv|vu]]; rewrite ?eqxx.
- by left.
- by right.
- by left; rewrite uv orbT.
- by right; rewrite vu orbT.
Qed.

Lemma seq_consecutive_pair x y u v :
  seq_consecutive [:: x; y] u v <-> (u = x /\ v = y) \/ (u = y /\ v = x).
Proof.
rewrite seq_consecutive_cons2; split; last by case=> ?; [constructor 1 | constructor 2].
by case=> [?|?|/seq_consecutive_seq1]; [left | right |].
Qed.

(** A repeated adjacent entry relates a value to itself. *)
Lemma seq_consecutive_repeat x s : seq_consecutive [:: x, x & s] x x.
Proof. by apply/seq_consecutive_cons2; constructor 1. Qed.

Lemma seq_consecutive_rev s u v : seq_consecutive (rev s) u v <-> seq_consecutive s u v.
Proof.
have rv a b : infix [:: a; b] (rev s) = infix [:: b; a] s by rewrite -[RHS]infix_rev.
rewrite !seq_consecutiveE !rv.
by split=> -[]; [right | left | right | left].
Qed.

Lemma seq_consecutive_mem s u v : seq_consecutive s u v -> u \in s /\ v \in s.
Proof.
by case/seq_consecutiveE => /infixP[s1 [s2 ->]]; rewrite !(mem_cat, inE, eqxx, orbT).
Qed.

Lemma seq_consecutive_cat s1 s2 u v :
  seq_consecutive s1 u v \/ seq_consecutive s2 u v -> seq_consecutive (s1 ++ s2) u v.
Proof.
rewrite !seq_consecutiveE => -[] [] /infixP[t1 [t2 ->]].
- by left; apply/infixP; exists t1, (t2 ++ s2); rewrite -!catA.
- by right; apply/infixP; exists t1, (t2 ++ s2); rewrite -!catA.
- by left; apply/infixP; exists (s1 ++ t1), t2; rewrite -!catA.
- by right; apply/infixP; exists (s1 ++ t1), t2; rewrite -!catA.
Qed.

Lemma seq_consecutive_cons x s u v :
  seq_consecutive s u v -> seq_consecutive (x :: s) u v.
Proof. by move=> uv; rewrite -cat1s; apply: seq_consecutive_cat; right. Qed.

Lemma seq_consecutive_rcons x s u v :
  seq_consecutive s u v -> seq_consecutive (rcons s x) u v.
Proof. by move=> uv; rewrite -cats1; apply: seq_consecutive_cat; left. Qed.

(** On a MathComp path, consecutive entries are related one way or the other;
    for a symmetric relation, they are related. *)
Lemma seq_consecutive_path (e : rel T) x s u v :
  path e x s -> seq_consecutive (x :: s) u v -> e u v || e v u.
Proof.
elim: s x => [|y s IH] x; first by move=> _ /seq_consecutive_seq1.
rewrite /= => /andP[xy ys] /seq_consecutive_cons2[[-> ->]|[-> ->]|/(IH y ys)//].
- by rewrite xy.
- by rewrite xy orbT.
Qed.

Lemma seq_consecutive_path_sym (e : rel T) x s u v :
  symmetric e -> path e x s -> seq_consecutive (x :: s) u v -> e u v.
Proof. by move=> esym p /(seq_consecutive_path p); rewrite (esym v) orbb. Qed.

End SeqConsecutive.

(** Consecutive entries are preserved by a map of the values. *)
Lemma seq_consecutive_map (T T' : eqType) (f : T -> T') (s : seq T) (u v : T) :
  seq_consecutive s u v -> seq_consecutive (map f s) (f u) (f v).
Proof.
rewrite !seq_consecutiveE => -[] /infixP[t1 [t2 ->]]; rewrite !map_cat.
- by left; apply/infixP; exists (map f t1), (map f t2).
- by right; apply/infixP; exists (map f t1), (map f t2).
Qed.

(** Consecutive vertices of the library's packaged paths are adjacent. *)
Section UpstreamConsecutive.
Variables (G : relType) (x y : G).

Lemma seq_consecutive_nodes (p : Path x y) u v :
  seq_consecutive (nodes p) u v -> (u -- v) || (v -- u).
Proof.
rewrite nodesE; apply: seq_consecutive_path.
by case/andP: (valP p).
Qed.

End UpstreamConsecutive.

(** *** Grounding of the consecutive entries

    Three vertices [o0], [o1], [o2] of ['I_3], a type with no edges at all: the
    empty and one-entry sequences, both orders of an adjacent pair, a
    non-adjacent pair of a three-entry sequence, the closing pair of a cyclic
    sequence, a repeated adjacent entry relating a vertex to itself, and a
    repeated non-adjacent value that is not related to itself. *)

Section ConsecutiveGrounding.
Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma seq_consecutive_ground_nil : ~ seq_consecutive ([::] : seq 'I_3) o0 o1.
Proof. exact: seq_consecutive_nil. Qed.

Lemma seq_consecutive_ground_seq1 : ~ seq_consecutive [:: o0] o0 o0.
Proof. exact: seq_consecutive_seq1. Qed.

Lemma seq_consecutive_ground_pair :
  seq_consecutive [:: o0; o1] o0 o1 /\ seq_consecutive [:: o0; o1] o1 o0.
Proof. by split; apply/seq_consecutive_pair; [left | right]. Qed.

Lemma seq_consecutive_ground_path : seq_consecutive [:: o0; o1; o2] o2 o1.
Proof. by apply/seq_consecutiveP. Qed.

Lemma seq_consecutive_ground_not_adjacent : ~ seq_consecutive [:: o0; o1; o2] o0 o2.
Proof. by move/seq_consecutiveP. Qed.

(** The closing pair of the cyclic sequence [o0, o1, o2] is not consecutive. *)
Lemma seq_consecutive_ground_not_cyclic : ~ seq_consecutive [:: o0; o1; o2] o2 o0.
Proof. by move/seq_consecutiveP. Qed.

Lemma seq_consecutive_ground_repeated : seq_consecutive [:: o0; o0; o1] o0 o0.
Proof. exact: seq_consecutive_repeat. Qed.

Lemma seq_consecutive_ground_repeated_apart : ~ seq_consecutive [:: o0; o1; o0] o0 o0.
Proof. by move/seq_consecutiveP. Qed.

End ConsecutiveGrounding.

(** ** Cyclically consecutive entries of a sequence

    [seq_cyclic_consecutive c u v] (a Prop) and [seq_cyclic_consecutiveb c u v]
    (a boolean) state that [u] and [v] are adjacent in the cyclic order of the raw
    sequence [c], in either order: the pair [(u, v)] or the pair [(v, u)] occurs
    in [zip c (rot 1 c)], the adjacent pairs of [c] together with the closing pair
    (last entry, first entry).  The two forms have the same disjuncts, joined by
    [\/] and by [||]; [seq_cyclic_consecutiveP] reflects one into the other, so
    both corpus interfaces are kept.

    Upstream audit (2026-10-02; MathComp 2.5.0, coq-graph-theory 0.9.7).
    MathComp's [cycle e (a :: p)] is [path e a (rcons p a)], i.e. it constrains the
    adjacent pairs of the closed sequence [a :: rcons p a]; [next] and [prev]
    describe neighbours only on duplicate-free cycles.  Neither library names the
    relation "u and v are cyclically adjacent entries of a raw sequence".  It is
    the path relation [seq_consecutive] of the closed sequence
    ([seq_cyclic_consecutive_closed]), and every MathComp [cycle] relates its
    cyclically consecutive entries ([seq_cyclic_consecutive_cycle]).

    Specification, every clause proved below:
    - closing: on [a :: p] it is [seq_consecutive (a :: rcons p a)], so the closing
      pair [(last a p, a)] is consecutive ([seq_cyclic_consecutive_last]) and every
      consecutive pair of the open sequence is ([seq_consecutive_cyclic]);
    - degenerate sequences: the empty sequence relates nothing, the one-entry
      sequence [[:: a]] relates [a] to itself (unlike [seq_consecutive]), and
      [[:: a; b]] relates exactly [a] and [b];
    - symmetry, invariance under [rot], [rotr] and [rev], preservation by [map],
      and both values occur in [c];
    - no path, graph-edge, uniqueness, size or distinctness premise: a repeated
      value may be cyclically consecutive to itself, and length guards belong to
      the hole and cycle predicates that use it. *)

Section SeqCyclicConsecutive.
Variable T : eqType.
Implicit Types (c p : seq T) (a b u v : T).

(** [u] and [v] are adjacent in the cyclic order of [c], as a boolean. *)
Definition seq_cyclic_consecutiveb c u v : bool :=
  ((u, v) \in zip c (rot 1 c)) || ((v, u) \in zip c (rot 1 c)).

(** The same relation as a proposition. *)
Definition seq_cyclic_consecutive c u v : Prop :=
  ((u, v) \in zip c (rot 1 c)) \/ ((v, u) \in zip c (rot 1 c)).

Lemma seq_cyclic_consecutiveP c u v :
  reflect (seq_cyclic_consecutive c u v) (seq_cyclic_consecutiveb c u v).
Proof. exact: orP. Qed.

Lemma zip_rcons_l (S : Type) (s : seq T) (t : seq S) (x : T) :
  size s = size t -> zip (rcons s x) t = zip s t.
Proof. by elim: s t => [|y s IH] [|z t] //= [/IH->]. Qed.

Lemma zip_nil_l (S : Type) (t : seq S) : zip ([::] : seq T) t = [::].
Proof. by case: t. Qed.

Lemma zip_nil_r (S : Type) (s : seq T) : zip s ([::] : seq S) = [::].
Proof. by case: s. Qed.

Lemma take_zip (S : Type) (s : seq T) (t : seq S) n :
  take n (zip s t) = zip (take n s) (take n t).
Proof. by elim: s t n => [|x s IH] [|y t] [|n] //=; rewrite IH. Qed.

Lemma drop_zip (S : Type) (s : seq T) (t : seq S) n :
  drop n (zip s t) = zip (drop n s) (drop n t).
Proof.
elim: s t n => [|x s IH] [|y t] [|n] //=; rewrite ?zip_nil_l ?zip_nil_r //.
by case: (drop n s).
Qed.

Lemma zip_rot (S : eqType) n (s : seq T) (t : seq S) :
  size s = size t -> zip (rot n s) (rot n t) = rot n (zip s t).
Proof.
move=> st; rewrite /rot zip_cat ?size_drop ?st //.
by rewrite take_zip drop_zip.
Qed.

(** Closing the sequence: cyclic adjacency on [a :: p] is the path adjacency of
    the closed sequence [a :: rcons p a]. *)
Lemma seq_cyclic_consecutive_closed a p u v :
  seq_cyclic_consecutive (a :: p) u v <-> seq_consecutive (a :: rcons p a) u v.
Proof.
rewrite /seq_cyclic_consecutive /seq_consecutive rot1_cons /=.
by rewrite -[a :: rcons p a]/(rcons (a :: p) a) zip_rcons_l // size_rcons.
Qed.

Lemma seq_cyclic_consecutive_sym c u v :
  seq_cyclic_consecutive c u v <-> seq_cyclic_consecutive c v u.
Proof. by split=> -[]; [right | left | right | left]. Qed.

Lemma seq_cyclic_consecutiveb_sym c u v :
  seq_cyclic_consecutiveb c u v = seq_cyclic_consecutiveb c v u.
Proof. exact: orbC. Qed.

Lemma seq_cyclic_consecutive_nil u v : ~ seq_cyclic_consecutive [::] u v.
Proof. by case. Qed.

(** A one-entry sequence relates its entry to itself. *)
Lemma seq_cyclic_consecutive_seq1 a u v :
  seq_cyclic_consecutive [:: a] u v <-> u = a /\ v = a.
Proof.
apply: (iff_trans (seq_cyclic_consecutive_closed _ _ _ _)) => /=.
apply: (iff_trans (seq_consecutive_pair _ _ _ _)).
by split; [case | left].
Qed.

Lemma seq_cyclic_consecutive_pair a b u v :
  seq_cyclic_consecutive [:: a; b] u v <-> (u = a /\ v = b) \/ (u = b /\ v = a).
Proof.
apply: (iff_trans (seq_cyclic_consecutive_closed _ _ _ _)) => /=.
apply: (iff_trans (seq_consecutive_cons2 _ _ _ _ _)).
by split=> [[?|?|/seq_consecutive_pair[?|?]]|[?|?]];
  [left | right | right | left | constructor 1 | constructor 2].
Qed.

Lemma seq_cyclic_consecutive_rot n c u v :
  seq_cyclic_consecutive (rot n c) u v <-> seq_cyclic_consecutive c u v.
Proof.
rewrite /seq_cyclic_consecutive rot_rot zip_rot ?size_rot //.
by rewrite !mem_rot.
Qed.

Lemma seq_cyclic_consecutiveb_rot n c u v :
  seq_cyclic_consecutiveb (rot n c) u v = seq_cyclic_consecutiveb c u v.
Proof. by rewrite /seq_cyclic_consecutiveb rot_rot zip_rot ?size_rot // !mem_rot. Qed.

Lemma seq_cyclic_consecutive_rotr n c u v :
  seq_cyclic_consecutive (rotr n c) u v <-> seq_cyclic_consecutive c u v.
Proof. exact: seq_cyclic_consecutive_rot. Qed.

Lemma seq_cyclic_consecutive_rev c u v :
  seq_cyclic_consecutive (rev c) u v <-> seq_cyclic_consecutive c u v.
Proof.
case: c => [|a p]; first by [].
rewrite rev_cons -rot1_cons.
apply: iff_trans (seq_cyclic_consecutive_rot _ _ _ _) _.
apply: iff_trans (seq_cyclic_consecutive_closed _ _ _ _) _.
apply: iff_trans _ (iff_sym (seq_cyclic_consecutive_closed _ _ _ _)).
have -> : a :: rcons (rev p) a = rev (a :: rcons p a) by rewrite rev_cons rev_rcons.
exact: seq_consecutive_rev.
Qed.

Lemma seq_cyclic_consecutive_mem c u v :
  seq_cyclic_consecutive c u v -> u \in c /\ v \in c.
Proof.
case: c => [|a p]; first by case.
move/seq_cyclic_consecutive_closed/seq_consecutive_mem.
by rewrite -[a :: rcons p a]/(rcons (a :: p) a) !mem_rcons !inE !orbA !orbb.
Qed.

(** Consecutive entries of the open sequence are cyclically consecutive. *)
Lemma seq_consecutive_cyclic c u v :
  seq_consecutive c u v -> seq_cyclic_consecutive c u v.
Proof.
case: c => [|a p]; first by case.
move=> uv; apply/seq_cyclic_consecutive_closed.
by rewrite -[a :: rcons p a]/(rcons (a :: p) a); apply: seq_consecutive_rcons.
Qed.

(** The closing pair: the last entry is cyclically consecutive to the first. *)
Lemma seq_cyclic_consecutive_last a p : seq_cyclic_consecutive (a :: p) (last a p) a.
Proof.
apply/seq_cyclic_consecutive_closed/seq_consecutiveE; left; apply/infixP.
exists (belast a p), [::].
by rewrite cats0 -[a :: rcons p a]/(rcons (a :: p) a) lastI -!cats1 -catA.
Qed.

(** On a MathComp cycle, cyclically consecutive entries are related one way or
    the other. *)
Lemma seq_cyclic_consecutive_cycle (e : rel T) c u v :
  cycle e c -> seq_cyclic_consecutive c u v -> e u v || e v u.
Proof.
case: c => [|a p]; first by move=> _ [].
by move=> ce /seq_cyclic_consecutive_closed; apply: seq_consecutive_path.
Qed.

End SeqCyclicConsecutive.

(** Cyclically consecutive entries are preserved by a map of the values. *)
Lemma seq_cyclic_consecutive_map (T T' : eqType) (f : T -> T') (c : seq T) (u v : T) :
  seq_cyclic_consecutive c u v -> seq_cyclic_consecutive (map f c) (f u) (f v).
Proof.
case: c => [|a p]; first by case.
move/seq_cyclic_consecutive_closed/(seq_consecutive_map f) => fuv.
by apply/seq_cyclic_consecutive_closed; rewrite -map_rcons.
Qed.

(** *** Grounding of the cyclically consecutive entries

    Vertices of ['I_3] and ['I_4], types with no edges: the empty sequence, the
    one-entry sequence relating its entry to itself, both orders of a two-entry
    sequence, the closing pair of a three-entry sequence (in both interfaces), a
    non-adjacent pair of a four-entry sequence, a value made consecutive to itself
    by the closing pair, and a repeated value that is not. *)

Section CyclicGrounding.
Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).
Local Notation q0 := (@Ordinal 4 0 isT).
Local Notation q1 := (@Ordinal 4 1 isT).
Local Notation q2 := (@Ordinal 4 2 isT).
Local Notation q3 := (@Ordinal 4 3 isT).

Lemma seq_cyclic_consecutive_ground_nil : ~ seq_cyclic_consecutive ([::] : seq 'I_3) o0 o0.
Proof. exact: seq_cyclic_consecutive_nil. Qed.

Lemma seq_cyclic_consecutive_ground_seq1 : seq_cyclic_consecutive [:: o0] o0 o0.
Proof. exact/seq_cyclic_consecutive_seq1. Qed.

Lemma seq_cyclic_consecutive_ground_pair :
  seq_cyclic_consecutive [:: o0; o1] o0 o1 /\ seq_cyclic_consecutive [:: o0; o1] o1 o0.
Proof. by split; apply/seq_cyclic_consecutive_pair; [left | right]. Qed.

Lemma seq_cyclic_consecutive_ground_closing : seq_cyclic_consecutive [:: o0; o1; o2] o2 o0.
Proof. exact: (seq_cyclic_consecutive_last o0 [:: o1; o2]). Qed.

Lemma seq_cyclic_consecutiveb_ground_closing : seq_cyclic_consecutiveb [:: o0; o1; o2] o2 o0.
Proof. by []. Qed.

Lemma seq_cyclic_consecutive_ground_not_adjacent :
  ~ seq_cyclic_consecutive [:: q0; q1; q2; q3] q0 q2.
Proof. by move/seq_cyclic_consecutiveP. Qed.

Lemma seq_cyclic_consecutive_ground_repeated : seq_cyclic_consecutive [:: o0; o1; o0] o0 o0.
Proof. by apply/seq_cyclic_consecutiveP. Qed.

Lemma seq_cyclic_consecutive_ground_repeated_apart :
  ~ seq_cyclic_consecutive [:: q0; q1; q0; q2] q0 q0.
Proof. by move/seq_cyclic_consecutiveP. Qed.

End CyclicGrounding.

(** ** Set-to-set simple paths

    [seq_set_path X Y p] states that the raw sequence [p] is a simple path from
    the vertex set [X] to the vertex set [Y]: [p] is nonempty, its first entry
    lies in [X] and its last entry in [Y], its entries are pairwise distinct, and
    consecutive entries are adjacent ([path (--)] from the first entry).

    Upstream audit (2026-10-02; coq-graph-theory 0.9.7).  [digraph.v] has, on
    tails, [pathp x y q := path (--) x q && (last x q == y)] and
    [upath x y q := uniq (x :: q) && pathp x y q], and packaged paths [Path x y]
    whose vertex list [nodes p] is [x :: val p], simple when [irred p].  A
    set-to-set path is that tail form once the head is split off:
    [seq_set_path X Y (x :: q)] holds exactly when [x \in X], [last x q \in Y] and
    [upath x (last x q) q] ([seq_set_path_upath]), and the vertex list of an
    irredundant packaged path from a vertex of [X] to a vertex of [Y] is one
    ([seq_set_path_nodes]).

    Specification, every clause proved below:
    - the empty sequence is never a path; a one-entry sequence [[:: x]] is one
      exactly when [x \in X :&: Y]; if [X] or [Y] is empty there is none;
    - repeated entries are excluded: a path is [uniq];
    - nothing else is required: [X] and [Y] may meet, the endpoints coincide for a
      one-entry path, there is no length guard, internal entries may lie in [X] or
      [Y], and enlarging [X] or [Y] keeps every path; reversing a path of a
      symmetric relation exchanges [X] and [Y]. *)

Section SeqSetPath.
Variable G : relType.
Implicit Types (X Y : {set G}) (p q : seq G) (x y : G).

(** [p] is a simple path from [X] to [Y]. *)
Definition seq_set_path X Y p : Prop :=
  match p with
  | [::] => False
  | x :: q => x \in X /\ last x q \in Y /\ uniq p /\ path (--) x q
  end.

Lemma seq_set_path_nil X Y : ~ seq_set_path X Y [::].
Proof. by []. Qed.

Lemma seq_set_path_cons X Y x q :
  seq_set_path X Y (x :: q) <->
  [/\ x \in X, last x q \in Y, uniq (x :: q) & path (--) x q].
Proof. by split=> [[xX [qY [u pq]]]|[xX qY u pq]]. Qed.

(** A one-entry path is a vertex of both sets. *)
Lemma seq_set_path_seq1 X Y x : seq_set_path X Y [:: x] <-> x \in X :&: Y.
Proof. by rewrite inE; split=> [[-> [-> _]]|/andP[xX xY]]. Qed.

Lemma seq_set_path_upath X Y x q :
  seq_set_path X Y (x :: q) <-> [/\ x \in X, last x q \in Y & upath x (last x q) q].
Proof.
rewrite /upath /pathp eqxx andbT.
by split=> [[xX [qY [u pq]]]|[xX qY /andP[u pq]]]; [split; rewrite // u pq | ].
Qed.

(** The vertex list of an irredundant packaged path from [X] to [Y]. *)
Lemma seq_set_path_nodes X Y x y (p : Path x y) :
  irred p -> x \in X -> y \in Y -> seq_set_path X Y (nodes p).
Proof.
rewrite /irred nodesE => u xX yY /=; rewrite path_last.
by do !split=> //; case/andP: (valP p).
Qed.

Lemma seq_set_path_uniq X Y p : seq_set_path X Y p -> uniq p.
Proof. by case: p => [|x q] // [_ [_ []]]. Qed.

Lemma seq_set_path_set0l Y p : ~ seq_set_path set0 Y p.
Proof. by case: p => [|x q] //; rewrite /= inE => -[]. Qed.

Lemma seq_set_path_set0r X p : ~ seq_set_path X set0 p.
Proof. by case: p => [|x q] //= [_ []]; rewrite inE. Qed.

(** Repeated entries are excluded. *)
Lemma seq_set_path_repeat X Y p : ~~ uniq p -> ~ seq_set_path X Y p.
Proof. by move=> /negP np /seq_set_path_uniq. Qed.

Lemma seq_set_path_sub X X' Y Y' p :
  X \subset X' -> Y \subset Y' -> seq_set_path X Y p -> seq_set_path X' Y' p.
Proof.
case: p => [|x q] // /subsetP sX /subsetP sY [xX [qY rest]].
by split; [exact: sX | split; [exact: sY | exact: rest]].
Qed.

(** Consecutive entries of a path are adjacent, one way or the other. *)
Lemma seq_set_path_consecutive X Y p u v :
  seq_set_path X Y p -> seq_consecutive p u v -> (u -- v) || (v -- u).
Proof. by case: p => [|x q] // [_ [_ [_ pq]]]; apply: seq_consecutive_path. Qed.

(** A path with [n] entries has [n - 1] consecutive pairs (its edges). *)
Lemma seq_set_path_size X Y p :
  seq_set_path X Y p -> size (zip p (behead p)) = (size p).-1.
Proof. by case: p => [|x q] // _; rewrite size2_zip /= ?leqnSn. Qed.

(** Reversing a path of a symmetric relation exchanges the endpoint sets. *)
Lemma seq_set_path_rev X Y p :
  symmetric (@edge_rel G) -> seq_set_path X Y p -> seq_set_path Y X (rev p).
Proof.
case: p => [|x q] // esym [xX [qY [u pq]]].
have revE : rev (x :: q) = last x q :: rev (belast x q) by rewrite lastI rev_rcons.
have lastE : last (last x q) (rev (belast x q)) = x.
  by case: q {qY u pq revE} => [|y q] //=; rewrite rev_cons last_rcons.
rewrite revE; apply/seq_set_path_cons; split; rewrite ?lastE //.
- by rewrite -revE rev_uniq.
- by rewrite rev_path (eq_path (e' := @edge_rel G)) // => a b; apply: esym.
Qed.

End SeqSetPath.

(** ** Simple whole-sequence paths

    [seq_simple_path p] states that the raw sequence [p] is a simple path: it is
    nonempty, its entries are pairwise distinct, and consecutive entries are
    adjacent.  There is no endpoint condition, and chords (adjacent entries that
    are not consecutive) are allowed: it is not an induced path.

    Upstream audit (2026-10-03; MathComp 2.5.0, coq-graph-theory 0.9.7).
    MathComp's [sorted e s] is [path e x s'] on [x :: s'] and [true] on [[::]], so
    [seq_simple_path p] is [p != [::]], [uniq p] and [sorted (--) p]
    ([seq_simple_pathE]).  coq-graph-theory's [upath x y q] is the simple path on
    a TAIL [q] from a named vertex [x] to a named vertex [y]; a nonempty whole
    sequence [x :: q] is a simple path exactly when [upath x (last x q) q]
    ([seq_simple_path_upath]): a translation that names the endpoints, not an
    equality at equal arguments.  It is the set-to-set path of
    [seq_set_path] with both endpoint sets the whole vertex set
    ([seq_simple_path_setT]), and the vertex list of an irredundant packaged path
    is one ([seq_simple_path_nodes]); a bare [Path] may repeat vertices.

    Specification, every clause proved below:
    - the empty sequence is not a path and every one-entry sequence is;
    - a two-entry sequence is a path exactly when its entries are distinct and
      adjacent; repeated entries are excluded;
    - consecutive entries are adjacent, and a path with [n] entries has [n - 1]
      consecutive pairs; nonconsecutive entries may also be adjacent;
    - reversal needs a symmetric relation, and a map keeps paths only if it is
      injective and preserves adjacency. *)

Section SeqSimplePath.
Variable G : relType.
Implicit Types (X Y : {set G}) (p q : seq G) (x y u v : G).

(** [p] is a nonempty simple path. *)
Definition seq_simple_path p : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

Lemma seq_simple_path_nil : ~ seq_simple_path [::].
Proof. by []. Qed.

Lemma seq_simple_path_seq1 x : seq_simple_path [:: x].
Proof. by []. Qed.

Lemma seq_simple_pathE p :
  seq_simple_path p <-> (p != [::]) /\ uniq p /\ sorted (--) p.
Proof.
case: p => [|x q] /=; first by split=> // -[].
by split=> [[u pq]|[_ [u pq]]]; do !split.
Qed.

Lemma seq_simple_path_upath x q :
  seq_simple_path (x :: q) <-> upath x (last x q) q.
Proof.
rewrite /upath /pathp eqxx andbT.
by split=> [[-> ->]|/andP[u pq]].
Qed.

Lemma seq_simple_path_setT p :
  seq_simple_path p <-> seq_set_path [set: G] [set: G] p.
Proof. by case: p => [|x q] //=; rewrite !inE; split=> [[u pq]|[_ [_ [u pq]]]]. Qed.

Lemma seq_set_path_simple X Y p : seq_set_path X Y p -> seq_simple_path p.
Proof. by case: p => [|x q] // [_ [_ []]]. Qed.

(** The vertex list of an irredundant packaged path. *)
Lemma seq_simple_path_nodes x y (p : Path x y) : irred p -> seq_simple_path (nodes p).
Proof.
move=> ip; apply/seq_simple_path_setT; apply: seq_set_path_nodes => //.
all: by rewrite inE.
Qed.

Lemma seq_simple_path_uniq p : seq_simple_path p -> uniq p.
Proof. by case: p => [|x q] // []. Qed.

(** Repeated entries are excluded. *)
Lemma seq_simple_path_repeat p : ~~ uniq p -> ~ seq_simple_path p.
Proof. by move=> /negP np /seq_simple_path_uniq. Qed.

Lemma seq_simple_path_pair x y : seq_simple_path [:: x; y] <-> x != y /\ x -- y.
Proof. by rewrite /= !inE !andbT; split=> [[xy e]|[xy e]]. Qed.

(** Consecutive entries of a path are adjacent, one way or the other. *)
Lemma seq_simple_path_consecutive p u v :
  seq_simple_path p -> seq_consecutive p u v -> (u -- v) || (v -- u).
Proof. by case: p => [|x q] // [_ pq]; apply: seq_consecutive_path. Qed.

(** A path with [n] entries has [n - 1] consecutive pairs (its edges). *)
Lemma seq_simple_path_size p :
  seq_simple_path p -> size (zip p (behead p)) = (size p).-1.
Proof. by case: p => [|x q] // _; rewrite size2_zip /= ?leqnSn. Qed.

Lemma seq_simple_path_rev p :
  symmetric (@edge_rel G) -> seq_simple_path p -> seq_simple_path (rev p).
Proof.
move=> esym /seq_simple_path_setT/(seq_set_path_rev esym) rp.
exact/seq_simple_path_setT.
Qed.

End SeqSimplePath.

(** An injective map preserving adjacency keeps simple paths. *)
Lemma seq_simple_path_map (G G' : relType) (f : G -> G') (p : seq G) :
  injective f -> {homo f : x y / x -- y} ->
  seq_simple_path p -> seq_simple_path (map f p).
Proof.
move=> finj fhom; case: p => [|x q] // [u pq].
have hu : uniq (map f (x :: q)) by rewrite (map_inj_uniq finj).
have hp : path (--) (f x) (map f q) by rewrite path_map; apply: sub_path pq => a b /fhom.
by split.
Qed.

(** ** Simple walks of a sequence (empty allowed)

    [seq_simple_walk s] is the boolean [uniq s && sorted (--) s]: the entries of
    [s] are pairwise distinct and consecutive entries are adjacent.  Unlike the
    path predicate [seq_simple_path] above, the EMPTY sequence is accepted: the
    two differ exactly there ([seq_simple_path_walk]).

    Upstream audit (2026-10-03; MathComp 2.5.0, coq-graph-theory 0.9.7).
    MathComp's [sorted e s] is [path e x s'] on [x :: s'] and [true] on [[::]];
    with [uniq] it is the whole-sequence form of coq-graph-theory's tail
    predicate [upath x y q]: on [x :: q] it is [upath x (last x q) q]
    ([seq_simple_walk_upath]).

    Specification, every clause proved below:
    - the empty sequence and every one-entry sequence are simple walks;
    - a two-entry sequence is one exactly when its entries are distinct and
      adjacent; repeated entries are excluded;
    - a nonempty simple walk is a simple path, and conversely. *)

Section SeqSimpleWalk.
Variable G : relType.
Implicit Types (p q s : seq G) (x y : G).

(** [s] is a duplicate-free walk; the empty sequence is one. *)
Definition seq_simple_walk s : bool := uniq s && sorted (--) s.

Lemma seq_simple_walk_nil : seq_simple_walk [::].
Proof. by []. Qed.

Lemma seq_simple_walk_seq1 x : seq_simple_walk [:: x].
Proof. by []. Qed.

Lemma seq_simple_walk_uniq s : seq_simple_walk s -> uniq s.
Proof. by case/andP. Qed.

Lemma seq_simple_walk_sorted s : seq_simple_walk s -> sorted (--) s.
Proof. by case/andP. Qed.

(** Repeated entries are excluded. *)
Lemma seq_simple_walk_repeat s : ~~ uniq s -> ~~ seq_simple_walk s.
Proof. by apply: contra => /seq_simple_walk_uniq. Qed.

Lemma seq_simple_walk_pair x y : seq_simple_walk [:: x; y] = (x != y) && (x -- y).
Proof. by rewrite /seq_simple_walk /= !inE !andbT. Qed.

(** The nonempty distinction with [seq_simple_path]. *)
Lemma seq_simple_path_walk s : seq_simple_path s <-> s != [::] /\ seq_simple_walk s.
Proof.
rewrite seq_simple_pathE /seq_simple_walk.
by split=> [[-> [-> ->]]|[-> /andP[-> ->]]].
Qed.

Lemma seq_simple_walk_path s : seq_simple_walk s <-> s = [::] \/ seq_simple_path s.
Proof.
case: s => [|x q]; first by split=> // _; left.
split=> [w|[//|/seq_simple_path_walk[_ //]]].
by right; apply/seq_simple_path_walk.
Qed.

Lemma seq_simple_walk_upath x q : seq_simple_walk (x :: q) = upath x (last x q) q.
Proof. by rewrite /seq_simple_walk /upath /pathp eqxx andbT. Qed.

End SeqSimpleWalk.

(** ** Edges traversed by a sequence

    Three edge extractors of a vertex sequence, kept as separate contracts (registry
    meta/library_primitives/path-edges.json):
    - [seq_edge_list s] is the ORDERED list of the unordered consecutive pairs
      [[set s_i; s_(i+1)]], one entry per adjacent pair of [s]: repeated traversals stay
      repeated and the order of traversal is kept;
    - [seq_edge_set s] is its finite support [[set e in seq_edge_list s]], which is also the
      existential image of the consecutive pairs ([seq_edge_set_image]);
    - [seq_index_edge_set p] (simple graphs) collects the ACTUAL edges [[set x; y]] of the
      graph whose ends occur in [p] and whose FIRST occurrences in [p] are adjacent
      positions ([seq_index_consecutive]).
    The first two read the sequence alone: there is no adjacency, irreflexivity, uniqueness
    or nonemptiness filter, so a non-adjacent pair [[:: a; b]] still yields [[set a; b]] and
    a repetition [[:: a; a]] yields the one-vertex set [[set a]]; only a walk premise puts
    their members in the edge set [E(G)] ([seq_edge_set_sorted]).  The third filters by
    adjacency but locates entries through [index], which sees first occurrences only: it is
    [seq_edge_set p :&: E(G)] on duplicate-free [p] and [seq_edge_set p] on duplicate-free
    walks, but in general it is neither (grounding: [[:: o0; o1; o0; o2]] in ['K_3]), and it
    is not invariant under reversal.

    Upstream audit (2026-10-03; MathComp 2.5.0, coq-graph-theory 0.9.7).  coq-graph-theory
    packages walks as [Path x y] with vertex list [nodes p] ([digraph.v]) and writes the edge
    set of a simple graph as [E(G)] ([sg_edge_set], the sets [[set x; y]] with [x -- y];
    [in_edges], [edgesP]; [sgraph.v]); [mgraph.walk] traverses explicit edge objects of a
    multigraph.  Neither library has the list or the set of the unordered consecutive pairs
    of a raw vertex sequence, nor a first-index variant, so these are new.  [E(G)] is the
    target of the walk bridges: the edges of a walk, in particular of the vertex list of a
    packaged path ([seq_edge_set_nodes]), are edges of [G].

    Specification, every clause proved below:
    - membership: [e] is listed exactly when [e = [set u; v]] for a pair [(u, v)] of
      [zip s (behead s)], equivalently for consecutive entries [u], [v] ([seq_consecutive]);
      the support has the same members;
    - degenerate sequences: [[::]] and [[:: x]] have no edge; [[:: x; y]] has exactly
      [[set x; y]], also when [x] and [y] are not adjacent, and [[set x]] when [x = y];
    - multiplicity and order: the list has [(size s).-1] entries, [[:: x, y & s]] lists
      [[set x; y]] before the edges of [y :: s], [[:: x; y; x]] lists [[set x; y]] twice
      while its support has it once, and reversal reverses the list and keeps the support;
    - the support has at most [(size s).-1] elements, each a subset of [seq_vertices s];
    - walks: on [sorted (--) s], on [x :: s] with [path (--) x s] and on [nodes p] every
      edge is in [E(G)];
    - first-index edges: always in [E(G)]; none on [[::]], on one-entry sequences or on a
      non-adjacent pair; on duplicate-free [p] exactly [seq_edge_set p :&: E(G)], hence
      [seq_edge_set p] when [p] is a duplicate-free walk ([seq_simple_walk], so also
      [seq_simple_path]); the endpoint membership guards are needed, since an absent vertex
      has index [size p] and is first-index adjacent to a last entry occurring once
      ([seq_index_consecutive_absent]). *)

Section SeqEdges.
Variable T : finType.
Implicit Types (s : seq T) (e : {set T}) (u v x y : T).

(** The ordered list of the unordered consecutive pairs of [s]. *)
Definition seq_edge_list s : seq {set T} :=
  map (fun e : T * T => [set e.1; e.2]) (zip s (behead s)).

(** Its finite support. *)
Definition seq_edge_set s : {set {set T}} := [set e in seq_edge_list s].

Lemma in_seq_edge_set s e : (e \in seq_edge_set s) = (e \in seq_edge_list s).
Proof. by rewrite /seq_edge_set inE. Qed.

Lemma seq_edge_listP s e :
  reflect (exists u v, (u, v) \in zip s (behead s) /\ e = [set u; v])
          (e \in seq_edge_list s).
Proof.
apply: (iffP mapP) => [[[u v] uv ->]|[u [v [uv ->]]]]; first by exists u, v.
by exists (u, v).
Qed.

Lemma seq_edge_setP s e :
  reflect (exists u v, (u, v) \in zip s (behead s) /\ e = [set u; v])
          (e \in seq_edge_set s).
Proof. by rewrite in_seq_edge_set; apply: seq_edge_listP. Qed.

(** The support is the existential image of the consecutive pairs. *)
Lemma seq_edge_set_image s :
  seq_edge_set s =
  [set e : {set T} |
     [exists xy : T * T, (xy \in zip s (behead s)) && (e == [set xy.1; xy.2])]].
Proof.
apply/setP => e; rewrite in_seq_edge_set inE.
apply/mapP/existsP => [[xy xyin ->]|[xy /andP[xyin /eqP ->]]]; exists xy => //.
by rewrite xyin eqxx.
Qed.

Lemma seq_edge_set_consecutive s u v :
  seq_consecutive s u v -> [set u; v] \in seq_edge_set s.
Proof.
case=> uv; apply/seq_edge_setP.
- by exists u, v.
- by exists v, u; rewrite setUC.
Qed.

Lemma seq_edge_set_consecutiveP s e :
  reflect (exists u v, seq_consecutive s u v /\ e = [set u; v]) (e \in seq_edge_set s).
Proof.
apply: (iffP idP) => [/seq_edge_setP[u [v [uv ->]]]|[u [v [uv ->]]]].
- by exists u, v; split => //; left.
- exact: seq_edge_set_consecutive.
Qed.

Lemma seq_edge_list_nil : seq_edge_list [::] = [::].
Proof. by []. Qed.

Lemma seq_edge_list_seq1 x : seq_edge_list [:: x] = [::].
Proof. by []. Qed.

Lemma seq_edge_list_cons2 x y s :
  seq_edge_list [:: x, y & s] = [set x; y] :: seq_edge_list (y :: s).
Proof. by []. Qed.

Lemma seq_edge_list_pair x y : seq_edge_list [:: x; y] = [:: [set x; y]].
Proof. by []. Qed.

(** A repeated entry gives the one-vertex set. *)
Lemma seq_edge_list_loop x : seq_edge_list [:: x; x] = [:: [set x]].
Proof. by rewrite seq_edge_list_pair setUid. Qed.

(** Going back and forth lists the same set twice. *)
Lemma seq_edge_list_back x y : seq_edge_list [:: x; y; x] = [:: [set x; y]; [set x; y]].
Proof. by rewrite !seq_edge_list_cons2 seq_edge_list_seq1 [[set y; x]]setUC. Qed.

Lemma seq_edge_set_nil : seq_edge_set [::] = set0.
Proof. by apply/setP => e; rewrite /seq_edge_set !inE. Qed.

Lemma seq_edge_set_seq1 x : seq_edge_set [:: x] = set0.
Proof. by apply/setP => e; rewrite /seq_edge_set !inE. Qed.

Lemma seq_edge_set_cons2 x y s :
  seq_edge_set [:: x, y & s] = [set x; y] |: seq_edge_set (y :: s).
Proof. by apply/setP => e; rewrite in_setU1 !in_seq_edge_set seq_edge_list_cons2 in_cons. Qed.

Lemma seq_edge_set_pair x y : seq_edge_set [:: x; y] = [set [set x; y]].
Proof. by rewrite seq_edge_set_cons2 seq_edge_set_seq1 setU0. Qed.

(** ... while the support has it once. *)
Lemma seq_edge_set_back x y : seq_edge_set [:: x; y; x] = [set [set x; y]].
Proof. by rewrite seq_edge_set_cons2 seq_edge_set_pair [[set y; x]]setUC setUid. Qed.

Lemma size_seq_edge_list s : size (seq_edge_list s) = (size s).-1.
Proof. by case: s => [|x s] //; rewrite size_map size2_zip /= ?leqnSn. Qed.

Lemma card_seq_edge_set s : #|seq_edge_set s| <= (size s).-1.
Proof. by rewrite /seq_edge_set cardsE -size_seq_edge_list card_size. Qed.

(** Every edge joins entries of [s]. *)
Lemma seq_edge_set_sub s e : e \in seq_edge_set s -> e \subset seq_vertices s.
Proof.
case/seq_edge_setP => u [v [uv ->]].
have [us vs] : u \in s /\ v \in s by apply: seq_consecutive_mem; left.
by apply/subsetP => z; rewrite in_seq_vertices !inE => /orP[]/eqP->.
Qed.

Lemma seq_edge_list_rcons x s y :
  seq_edge_list (rcons (x :: s) y) = rcons (seq_edge_list (x :: s)) [set last x s; y].
Proof. by rewrite /seq_edge_list; elim: s x => [|z s IH] x //=; rewrite IH. Qed.

Lemma seq_edge_list_rev s : seq_edge_list (rev s) = rev (seq_edge_list s).
Proof.
elim/last_ind: s => [|t y IH] //; case: t IH => [|x t] IH //.
rewrite rev_rcons seq_edge_list_rcons rev_rcons -IH (lastI x t) rev_rcons.
by rewrite seq_edge_list_cons2 setUC.
Qed.

Lemma seq_edge_set_rev s : seq_edge_set (rev s) = seq_edge_set s.
Proof. by apply/setP => e; rewrite !in_seq_edge_set seq_edge_list_rev mem_rev. Qed.

End SeqEdges.

Section SeqEdgesWalk.
Variable G : sgraph.
Implicit Types (s p : seq G) (e : {set G}) (x y : G).

(** On a walk every listed pair is an edge of [G]. *)
Lemma seq_edge_set_path x s : path (--) x s -> seq_edge_set (x :: s) \subset E(G).
Proof.
move=> ps; apply/subsetP => e /seq_edge_set_consecutiveP[u [v [uv ->]]].
by rewrite in_edges; apply: seq_consecutive_path_sym uv => //; apply: sg_sym.
Qed.

Lemma seq_edge_set_sorted s : sorted (--) s -> seq_edge_set s \subset E(G).
Proof. by case: s => [|x s] ps; [rewrite seq_edge_set_nil sub0set|apply: seq_edge_set_path]. Qed.

Lemma seq_edge_list_sorted s : sorted (--) s -> {subset seq_edge_list s <= E(G)}.
Proof. by move=> /seq_edge_set_sorted /subsetP sub e es; apply: sub; rewrite in_seq_edge_set. Qed.

(** The vertex list of a packaged path. *)
Lemma seq_edge_set_nodes x y (p : Path x y) : seq_edge_set (nodes p) \subset E(G).
Proof. by rewrite nodesE; apply: seq_edge_set_path; case/andP: (valP p). Qed.

Lemma seq_edge_list_edgep x y (xy : x -- y) : seq_edge_list (nodes (edgep xy)) = [:: [set x; y]].
Proof. by rewrite nodesE. Qed.

End SeqEdgesWalk.

Section SeqIndexConsecutive.
Variable T : eqType.
Implicit Types (p : seq T) (x y : T).

(** The FIRST occurrences of [x] and [y] in [p] are adjacent positions. *)
Definition seq_index_consecutive p x y : bool :=
  ((index x p).+1 == index y p) || ((index y p).+1 == index x p).

Lemma seq_index_consecutive_sym p x y :
  seq_index_consecutive p x y = seq_index_consecutive p y x.
Proof. by rewrite /seq_index_consecutive orbC. Qed.

(** On duplicate-free sequences first indices are positions, so index-adjacency
    of two entries is adjacency of the entries. *)
Lemma index_succ_zip p x y : uniq p -> x \in p -> y \in p ->
  ((index x p).+1 == index y p) = ((x, y) \in zip p (behead p)).
Proof.
elim: p => [|a q IH] //; rewrite cons_uniq => /andP[aq uq].
have ia z : index z (a :: q) = if a == z then 0 else (index z q).+1 by [].
rewrite !in_cons !ia; clear ia.
case: q IH aq uq => [|b r] IH aq uq.
  by move=> /orP[/eqP->|//] /orP[/eqP->|//]; rewrite eqxx.
have ib z : index z (b :: r) = if b == z then 0 else (index z r).+1 by [].
have ab : (a == b) = false.
  by apply/negbTE; apply: contra aq => /eqP->; exact: mem_head.
have za z : ((a, z) \in zip (b :: r) r) = false.
  apply/negbTE/negP => az.
  case: (@seq_consecutive_mem _ (b :: r) a z (or_introl az)) => abr _.
  by rewrite abr in aq.
have za' z : ((z, a) \in zip (b :: r) r) = false.
  apply/negbTE/negP => zaz.
  case: (@seq_consecutive_mem _ (b :: r) z a (or_introl zaz)) => _ abr.
  by rewrite abr in aq.
have -> : zip (a :: b :: r) (behead (a :: b :: r)) = (a, b) :: zip (b :: r) r by [].
rewrite (in_cons (a, b)) xpair_eqE.
case: (a =P x) => [<-|/eqP ax] xp; case: (a =P y) => [<-|/eqP ay] yp.
- by rewrite eqxx ab za.
- by rewrite eqxx za orbF eqSS ib [y == b]eq_sym; case: (b == y).
- by rewrite za' ab andbF.
- rewrite eqSS [x == a]eq_sym (negbTE ax) /= IH //.
  + by move: xp; rewrite [x == a]eq_sym (negbTE ax).
  + by move: yp; rewrite [y == a]eq_sym (negbTE ay).
Qed.

Lemma seq_index_consecutiveE p x y : uniq p -> x \in p -> y \in p ->
  seq_index_consecutive p x y =
  ((x, y) \in zip p (behead p)) || ((y, x) \in zip p (behead p)).
Proof. by move=> up xp yp; rewrite /seq_index_consecutive !index_succ_zip. Qed.

(** On duplicate-free sequences, first-index adjacency is adjacency of entries. *)
Lemma seq_index_consecutiveP p x y : uniq p -> x \in p -> y \in p ->
  reflect (seq_consecutive p x y) (seq_index_consecutive p x y).
Proof. by move=> up xp yp; rewrite seq_index_consecutiveE //; apply: orP. Qed.

(** An absent vertex has index [size p]: it is "index-adjacent" to a last entry
    occurring once, so membership guards are needed. *)
Lemma seq_index_consecutive_absent x y : y != x -> seq_index_consecutive [:: x] x y.
Proof. by move=> yx; rewrite /seq_index_consecutive /= eqxx [x == y]eq_sym (negbTE yx). Qed.

End SeqIndexConsecutive.

Section SeqIndexEdges.
Variable G : sgraph.
Implicit Types (p : seq G) (e : {set G}) (x y : G).

(** The actual edges of [G] between entries of [p] whose first indices are adjacent. *)
Definition seq_index_edge_set p : {set {set G}} :=
  [set e : {set G} |
    [exists x : G, [exists y : G,
      [&& x -- y, e == [set x; y], x \in p, y \in p & seq_index_consecutive p x y]]]].

Lemma seq_index_edge_setP p e :
  reflect (exists x y,
             [/\ x -- y, e = [set x; y], x \in p, y \in p & seq_index_consecutive p x y])
          (e \in seq_index_edge_set p).
Proof.
rewrite inE; apply: (iffP existsP) => [[x /existsP[y /and5P[xy /eqP-> xp yp c]]]|].
  by exists x, y.
by case=> x [y [xy -> xp yp c]]; exists x; apply/existsP; exists y; rewrite xy eqxx xp yp c.
Qed.

(** Only actual edges are collected. *)
Lemma seq_index_edge_set_sub p : seq_index_edge_set p \subset E(G).
Proof. by apply/subsetP => e /seq_index_edge_setP[x [y [xy -> _ _ _]]]; rewrite in_edges. Qed.

Lemma seq_index_edge_set_nil : seq_index_edge_set [::] = set0.
Proof. by apply/eqP; rewrite -subset0; apply/subsetP => e /seq_index_edge_setP[x [y []]]. Qed.

Lemma seq_index_edge_set_seq1 v : seq_index_edge_set [:: v] = set0.
Proof.
apply/eqP; rewrite -subset0; apply/subsetP => e /seq_index_edge_setP[x [y [xy _]]].
by rewrite !mem_seq1 => /eqP xv /eqP yv _; move: xy; rewrite xv yv sg_irrefl.
Qed.

(** On a duplicate-free sequence: the consecutive pairs that are edges. *)
Lemma seq_index_edge_set_uniq p : uniq p -> seq_index_edge_set p = seq_edge_set p :&: E(G).
Proof.
move=> up; apply/setP => e; rewrite in_setI.
apply/seq_index_edge_setP/andP => [[x [y [xy -> xp yp c]]]|[/seq_edge_setP[u [v [uv ->]]] ev]].
- split; last by rewrite in_edges.
  apply/seq_edge_set_consecutiveP; exists x, y; split => //.
  exact/(seq_index_consecutiveP up xp yp).
- have [up' vp] := @seq_consecutive_mem _ p u v (or_introl uv).
  exists u, v; split => //; first by rewrite -in_edges.
  by rewrite seq_index_consecutiveE // uv.
Qed.

(** On a duplicate-free walk it is the raw support. *)
Lemma seq_index_edge_set_walk p : seq_simple_walk p -> seq_index_edge_set p = seq_edge_set p.
Proof.
case/andP => up sp; rewrite seq_index_edge_set_uniq //.
by apply/setIidPl; apply: seq_edge_set_sorted.
Qed.

Lemma seq_index_edge_set_simple_path p :
  seq_simple_path p -> seq_index_edge_set p = seq_edge_set p.
Proof. by case/seq_simple_path_walk => _; apply: seq_index_edge_set_walk. Qed.

Lemma seq_index_edge_set_edge x y : x -- y -> seq_index_edge_set [:: x; y] = [set [set x; y]].
Proof.
move=> xy; rewrite seq_index_edge_set_walk ?seq_edge_set_pair //.
by rewrite seq_simple_walk_pair xy (sg_edgeNeq xy).
Qed.

(** Unlike the raw support, a non-edge contributes nothing. *)
Lemma seq_index_edge_set_nonedge x y : ~~ x -- y -> seq_index_edge_set [:: x; y] = set0.
Proof.
move=> nxy; apply/eqP; rewrite -subset0; apply/subsetP => e /seq_index_edge_setP[u [v [uv -> up vp _]]].
move: up vp uv; rewrite !inE => /orP[]/eqP-> /orP[]/eqP->; rewrite ?sg_irrefl //.
  by rewrite (negbTE nxy).
by rewrite sg_sym (negbTE nxy).
Qed.

End SeqIndexEdges.

Section EdgesGrounding.
Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma seq_edge_list_ground_back : seq_edge_list [:: o0; o1; o0] = [:: [set o0; o1]; [set o0; o1]].
Proof. exact: seq_edge_list_back. Qed.

Lemma seq_edge_set_ground_back : seq_edge_set [:: o0; o1; o0] = [set [set o0; o1]].
Proof. exact: seq_edge_set_back. Qed.

Lemma seq_edge_list_ground_loop : seq_edge_list [:: o2; o2] = [:: [set o2]].
Proof. exact: seq_edge_list_loop. Qed.

(** [o0, o1, o0, o2] in K_3: the raw support has the pair [o0, o2] ... *)
Lemma seq_edge_set_ground_repeat : [set o0; o2] \in seq_edge_set [:: o0; o1; o0; o2].
Proof. by apply: seq_edge_set_consecutive; left. Qed.

(** ... but first indices 0 and 3 are not adjacent, so X178's set misses it, *)
Lemma seq_index_edge_set_ground_repeat :
  [set o0; o2] \notin seq_index_edge_set (G := 'K_3) [:: o0; o1; o0; o2].
Proof.
apply/seq_index_edge_setP => -[x [y [_ /doubleton_eq_iff[[<- <-]|[<- <-]] _ _]]];
  by vm_compute.
Qed.

(** while it has [o2, o0] on the reversed sequence. *)
Lemma seq_index_edge_set_ground_rev :
  [set o2; o0] \in seq_index_edge_set (G := 'K_3) [:: o2; o0; o1; o0].
Proof. by apply/seq_index_edge_setP; exists o2, o0. Qed.

End EdgesGrounding.

(** ** Genuine cycles of a sequence

    [seq_cycle r c] (a proposition) and [seq_cycleb r c] (a boolean) state that the
    sequence [c] is a cycle of the relation [r] with at least three entries: MathComp's
    [ucycle r c] / [ucycleb r c], i.e. [cycle r c && uniq c] (consecutive entries and
    the closing pair (last entry, first entry) are related, and the entries are
    pairwise distinct), together with [2 < size c] (registry
    meta/library_primitives/genuine-cycle.json).  The relation is ARBITRARY: no
    symmetry, irreflexivity or graph premise is part of the definition, so the same
    predicate serves undirected adjacency [(--)] and supplied or directed relations.

    Upstream audit (2026-10-03; MathComp 2.5.0, coq-graph-theory 0.9.7).  MathComp
    [path.v] owns [cycle], [ucycleb] and [ucycle] with [rot_ucycle], [rotr_ucycle],
    [rev_cycle] and [eq_cycle]; without the size guard the empty sequence, a single
    [r]-loop and a two-way pair would all be [ucycle]s.  coq-graph-theory has no
    predicate for a genuine cycle of a raw sequence.  Hamiltonian cycles, cycles of a
    prescribed length, longest, induced, rainbow or chorded cycles, existential
    "has a cycle" conditions, multigraph circuits and the raw cycle-edge interfaces
    are different contracts and stay separate.

    Specification, every clause proved below:
    - the two forms reflect each other ([seq_cycleP]); a genuine cycle is a [ucycle],
      a [cycle], duplicate-free and of size at least three;
    - degenerate sequences are excluded whatever [r]: [[::]], [[:: x]] (even when
      [r x x]) and the digon [[:: x; y]] (even when [r x y] and [r y x]);
    - a triangle [[:: x; y; z]] is one exactly when its entries are distinct and
      [r x y], [r y z], [r z x] hold; repeated entries are excluded;
    - invariance under [rot] and [rotr]; every cyclically consecutive pair is related
      one way or the other;
    - reversal gives a cycle of the CONVERSE relation, hence a cycle of [r] itself
      under the hypothesis [symmetric r], a sufficient condition (a directed 3-cycle
      is grounded not to reverse). *)

Section SeqCycle.
Variables (T : eqType) (r : rel T).
Implicit Types (c : seq T) (u v x y z : T).

(** [c] is a cycle of [r] with at least three entries, as a boolean ... *)
Definition seq_cycleb c : bool := ucycleb r c && (2 < size c).

(** ... and as a proposition. *)
Definition seq_cycle c : Prop := ucycle r c /\ 2 < size c.

Lemma seq_cycleP c : reflect (seq_cycle c) (seq_cycleb c).
Proof. exact: andP. Qed.

Lemma seq_cycleE c : seq_cycle c <-> [/\ cycle r c, uniq c & 2 < size c].
Proof. by split=> [[/andP[-> ->] ->]|[cc uc sc]]; split=> //; apply/andP. Qed.

Lemma seq_cycle_ucycle c : seq_cycle c -> ucycle r c.
Proof. by case. Qed.

Lemma seq_cycle_cycle c : seq_cycle c -> cycle r c.
Proof. by case/seq_cycleE. Qed.

Lemma seq_cycle_uniq c : seq_cycle c -> uniq c.
Proof. by case/seq_cycleE. Qed.

Lemma seq_cycle_size c : seq_cycle c -> 2 < size c.
Proof. by case. Qed.

(** Degenerate sequences are never cycles, whatever [r]: the empty sequence, a
    single entry (even with [r x x]) and a digon (even with [r x y] and [r y x]). *)
Lemma seq_cycle_nil : ~ seq_cycle [::].
Proof. by case. Qed.

Lemma seq_cycle_seq1 x : ~ seq_cycle [:: x].
Proof. by case. Qed.

Lemma seq_cycle_pair x y : ~ seq_cycle [:: x; y].
Proof. by case. Qed.

(** A triangle is a cycle exactly when its three entries are distinct and related
    around the closing pair. *)
Lemma seq_cycle_triangle x y z :
  seq_cycle [:: x; y; z] <-> [/\ uniq [:: x; y; z], r x y, r y z & r z x].
Proof.
rewrite seq_cycleE /= andbT.
by split=> [[/and3P[xy yz zx] u _]|[u xy yz zx]]; split=> //; apply/and3P.
Qed.

(** Repeated entries are excluded. *)
Lemma seq_cycle_repeat c : ~~ uniq c -> ~ seq_cycle c.
Proof. by move=> /negP nu /seq_cycle_uniq. Qed.

(** Rotation invariance. *)
Lemma seq_cycle_rot n c : seq_cycle (rot n c) <-> seq_cycle c.
Proof. by rewrite /seq_cycle rot_ucycle size_rot. Qed.

Lemma seq_cycle_rotr n c : seq_cycle (rotr n c) <-> seq_cycle c.
Proof. by rewrite /seq_cycle rotr_ucycle size_rotr. Qed.

(** Every cyclically consecutive pair is related, one way or the other. *)
Lemma seq_cycle_consecutive c u v :
  seq_cycle c -> seq_cyclic_consecutive c u v -> r u v || r v u.
Proof. by move/seq_cycle_cycle; apply: seq_cyclic_consecutive_cycle. Qed.

End SeqCycle.

(** Reversal: the reversed sequence is a cycle of the CONVERSE relation; for a
    symmetric relation (an undirected adjacency) it is a cycle of the same one. *)
Lemma seq_cycle_rev_converse (T : eqType) (r : rel T) (c : seq T) :
  seq_cycle r (rev c) <-> seq_cycle (fun x y => r y x) c.
Proof. by rewrite /seq_cycle /ucycle rev_cycle rev_uniq size_rev. Qed.

Lemma seq_cycle_rev (T : eqType) (r : rel T) (c : seq T) :
  symmetric r -> seq_cycle r (rev c) <-> seq_cycle r c.
Proof.
move=> rsym; rewrite seq_cycle_rev_converse /seq_cycle /ucycle.
by rewrite (@eq_cycle _ (fun x y => r y x) r) // => x y; rewrite rsym.
Qed.

(** ** Grounding: the triangle of [K_3], a digon of [K_2], and a directed
    relation on ['I_3] *)
Section CycleGrounding.
Local Notation o0 := (@Ordinal 3 0 isT).
Local Notation o1 := (@Ordinal 3 1 isT).
Local Notation o2 := (@Ordinal 3 2 isT).

Lemma seq_cycle_ground_K3 : seq_cycle (@edge_rel 'K_3) [:: o0; o1; o2].
Proof. by apply/seq_cycleP. Qed.

Lemma seq_cycle_ground_digon : ~ seq_cycle (@edge_rel 'K_2) [:: ord0; ord_max].
Proof. exact: seq_cycle_pair. Qed.

Lemma seq_cycle_ground_repeat : ~ seq_cycle (@edge_rel 'K_3) [:: o0; o1; o0; o2].
Proof. by apply: seq_cycle_repeat. Qed.

(** A directed 3-cycle of the successor relation mod 3: a cycle in one
    direction, not in the reverse one (the relation is not symmetric). *)
Let succ3 : rel 'I_3 := fun x y => (y == x.+1 %% 3 :> nat).

Lemma seq_cycle_ground_directed : seq_cycle succ3 [:: o0; o1; o2].
Proof. by apply/seq_cycleP. Qed.

Lemma seq_cycle_ground_directed_rev : ~ seq_cycle succ3 (rev [:: o0; o1; o2]).
Proof. by move/seq_cycleP. Qed.

End CycleGrounding.
