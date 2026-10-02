(** * GTBase.walks_paths — vertex sequences, walks and paths

    Batch B of the library migration (meta/LIBRARY_MIGRATION_PLAN.md, section 15)
    gathers the reusable finite path and cycle vocabulary of the corpus in this
    module, one concept family per reviewed change: the vertex set of a raw
    vertex sequence, [seq_vertices] (registry
    meta/library_primitives/path-vertices.json), and the internal vertices of a
    sequence, [seq_interior] and [seq_inner] (registry
    meta/library_primitives/internal-vertices.json, section "Internal vertices"
    below).

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
From GraphTheory Require Import digraph.

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
