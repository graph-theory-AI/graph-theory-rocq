(** * GTBase.walks_paths — vertex sequences, walks and paths

    Batch B of the library migration (meta/LIBRARY_MIGRATION_PLAN.md, section 15)
    gathers the reusable finite path and cycle vocabulary of the corpus in this
    module, one concept family per reviewed change.  The first family is the
    vertex set of a raw vertex sequence, [seq_vertices] (registry entry
    [path-vertices] in meta/library_primitives.json).

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
