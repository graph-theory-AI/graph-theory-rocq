(** * Digraph.conjectures.X231 -- wave X231: the forward-cover conjecture (2026-10-26)

    A one-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier). Row:
    arxiv:2304.03567#04, Conjecture 1 of Bessy, Thomasse and Viennot, "Temporalizing digraphs
    via linear-size balanced bi-trees". Shared vocabulary is reused: [u --> v] is the arc
    relation (core/digraph.v), [strongb D] is strong connectivity (invariants/strong.v),
    [connect] is reachability (MathComp fingraph) and [trunc_log 2 n] is the floor of the
    base-two logarithm (MathComp). The disproof is applications/forward_cover_disproof.v. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph strong.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x231 vocabulary ************************************************* *)

(** The forward arcs of a vertex ranking [r]: the arcs [u --> v] with [r u < r v]. An
    injective ranking is a vertex ordering, and a walk of forward arcs is a directed path whose
    vertices increase in that ordering (a forward path). *)
Definition x231_forward_arc (D : diGraphType) (r : D -> nat) : rel D :=
  fun u v => (u --> v) && (r u < r v).

(** The pair {x, y} is forward connected in [r]: there is a forward path from the earlier
    endpoint to the later one. A forward walk raises [r], so this is a forward path from [x]
    to [y] or from [y] to [x]. *)
Definition x231_forward_pair (D : diGraphType) (r : D -> nat) (x y : D) : bool :=
  connect (x231_forward_arc r) x y || connect (x231_forward_arc r) y x.

(** A forward cover: a family of vertex orderings (injective rankings) in which every pair of
    distinct vertices is forward connected in at least one member. *)
Definition x231_forward_cover (D : diGraphType) (rs : seq {ffun D -> nat}) : Prop :=
  all (fun r : {ffun D -> nat} => injectiveb r) rs /\
  forall x y : D, x != y -> has (fun r : {ffun D -> nat} => x231_forward_pair r x y) rs.

(** ** X231 statements ********************************************************* *)

(** Corpus row: arxiv:2304.03567#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2304.03567__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2304.03567__04.json
    English statement: (arXiv:2304.03567, "Temporalizing digraphs via linear-size balanced
      bi-trees", Conjecture 1)
      Every strong digraph D on n vertices has a O(log n) size forward cover. A forward cover
      of D is a set of vertex orderings such that for every pair {x, y} of vertices, x, y or
      y, x is a forward pair in one of them: joined by a directed path whose vertices
      increase in that ordering.
    Definitions: [strongb D] - D is strongly connected (invariants/strong.v);
      [x231_forward_cover rs] - the rankings in rs are injective (vertex orderings) and every
      pair of distinct vertices is forward connected in one of them (this file);
      [x231_forward_pair r x y] - a forward path joins x and y, from the earlier endpoint to
      the later one in r (this file); [x231_forward_arc r] - the arcs that go up in r (this
      file); [trunc_log 2 n] - floor of log2 n (MathComp).
    Notes: O(log n) is read as constants c and n0 with a cover of size at most
      c * floor(log2 n) for every strong digraph on n >= n0 vertices. A vertex ordering is an
      injective ranking into nat, and the cover is a sequence: repeated orderings never help,
      so its size bounds the size of a set. Pairs are unordered pairs of distinct vertices, as
      in the source's request set V choose 2. The source (body/request.tex of the arXiv
      e-print, sha256 50912bde0934a2cc6b0066537dcaf4a77dd3275cdb56aa86d8065dd4703c3ed3)
      defines the forward cover in exactly these terms. The statement is refuted in
      applications/forward_cover_disproof.v: a cyclic chain of m directed diamonds on 3m
      vertices needs m orderings. *)
Definition logarithmic_forward_cover_statement : Prop :=
  exists c n0 : nat, forall D : diGraphType, strongb D -> n0 <= #|D| ->
    exists rs : seq {ffun D -> nat}, x231_forward_cover rs /\ size rs <= c * trunc_log 2 #|D|.
