(** * Digraph.conjectures.X251 -- wave X251: blow-ups and extensions of oriented trees (Aboulker, Havet, Lochet,
    Lopes, Picasarri-Arrieta, Rambaud, arXiv:2410.23566) and the strong Erdos-Hajnal property of tournaments
    (Chudnovsky, Scott, Seymour, Spirkl, arXiv:2202.13977) (2026-10-28)

    A four-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint, classified local
    helpers, grounding certificates, an independent verifier). Rows: arxiv:2410.23566#01 (k-blow-ups of a linearly
    unavoidable family of bounded maximum average degree), #04 (k-extensions of oriented trees), arxiv:2202.13977#00
    (the strong EH-property and forest backedge graphs) and #01 (tournaments with at most three backedges). Shared
    vocabulary is reused: [linearly_unavoidable] (foundations/tournament_unavoidability.v), [unavoidable]
    (conjectures/unvd.v), [x221_kextension] (conjectures/X221.v), [oriented_tree] (conjectures/X2.v), [backedge]
    (core/order.v), [ind_free] (conjectures/heroes.v), [dgiso] (core/digraph.v) and coq-graph-theory's [is_forest]
    and edge set E(_). The sources are the Mac's deposit coordination/sources/x251-source-mac-20261028
    (2410.23566v1 and 2202.13977v3, TeX main.tex, line numbers below); the grounding certificates are in
    grounding_X251.v. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup.
From GraphTheory Require Import preliminaries digraph sgraph.
From Digraph Require Import prelude interop_graph_theory digraph oriented dipath tournament order.
From Digraph Require Import heroes dichromatic unvd X2 X221.
From Digraph.foundations Require Import tournament_unavoidability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x251 vocabulary ************************************************* *)

(** The K-BLOW-UP D[k] of a digraph (arXiv:2410.23566 l.176-181): each vertex becomes k copies, and every arc uv of D
    gives an arc from every copy of u to every copy of v. *)
Definition x251_blowup (D : diGraphType) (k : nat) : Type := (D * 'I_k)%type.

Section Blowup.
Variables (D : diGraphType) (k : nat).
HB.instance Definition _ := Finite.on (x251_blowup D k).
Definition x251_blowup_rel (a b : x251_blowup D k) : bool := a.1 --> b.1.
HB.instance Definition _ := HasArc.Build (x251_blowup D k) x251_blowup_rel.
End Blowup.

(** The family F[k] = {D[k] | D in F} (l.182), up to digraph isomorphism. *)
Definition x251_blowup_family (k : nat) (F : diGraphType -> Prop) (E : diGraphType) : Prop :=
  exists D : diGraphType, F D /\ dgiso E (x251_blowup D k : diGraphType).

(** The maximum average degree of D is at most a (l.94-95): every nonempty S spans at most a |S| / 2 arcs. *)
Definition x251_mad_le (D : diGraphType) (a : nat) : Prop :=
  forall S : {set D}, S != set0 ->
    2 * #|[set p : D * D | (p.1 \in S) && (p.2 \in S) && (p.1 --> p.2)]| <= a * #|S|.

(** The digraphs isomorphic to an oriented tree of order n. *)
Definition x251_oriented_tree_of_order (n : nat) (A : diGraphType) : Prop :=
  exists T : orientedDigraph, oriented_tree T /\ #|T| = n /\ dgiso A T.

(** The STRONG EH-PROPERTY of a tournament H (arXiv:2202.13977 l.130-135): some c = 1/q > 0 such that every H-free
    tournament G with more than one vertex has a pure pair (A, B), every vertex of A adjacent to every vertex of B,
    with |A|, |B| >= c |G|. *)
Definition x251_seh (H : tournament) : Prop :=
  exists q : nat, 1 <= q /\
    forall G : tournament, ind_free H G -> 1 < #|G| ->
      exists A B : {set G}, [/\ [disjoint A & B], (forall a b, a \in A -> b \in B -> a --> b),
        #|G| <= q * #|A| & #|G| <= q * #|B|].

(** ** Statements ************************************************************ *)

(** Corpus row: arxiv:2410.23566#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2410.23566__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2410.23566__01.json
    English statement: (Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, Blow-ups and extensions of trees
      in tournaments, arXiv:2410.23566v1, Conjecture 7)
      If a family F of digraphs is linearly unavoidable and has bounded maximum average degree, then for every
      positive integer k the family F[k] of the k-blow-ups of its members is linearly unavoidable.
    Definitions: [linearly_unavoidable F] - one constant C with unavoidability number at most C |V(D)| throughout F
      (foundations/tournament_unavoidability.v); [x251_mad_le D a], [x251_blowup], [x251_blowup_family] (this file).
    Notes: k is positive, as the source states before the definition (l.176). The source prints the arc set of D[k]
      as {(u,i)(v,j) | uv in A(D), i, j in [k], i <> j} (l.180); the "i <> j" is read as a misprint and not
      encoded, because the same paragraph defines D[k] by blowing up each vertex into an independent set (l.177),
      D[1] would otherwise have no arc, and the source's maximum average degree of the k-blow-up of a tree of order
      n, 2k - 2k/n (l.198), counts k^2 arcs per arc. The family F[k] is taken up to isomorphism, which does not
      change linear unavoidability. The average degree of a nonempty digraph is 2|A(D)|/|V(D)| (l.94-95), counted
      here on the arcs; "bounded" does not depend on that convention, since the edges of the underlying graph and
      the arcs differ by at most a factor 2 plus the loops. The unavoidability number is relational, as in X221:
      a member with no unavoidability number (one with a directed cycle) imposes nothing, and its blow-ups have
      directed cycles too. The empty family, arcless members and single vertices are consistent with the source.
      Literature status: partial at the pin (pinned status partial): the source proves it for oriented trees
      (l.196-197: the k-blow-up of an oriented tree of order n is (2^(10+18k) k n)-unavoidable) and notes it for
      directed paths (l.194-195). *)
Definition blowup_linear_unavoidability_statement : Prop :=
  forall (F : diGraphType -> Prop) (k : nat), 1 <= k ->
    linearly_unavoidable F ->
    (exists a : nat, forall D : diGraphType, F D -> x251_mad_le D a) ->
    linearly_unavoidable (x251_blowup_family k F).

(** Corpus row: arxiv:2410.23566#04
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2410.23566__04/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2410.23566__04.json
    English statement: (Aboulker, Havet, Lochet, Lopes, Picasarri-Arrieta, Rambaud, Blow-ups and extensions of trees
      in tournaments, arXiv:2410.23566v1, Conjecture 10)
      There is an absolute constant C such that for every positive integer k, every k-extension of an oriented tree
      of order n > 1 is C^k (2n - 2)-unavoidable.
    Definitions: [x221_kextension k F D] - D is acyclic and deleting some k vertices of D leaves a member of F up to
      isomorphism (conjectures/X221.v); [x251_oriented_tree_of_order n] (this file); [oriented_tree T] (X2.v);
      [unavoidable D N] - every tournament on N vertices contains D (conjectures/unvd.v).
    Notes: k-extensions are defined for positive k (l.211-212). The conjecture follows from Conjecture 9 together
      with Sumner's conjecture (l.218), which is stated for oriented trees of order n > 1 (l.136); the printed
      Conjecture 10 does not repeat that range, but at n = 1 the bound C^k (2n - 2) is 0 and no digraph with a vertex
      is 0-unavoidable, so the guard 1 < n is kept (load-bearing: grounding_X251.v). The subtraction 2 * n - 2 is
      natural-number subtraction, exact under the guard 1 < n. C is a natural number: unavoidability is monotone in
      the order (tournament_unavoidable_monotone), so a real constant can be rounded up.
      Literature status: open at the pin (pinned status open); the source proves the weaker bound
      2 * 3^C(2k+2,2) |V(F)| for k-extensions of large oriented trees (l.230). *)
Definition kextension_oriented_tree_unavoidability_statement : Prop :=
  exists C : nat, forall k n : nat, 1 <= k -> 1 < n ->
    forall D : diGraphType, x221_kextension k (x251_oriented_tree_of_order n) D ->
      unavoidable D (C ^ k * (2 * n - 2)).

(** Corpus row: arxiv:2202.13977#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.13977__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.13977__00.json
    English statement: (Chudnovsky, Scott, Seymour, Spirkl, Pure pairs. X. Tournaments and the strong Erdos-Hajnal
      property, arXiv:2202.13977v3, Conjecture 1.5)
      A tournament has the strong EH-property if and only if it admits a numbering for which the backedge graph is a
      forest.
    Definitions: [x251_seh H] (this file); [backedge p] - the backedge graph of the numbering p: for i < j, v_i and
      v_j are adjacent iff v_j -> v_i (core/order.v; the source's l.144-149); [is_forest] (coq-graph-theory).
    Notes: G contains H when a subtournament of G is isomorphic to H (l.101-103), so H-free is [ind_free H G]. A
      numbering is a permutation of the vertices read through [ltp]. The biconditional is encoded as stated
      (l.216-217); its "only if" direction is the source's Theorem 1.4 (l.211-212). At the empty tournament and at
      TT 1 both sides hold. Literature status: open at the pin (pinned status open). *)
Definition strong_eh_iff_forest_backedge_statement : Prop :=
  forall H : tournament, x251_seh H <-> exists p : {perm H}, is_forest [set: backedge p].

(** Corpus row: arxiv:2202.13977#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2202.13977__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2202.13977__01.json
    English statement: (Chudnovsky, Scott, Seymour, Spirkl, Pure pairs. X. Tournaments and the strong Erdos-Hajnal
      property, arXiv:2202.13977v3, after Theorem 1.6)
      Every tournament that admits a numbering whose backedge graph has at most three edges has the strong
      EH-property.
    Definitions: [x251_seh H] (this file); [backedge p] (core/order.v); E(_) - the edge set of a simple graph
      (coq-graph-theory).
    Notes: the pinned text asks whether the second sentence of Theorem 1.6 (l.251-254), the D_5-freeness of H (a
      pattern {v_a v_d, v_a v_e, v_b v_e}, a < b < c < d < e, of backedges), can be omitted (l.258: "that remains
      open"). The row is Theorem 1.6 with that sentence dropped and every other hypothesis kept: a tournament with a
      numbering whose backedge graph has at most three edges. Literature status: open at the pin (pinned status
      open). *)
Definition three_backedges_strong_eh_statement : Prop :=
  forall H : tournament, (exists p : {perm H}, #|E(backedge p)| <= 3) -> x251_seh H.
