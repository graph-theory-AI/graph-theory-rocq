(** * GTMisc.conjectures.X232 -- wave X232: the heavy-path extension (2026-10-26)

    A one-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier). Row:
    arxiv:1904.12273#01, the heavy-path extension in the introduction of Chudnovsky, Scott and
    Seymour, "Detecting a long odd hole". Shared vocabulary is reused: [hole c] is an induced
    cycle with at least four vertices (GTBase.induced_cycles) and [u -- v] is adjacency in a
    finite simple graph (GraphTheory sgraph). The grounding certificates are in grounding_X232.v
    and the disproof is applications/heavy_path_disproof.v. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base induced_cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x232 vocabulary ************************************************* *)

Section X232.
Variable G : sgraph.
Implicit Types (c p : seq G).

(** A long odd hole: a hole of odd length at least [ell]. *)
Definition x232_long_odd_hole (ell : nat) c : Prop := [/\ hole c, odd (size c) & ell <= size c].

Definition x232_shortest_long_odd_hole (ell : nat) c : Prop :=
  x232_long_odd_hole ell c /\ forall d : seq G, x232_long_odd_hole ell d -> size c <= size d.

(** A path of the cycle [c]: [m.+1] cyclically consecutive entries, [m < size c] ([m] edges). *)
Definition x232_cycle_path c p : Prop := exists i m, m < size c /\ p = take m.+1 (rot i c).

(** [v] is C-major: it is off [c], and no three-vertex path of [c] contains all its neighbours in [c]. *)
Definition x232_major c (v : G) : Prop :=
  v \notin c /\
  ~ exists p, [/\ x232_cycle_path c p, size p = 3 & forall u, u \in c -> u -- v -> u \in p].

End X232.

(** ** X232 statements ********************************************************* *)

(** Corpus row: arxiv:1904.12273#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1904.12273__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1904.12273__01.json
    English statement: (arXiv:1904.12273, Chudnovsky, Scott and Seymour, "Detecting a long odd
      hole", the heavy-path extension of the introduction)
      For every ell >= 5 there is a bound b such that, if C is a shortest long odd hole in a
      graph G (an odd hole of length at least ell, of minimum length among them) and M is a set
      of C-major vertices of which one is nonadjacent to all the others, then some path of C
      with at most b edges contains a neighbour of every vertex of M.
    Definitions: [hole c] - c lists the vertices of an induced cycle with at least four
      vertices (GTBase.induced_cycles); [x232_long_odd_hole ell c] - a hole of odd length at
      least ell (this file); [x232_shortest_long_odd_hole ell c] - a long odd hole of minimum
      length (this file); [x232_cycle_path c p] - p is a path of the cycle c: cyclically
      consecutive vertices of c, fewer than size c edges (this file); [x232_major c v] - v is
      C-major (this file); [u -- v] - adjacency (GraphTheory).
    Notes: the source is the arXiv e-print, detectinglongodd.tex (sha256
      2bf7dc35a7d923683f6f9b31332857ca9bc717f6630e1946483fd24dcb6f69fd). It fixes ell >= 5 and
      calls a path or hole long if its length is at least ell (l.124-125); C-major is
      l.126-127 verbatim; a shortest long odd hole is a long odd hole of minimum length
      (l.133-134). The sentence is l.146-149: "a heavy path of C of bounded length (that is,
      such that every vertex in M has a neighbour in the path) would be just as good as a
      heavy edge; and this extension might be true, but we were unable to prove it".
      "Bounded" is read as a bound depending only on ell, as every bound of the paper; the
      length of a path is its number of edges. The extension is stated "for our purposes"
      (l.146), inside the algorithm, where the easily-detected configurations are excluded
      (l.129-132): the paper works in a candidate graph (l.359-360: no long pyramid, no long
      jewel of order at most ell + 2, no long odd hole of length at most 2 ell + 2). The row
      does not state that hypothesis and it is not encoded. The statement is refuted in
      applications/heavy_path_disproof.v, at ell = 7, by graphs G(q) on 3q + 4 vertices with
      M of four members; so a bound depending on |M| as well is refuted too. Candidacy of
      G(q) was checked by the source's referee report only computationally (ell = 7, odd
      q >= 9), and the extension in the candidate setting stays open as far as this
      refutation is concerned. *)
Definition heavy_path_extension_statement : Prop :=
  forall ell : nat, 5 <= ell -> exists b : nat,
    forall (G : sgraph) (c : seq G) (M : {set G}),
      x232_shortest_long_odd_hole ell c ->
      (forall v, v \in M -> x232_major c v) ->
      (exists2 m0, m0 \in M & forall v, v \in M -> v != m0 -> ~~ (m0 -- v)) ->
      exists p, [/\ x232_cycle_path c p, (size p).-1 <= b
                  & forall v, v \in M -> exists2 u, u \in p & v -- u].
