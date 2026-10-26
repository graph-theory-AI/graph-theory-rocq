(** * Extremal.conjectures.X234 -- wave X234: three Ramsey rows (2026-10-26)

    A three-row wave under the prospective contract of meta/faithfulness_policy.json (hard lint,
    classified local helpers, grounding certificates, an independent verifier).  Rows:
    arxiv:2207.07775#01 (mixed blowup colourings), arxiv:2312.06895#00 (the K_s-Ramsey number of
    K_t) and arxiv:2312.06895#01 (its q-colour generalization).  Ramsey vocabulary is not copied: the
    registered ramsey-number source Extremal.conjectures.X195 is imported, [x195_arrows Host k Fam]
    (every k-colouring of the edges of Host has a monochromatic copy of some member of Fam) and
    [x195_ramsey_number k Fam n] (n is the least order of a complete graph that arrows Fam); there k
    counts COLOURS, while the papers' k and t are clique sizes.  Shared vocabulary is reused as well:
    [mono_copy] (Extremal.foundations.edge_colourings), [complete_multipartite_graph] and
    [clique_count_size] (GTBase).  The grounding certificates are in grounding_X234.v. *)

From GTBase Require Import base common clique_counts complete_multipartite_graphs.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import X195.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x234 vocabulary ************************************************* *)

(** A red/blue colouring of the edges of the 2-blowup K_n[2] (GTBase
    [complete_multipartite_graph n 2]: parts of size 2, adjacent iff the parts differ) is a blowup
    colouring when the colour of every edge depends only on the two parts it joins
    (arXiv:2207.07775 l.1091-1095). *)
Definition x234_blowup_colouring (n : nat) (col : {set complete_multipartite_graph n 2} -> 'I_2) : Prop :=
  exists chi : {set 'K_n} -> 'I_2,
    forall x y : complete_multipartite_graph n 2, x.1 != y.1 -> col [set x; y] = chi [set x.1; y.1].

(** ** X234 statements ******************************************************* *)

(** Corpus row: arxiv:2207.07775#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2207.07775__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2207.07775__01.json
    English statement: (arXiv:2207.07775, Fox and Wigderson, "Ramsey multiplicity and the Turan
      coloring", Conjecture conj:mixed)
      For infinitely many k there is a mixed blowup colouring of K_{r(k)-1}[2]: a red/blue colouring
      of the edges of the 2-blowup of K_{r(k)-1} with no monochromatic K_k which is not the blowup of
      a Ramsey colouring of the edges of K_{r(k)-1}; r(k) = r(k,k) is the diagonal Ramsey number.
    Definitions: [x195_ramsey_number 2 Fam R] - R is the 2-colour Ramsey number of the family Fam,
      here the single graph K_k (Extremal.conjectures.X195); [complete_multipartite_graph n 2] - the
      2-blowup K_n[2] (GTBase); [mono_copy F col c] - a (not necessarily induced) copy of F all of
      whose edges have colour c (Extremal.foundations.edge_colourings); [x234_blowup_colouring col] -
      the colour of an edge depends only on the two parts it joins (this file).
    Notes: the source is the e-print multiplicity_aic_style.tex (sha256 335c2e27...): r(k) l.1089,
      the s-blowup l.1091, mixed blowup colourings l.1092-1094, the conjecture l.1114-1117, why only
      infinitely many k l.1121.  "Infinitely many k" is: for every N some k >= N.  Not being the
      blowup of a RAMSEY colouring is the same as not being the blowup of any colouring: a blowup of
      chi with no monochromatic K_k makes chi Ramsey (one vertex per part lifts a monochromatic K_k
      of chi).  r(k) is named by [x195_ramsey_number], which is functional; X195's k counts colours
      (here 2), not the clique size.  The parts of the blowup are independent (no edge inside a
      part): a mixed colouring gives the red and blue edges of a 3-colouring of K_n, the edges inside
      parts taking the third colour (l.1096), and the proof of lem:mixed-equivalence colours only
      edges across parts (l.1108, l.1110-1111).  The colouring is a function on all vertex sets, of
      which only those edges are read.  The pinned review says open. *)
Definition mixed_blowup_colouring_statement : Prop :=
  forall N : nat, exists k R : nat,
    [/\ N <= k, x195_ramsey_number 2 (fun _ : 'I_1 => 'K_k) R &
        exists col : {set complete_multipartite_graph R.-1 2} -> 'I_2,
          (forall c : 'I_2, ~ mono_copy 'K_k col c) /\ ~ x234_blowup_colouring col].

(** Corpus row: arxiv:2312.06895#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2312.06895__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2312.06895__00.json
    English statement: (arXiv:2312.06895, Fox, Tidor and Zhang, "Triangle Ramsey numbers of complete
      graphs", Conjecture conj:clique-clique)
      For all s <= t, r_{K_s}(K_t) = C(r(K_t), s), where a graph is K_t-Ramsey if every 2-colouring of
      its edges has a monochromatic copy of K_t, r_F(H) is the minimum number of copies of F in an
      H-Ramsey graph, and r(K_t) is the Ramsey number.
    Definitions: [x195_arrows G 2 Fam] - every 2-colouring of the edges of G has a monochromatic copy
      of the member K_t of Fam, i.e. G is K_t-Ramsey (Extremal.conjectures.X195);
      [x195_ramsey_number 2 Fam R] - R = r(K_t) (X195); [clique_count_size G s] - the number of
      s-cliques of G, i.e. of copies of K_s (GTBase.clique_counts).
    Notes: the source is the e-print main-v2.tex (sha256 a6b1c85c...): H-Ramsey and r_F(H) l.84,
      Chvatal's case s = 2 l.88-92, the conjecture l.96-100.  A copy of K_s is an s-clique, counted by
      [clique_count_size]; s = 1 counts vertices and s = 2 edges (Chvatal).  The minimum equals
      C(r(K_t), s) iff some K_t-Ramsey graph has exactly that many s-cliques and every K_t-Ramsey
      graph has at least that many; the first half holds for K_{r(K_t)} itself.  s = 0 is harmless
      (one empty clique, C(R, 0) = 1).  R exists by Ramsey's theorem (the source presupposes
      r(K_t)); the statement quantifies over every R with [x195_ramsey_number 2 Fam R], the X195 /
      X230 pattern (R is unique).  The pinned review is partial (the paper proves s = 3 for all large
      t); that is the upstream status, not the leg. *)
Definition clique_ramsey_count_statement : Prop :=
  forall s t : nat, s <= t -> forall R : nat, x195_ramsey_number 2 (fun _ : 'I_1 => 'K_t) R ->
    (exists G : sgraph, x195_arrows G 2 (fun _ : 'I_1 => 'K_t) /\ clique_count_size G s = 'C(R, s)) /\
    (forall G : sgraph, x195_arrows G 2 (fun _ : 'I_1 => 'K_t) -> 'C(R, s) <= clique_count_size G s).

(** Corpus row: arxiv:2312.06895#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2312.06895__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2312.06895__01.json
    English statement: (arXiv:2312.06895, Fox, Tidor and Zhang, the q-colour generalization of
      Conjecture conj:clique-clique)
      For every number q >= 2 of colours and all s <= t, the minimum number of copies of K_s in a
      graph every q-colouring of whose edges has a monochromatic K_t equals C(r_q(K_t), s), r_q(K_t)
      being the q-colour Ramsey number.
    Definitions: [x195_arrows G q Fam] - every q-colouring of the edges of G has a monochromatic copy
      of the member K_t of Fam (Extremal.conjectures.X195); [x195_ramsey_number q Fam R] - R =
      r_q(K_t) (X195); [clique_count_size G s] - the number of s-cliques of G (GTBase.clique_counts).
    Notes: the source is the e-print main-v2.tex (sha256 a6b1c85c...) l.134: "We also conjecture that
      the $q$-color generalization of  \cref{conj:clique-clique} holds."; the paper states the
      generalization, so the row is determined.  It is conj:clique-clique (l.96-100) with q colours
      in BOTH "two-coloring" of H-Ramsey (l.84) and the Ramsey number, r(K_t) becoming r_q(K_t).  The
      second change is forced: K_{r(K_t)} is not q-colour K_t-Ramsey for q >= 3, and the q-colour
      form of Chvatal's theorem cited at l.134 needs r_q.  q >= 2, the generalization being from two
      colours up: q = 1 would be trivial, and q = 0 is excluded because no map {set G} -> 'I_0
      exists, so [x195_arrows G 0 Fam] holds vacuously (and R = 0).  At q = 2 the body is that of
      arxiv:2312.06895#00 (grounding_X234.v, g234_multi_two).  R exists by Ramsey's theorem; the
      forall-R form and the minimum are read as for arxiv:2312.06895#00.  The pinned review status
      is the upstream status, not the leg. *)
Definition multicolour_clique_ramsey_count_statement : Prop :=
  forall q s t : nat, 2 <= q -> s <= t ->
    forall R : nat, x195_ramsey_number q (fun _ : 'I_1 => 'K_t) R ->
      (exists G : sgraph, x195_arrows G q (fun _ : 'I_1 => 'K_t) /\ clique_count_size G s = 'C(R, s)) /\
      (forall G : sgraph, x195_arrows G q (fun _ : 'I_1 => 'K_t) -> 'C(R, s) <= clique_count_size G s).
