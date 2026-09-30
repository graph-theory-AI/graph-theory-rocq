(** * Digraph.conjectures.implications_X46 — wave X46 implication edges

      - e100 : opg:caccetta_haggkvist_conjecture ==> arxiv:1809.08324#00
               (Caccetta-Haggkvist implies the bipartite short-cycle
               conjecture).  BLOCKED, see the annotation: the implication is
               stated in the source paper's abstract but derived there through an
               auxiliary digraph; instantiating CH on the bipartite host itself
               loses a factor and only gives girth 2k+2.

      - e102 : arxiv:1809.08324#01 ==> arxiv:1809.08324#00
               (Seymour-Spirkl Conjecture 1.5, the asymmetric bipartite
               short-cycle conjecture, implies their Conjecture 1.2).

    VERIFIED: hypothesis-class containment with an explicit choice of the two
    rationals.  The target gives equal parts [#|A| = #|B| = n > 0] and the
    division-free strict bound [n < k.+1 * outdeg v]; the source is applied with
    [alpha = beta = (n+1) / ((k+1) * n)], which is [> 1/(k+1)] and hence
    satisfies [k * alpha + beta > 1], and whose numeric content
    [(n+1) * n <= (k+1) * n * outdeg v] is exactly [n + 1 <= (k+1) * outdeg v].
    The only non-bookkeeping step is that in a bipartite digraph every
    out-neighbour of a vertex of [A] lies in [B], so the part-relative
    out-degree [x53_out_to B v] equals the plain [outdeg v]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.
From Digraph.conjectures Require Import X46 X53.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** In a digraph all of whose arcs cross the partition [{A, B}], the
    out-neighbours of a vertex of [A] all lie in [B], so counting them inside
    [B] is counting all of them. *)
Lemma x46_out_to_other_part (D : diGraphType) (A B : {set D}) (v : D) :
  [disjoint A & B] ->
  (forall u w : D, u --> w -> ((u \in A) && (w \in B)) || ((u \in B) && (w \in A))) ->
  v \in A -> x53_out_to B v = outdeg v.
Proof.
move=> dAB cross vA; rewrite /x53_out_to /outdeg; apply: eq_card => w.
rewrite !inE andbC; case harc: (v --> w) => //=.
case/orP: (cross _ _ harc) => /andP[h1 h2]; first by rewrite h2.
by rewrite (disjointFr dAB vA) in h1.
Qed.

(*@EDGE from=bipartite_digraph_asymmetric_outdegree_girth_statement to=bipartite_digraph_outdegree_girth_statement kind=implies status=verified proof=bipartite_digraph_asymmetric_outdegree_girth_implies_bipartite_digraph_outdegree_girth cite="gc:e102" note="Hypothesis-class containment with alpha = beta = (n+1)/((k+1)*n): positivity is 0 < n; k*alpha+beta > 1 reduces (after dividing by (k+1)*n > 0) to (k+1)*n < (k+1)*(n+1); and the degree premise n < (k+1)*outdeg v gives (n+1)*n <= (k+1)*n*outdeg v = (k+1)*n*x53_out_to B v, since in a bipartite digraph every out-neighbour of a vertex of A lies in B (x46_out_to_other_part). Equal parts of size n > 0 make D nonempty, so the source's 0 < #|D| guard is met, and the conclusion (a dicycle on at most 2k vertices) is literally the target's." *)

Theorem bipartite_digraph_asymmetric_outdegree_girth_implies_bipartite_digraph_outdegree_girth :
  bipartite_digraph_asymmetric_outdegree_girth_statement ->
  bipartite_digraph_outdegree_girth_statement.
Proof.
move=> H k n D A B hk hn [dAB [cov [cA [cB cross]]]] hdeg.
have hden : (0 < k.+1 * n)%N by rewrite muln_gt0 hn.
have crossBA : forall u w : D, u --> w ->
    ((u \in B) && (w \in A)) || ((u \in A) && (w \in B)).
  by move=> u w /cross; rewrite orbC.
have key : forall (S T : {set D}) (v : D), [disjoint S & T] ->
    (forall u w : D, u --> w -> ((u \in S) && (w \in T)) || ((u \in T) && (w \in S))) ->
    #|T| = n -> v \in S -> (n.+1 * #|T| <= k.+1 * n * x53_out_to T v)%N.
  move=> S T v dST crossST cT vS.
  rewrite (x46_out_to_other_part dST crossST vS) cT.
  rewrite -mulnA [(n * _)%N]mulnC mulnA (leq_pmul2r hn).
  exact: (hdeg v).
apply: (H k n.+1 (k.+1 * n) n.+1 (k.+1 * n) hk) => //.
- rewrite /x53_k_alpha_plus_beta_gt_one -mulnDl addnC -mulSn.
  by rewrite (ltn_pmul2r hden) (ltn_pmul2l (ltn0Sn k)).
- by apply: leq_trans (max_card (mem A)); rewrite cA.
- by split; [exact: dAB | split; [exact: cov | exact: cross]].
- by move=> v vA; apply: (key A B).
- by move=> v vB; apply: (key B A) => //; rewrite disjoint_sym.
Qed.

(*@EDGE from=caccetta_haggkvist_statement to=bipartite_digraph_outdegree_girth_statement kind=implies status=candidate proved=false cite="gc:e100" note="BLOCKED: the reduction is NOT an instantiation of the source, and the corpus argument itself records that the confirmation rests on the source paper's abstract rather than on a one-line derivation. Applying caccetta_haggkvist_statement to the bipartite host D itself (2n vertices, minimum out-degree r with n < (k+1) * r forced by the target premise) yields a dicycle of size at most (2n + r - 1) %/ r, which is about 2(k+1) = 2k+2, not 2k; and the evenness of dicycles in a bipartite digraph does not close the gap, since 2k+2 is already even. Seymour and Spirkl derive their Conjecture 1.2 from Caccetta-Haggkvist through an AUXILIARY digraph (arXiv:1809.08324), which the corpus argument does not reproduce. Missing ingredients: that auxiliary construction on one side of the bipartition, the lower bound on its minimum out-degree, and the transfer of a short dicycle of it back to a dicycle of length at most 2k in D. The converse direction is available and verified as corpus e102 above." *)

(** ** Print Assumptions audit *)

Print Assumptions x46_out_to_other_part.
Print Assumptions bipartite_digraph_asymmetric_outdegree_girth_implies_bipartite_digraph_outdegree_girth.
