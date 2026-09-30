(** * Extremal.conjectures.implications_X13 -- corpus relation edges whose TARGET
    is the X13 row [large_girth_min_degree_bipartite_induced_statement]
    (arxiv:1802.03727#03, Esperet-Kang-Thomasse Conjecture 1.6).

      e063  arxiv:1802.03727#02 => #03   VERIFIED below
              (triangle-free C*log d bipartite-induced degree  =>  girth >= 4
               version with the absolute constant 3)
      e075  arxiv:1802.03727#01 => #03   VERIFIED below
              (min-degree clique/bipartite dichotomy  =>  large-girth version)

    Both edges are restrictions of a stronger hypothesis to graphs of girth at
    least 4, using girth >= 4 <-> triangle-free (proved here as
    [girth_geq4_triangle_free]) and then a purely arithmetic choice of the
    threshold d0 which makes the source's degree guarantee reach the constant 3. *)

From mathcomp Require Import all_boot.
From GTBase Require Import base.
From Extremal.conjectures Require Import X13 X30.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared bridge: girth >= 4 is triangle-freeness.

    A triangle [x -- y -- z -- x] is the genuine 3-cycle [[:: x; y; z]]
    ([ucycle], size 3 > 2), which [girth_geq G 4] forbids.  The three vertices
    are pairwise distinct because [sedge] is irreflexive. *)
Lemma girth_geq4_triangle_free (G : sgraph) : girth_geq G 4 -> triangle_free G.
Proof.
move=> Hg x y z xy yz zx.
have xNy : x != y by apply: contraTneq xy => ->; rewrite sg_irrefl.
have yNz : y != z by apply: contraTneq yz => ->; rewrite sg_irrefl.
have zNx : z != x by apply: contraTneq zx => ->; rewrite sg_irrefl.
have Hc : ucycle (@sedge G) [:: x; y; z].
  rewrite /ucycle /= xy yz zx /= !inE negb_or xNy /=.
  by rewrite eq_sym zNx yNz.
by have := Hg _ Hc isT.
Qed.

(** A triangle-free graph has no clique on 3 or more vertices. *)
Lemma triangle_free_no_clique3 (G : sgraph) (S : {set G}) :
  triangle_free G -> clique S -> 3 <= #|S| -> False.
Proof.
move=> Htf Hcl S3.
have /card_gt0P [x xS] : 0 < #|S| by apply: leq_trans S3.
have S2 : 2 <= #|S :\ x| by rewrite (cardsD1 x) xS add1n ltnS in S3.
have /card_gt0P [y yS] : 0 < #|S :\ x| by apply: leq_trans S2.
have S1 : 1 <= #|(S :\ x) :\ y| by rewrite (cardsD1 y) yS add1n ltnS in S2.
have /card_gt0P [z zS] : 0 < #|(S :\ x) :\ y| by [].
move: yS zS; rewrite !inE => /andP[yNx yS] /andP[zNy /andP[zNx zS]].
apply: (Htf x y z); apply: Hcl => //; by rewrite eq_sym.
Qed.

(** ** e063 -- the triangle-free C*log(d) row implies the large-girth row.

    Girth at least [g0 = 4] gives triangle-freeness, so the source applies to
    every graph the target quantifies over.  It remains to pick the minimum
    degree threshold so that the source's guarantee
    [cden * deg >= cnum * trunc_log 2 d] beats [deg >= 3]: with
    [d0 := 2 ^ (3 * cden)] one has [trunc_log 2 d0 = 3 * cden]
    ([trunc_expnK]), hence
    [cden * deg >= cnum * (3 * cden) >= 3 * cden = cden * 3]
    and [deg >= 3] by [leq_pmul2l] (using [0 < cden]).  No monotonicity in [d]
    is needed since the target only has to exhibit ONE threshold. *)
Theorem triangle_free_min_degree_log_bipartite_induced_implies_large_girth_min_degree_bipartite_induced :
  triangle_free_min_degree_log_bipartite_induced_statement ->
  large_girth_min_degree_bipartite_induced_statement.
Proof.
move=> [cnum [cden [cnum0 [cden0 Hsrc]]]].
exists (2 ^ (3 * cden)), 4; split; first by rewrite expn_gt0.
split=> // G G0 Hgirth Hmin.
have Htf := girth_geq4_triangle_free Hgirth.
have d2 : 2 <= 2 ^ (3 * cden).
  by rewrite (_ : 2 = 2 ^ 1) // leq_exp2l // muln_gt0.
have [S [S0 [Sbip Hdeg]]] := Hsrc _ G d2 G0 Htf Hmin.
exists S; split => //; split => // v.
have := Hdeg v; rewrite trunc_expnK // mulnA => Hv.
rewrite -(leq_pmul2l cden0) mulnC.
apply: leq_trans Hv.
by rewrite leq_mul2r (leq_pmull 3 cnum0) orbT.
Qed.

(*@EDGE from=triangle_free_min_degree_log_bipartite_induced_statement to=large_girth_min_degree_bipartite_induced_statement kind=implies status=verified proof=triangle_free_min_degree_log_bipartite_induced_implies_large_girth_min_degree_bipartite_induced cite="gc:e063" note="g0 = 4 gives triangle-freeness (girth_geq4_triangle_free: a triangle is a genuine 3-cycle); d0 = 2^(3*cden) makes trunc_log 2 d0 = 3*cden (trunc_expnK), so cden*deg >= cnum*3*cden >= cden*3 and deg >= 3 by leq_pmul2l." *)

(** ** e075 -- the clique/bipartite dichotomy implies the large-girth row.

    [x13_unbounded] is the EVENTUAL form ("for every b there is d0 with
    b <= f d for ALL d >= d0"), so the two unbounded functions x2 and x3 DO
    share a threshold: take [d0 := maxn 1 (maxn d2 d3)] where d2, d3 are the
    thresholds given by [x13_unbounded x2 3] and [x13_unbounded x3 3].  With
    girth [g0 = 4] the host is triangle-free, hence has no clique on
    [x2 d0 >= 3] vertices, which kills the first disjunct of the dichotomy; the
    second disjunct gives a non-empty bipartite induced subgraph of minimum
    degree [x3 d0 >= 3], i.e. exactly the target's conclusion. *)
Theorem min_degree_forces_large_clique_or_bipartite_induced_implies_large_girth_min_degree_bipartite_induced :
  min_degree_forces_large_clique_or_bipartite_induced_statement ->
  large_girth_min_degree_bipartite_induced_statement.
Proof.
move=> [x2 [x3 [U2 [U3 [_ Hsrc]]]]].
have [b2 Hb2] := U2 3; have [b3 Hb3] := U3 3.
pose d0 := maxn 1 (maxn b2 b3).
have d0_gt0 : 0 < d0 by rewrite leq_max leqnn.
have x2_3 : 3 <= x2 d0 by apply: Hb2; rewrite leq_max leq_maxl orbT.
have x3_3 : 3 <= x3 d0 by apply: Hb3; rewrite leq_max leq_maxr orbT.
exists d0, 4; split => //; split => // G G0 Hgirth Hmin.
have Htf := girth_geq4_triangle_free Hgirth.
have [[S [Scard Sclique]]|[S [S0 [Sbip Hdeg]]]] := Hsrc d0 G d0_gt0 G0 Hmin.
  by case: (triangle_free_no_clique3 Htf Sclique (leq_trans x2_3 Scard)).
exists S; split => //; split => // v.
exact: leq_trans x3_3 (Hdeg v).
Qed.

(*@EDGE from=min_degree_forces_large_clique_or_bipartite_induced_statement to=large_girth_min_degree_bipartite_induced_statement kind=implies status=verified proof=min_degree_forces_large_clique_or_bipartite_induced_implies_large_girth_min_degree_bipartite_induced cite="gc:e075" note="x13_unbounded is the EVENTUAL form, so x2 and x3 share a threshold: d0 = maxn 1 (maxn b2 b3) with x2 d0 >= 3, x3 d0 >= 3. g0 = 4 gives triangle-freeness, which forbids a clique on x2 d0 >= 3 vertices (triangle_free_no_clique3), so the dichotomy's second disjunct fires and x3 d0 >= 3 gives min degree 3." *)

Print Assumptions triangle_free_min_degree_log_bipartite_induced_implies_large_girth_min_degree_bipartite_induced.
Print Assumptions min_degree_forces_large_clique_or_bipartite_induced_implies_large_girth_min_degree_bipartite_induced.
