(** * Extremal.conjectures.implications_X223 -- corpus relation edges unlocked by wave X223.

    Five confirmed [implies] relations of meta/corpus_relations.json have both
    endpoints formalised once this wave lands:

      e076  arxiv:1810.00058#00 => #01   VERIFIED below (pure instantiation H = K_3)
      e160  arxiv:1708.07369#00 => #01   VERIFIED below (eventual => infinitely often)
      e077  arxiv:1810.00058#02 => #00   VERIFIED below (the record's proof in nat, eps = 1/D)
      e109  arxiv:2210.16971#01 => #00   candidate (the #01 endpoint is a BLOCKED placeholder)
      e116  opg:the_erdos_hajnal_conjecture => arxiv:1912.02342#00
                                         VERIFIED below (shattering gadget H_d
                                         + VC-monotonicity, foundations/vc.v)

    NB the derived file meta/corpus_relations.json still records
    [from_formal_name]/[to_formal_name] = null for the endpoints this wave
    authors; it must be regenerated (meta/build_corpus_relations.py) before
    meta/build_edge_graph.py can re-check these [gc:] citations. *)

From GTBase Require Import base.
From Extremal.foundations Require Import degree_bounds ramsey vc.
From Extremal.conjectures Require Import D2ram X58 X118 X120 X195 X196 X223.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Wave-V vocabulary equivalences (2026-09-24) ************************

    meta/STATEMENT_IMPROVEMENTS.md and the X211-X229 faithfulness audit record
    three duplications carried by the X223 vocabulary.  Each is settled below by
    one named lemma; no statement body is changed.

    (1) eps-boundedness is spelled twice: X223 bounds every CLOSED neighbourhood
    ([d * |N[v]| < p * |V(G)|]), X58 bounds the MAXIMUM DEGREE
    ([d * Delta(G) < p * |V(G)|]).  The closed form implies the Delta form on a
    non-empty graph; the reusable half lives in
    [Extremal.foundations.degree_bounds.Delta_lt_of_cln_lt] and this is the
    named bridge between the two conjecture-file predicates.  The e076 edge
    below used to inline it. *)

Lemma x223_eps_bounded_implies_x58_epsilon_bounded (G : sgraph) (p d : nat) :
  0 < #|G| -> x223_eps_bounded G p d -> x58_epsilon_bounded G p d.
Proof. exact: Delta_lt_of_cln_lt. Qed.

(** The converse fails: [Delta G < |N[v]|] for a vertex of maximum degree, so
    the Delta form is strictly weaker and only the direction above is available. *)

(** (2) [x118_edges_between] (X118), [x120_edges_between] (X120) and
    [x223_edges_between] all count the ORDERED pairs [(a,b)] of [A x B] with
    [a -- b]: since library migration A8 all three are [GTBase.common.edges_between]
    (their former bodies differed only by the associativity of [&&]). *)

Lemma x118_edges_betweenE (G : sgraph) (A B : {set G}) :
  x118_edges_between A B = x223_edges_between A B.
Proof. by apply: eq_card => p; rewrite !inE andbA. Qed.

Lemma x120_edges_betweenE (G : sgraph) (A B : {set G}) :
  x120_edges_between A B = x223_edges_between A B.
Proof. by apply: eq_card => p; rewrite !inE andbA. Qed.

(** (3) On DISJOINT [A] and [B] the ordered-pair count is the cardinality of the
    set of CROSS EDGES of [G] -- the edges of [E(G)] meeting both [A] and [B],
    i.e. the library-level reading |E(A,B)| of the audit note.  Disjointness is
    what makes the two counts agree: it forbids an edge from being counted twice
    (once as [(a,b)] and once as [(b,a)]). *)

Lemma x223_edges_between_card_cross (G : sgraph) (A B : {set G}) :
  [disjoint A & B] ->
  x223_edges_between A B
    = #|[set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]|.
Proof. exact: edges_between_cross. Qed.

(** ** e076 -- Conjecture 1.4 for all H implies its open case H = K_3.

    Pure instantiation, plus one weakening step: X58's eps-boundedness uses the
    maximum degree (Delta(G) < eps|G|) whereas the recovered source condition, used
    by this wave, is the CLOSED neighbourhood one (|N[v]| < eps|G| for every v).
    Since Delta(G) = |N(x)| for some x and |N(x)| < |N[x]|, the closed form implies
    the Delta form, so the H-quantified statement applies to every graph this row
    quantifies over. *)
Theorem epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair :
  epsilon_bounded_h_free_anticomplete_pair_statement ->
  triangle_free_eps_bounded_anticomplete_pair_statement.
Proof.
move=> EH.
have [p [d [p0 [pd Hcore]]]] := EH 'K_3.
exists p, d; split => // G G1 Hfree Heps.
have G0 : 0 < #|G| by apply: leq_trans G1.
have Hfree58 : x58_induced_free G 'K_3 by exact: Hfree.
have Heps58 : x58_epsilon_bounded G p d.
  exact: x223_eps_bounded_implies_x58_epsilon_bounded G0 Heps.
have [A [B [Hac [HA HB]]]] := Hcore G G1 Hfree58 Heps58.
by exists A, B; split.
Qed.

(*@EDGE from=epsilon_bounded_h_free_anticomplete_pair_statement to=triangle_free_eps_bounded_anticomplete_pair_statement kind=implies status=verified proof=epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair cite="gc:e076" *)

(** ** e160 -- "k-nice for every large k" implies "k-nice for infinitely many k".

    Elementary: take the maximum of the two thresholds. *)
Theorem ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite :
  ramsey_nice_forest_family_eventual_statement ->
  ramsey_nice_forest_family_infinite_statement.
Proof.
move=> H r Fam r0 Hf k0.
have [k1 Hk1] := H r Fam r0 Hf.
by exists (maxn k0 k1); split; [exact: leq_maxl | apply: Hk1; exact: leq_maxr].
Qed.

(*@EDGE from=ramsey_nice_forest_family_eventual_statement to=ramsey_nice_forest_family_infinite_statement kind=implies status=verified proof=ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite cite="gc:e160" *)

(** ** e077 -- Conjecture 3.4 implies Conjecture 1.4 (arXiv:1810.00058), with eps = 1/D in nat.

    The record's own proof (tex l.334-366, with its lemma sparsetoanti l.373-381), the real powers
    replaced by naturals: eps = 1/D for D = max(6, s + 1, 3d %/ p + 1) from the source's p, d, s.
    - n <= D^D ([e077_small]): a vertex against its non-neighbours.
    - otherwise r, the integer D-th root of n ([e077_iroot], r >= D), and t = ceil(2r / D)
      ([e077_ceil], 2r <= tD <= 3r); X58's maximum-degree bound gives X223's closed-neighbourhood
      bound for these n ([e077_eps_transfer]); the source at c = 1/(2t) gives a c-sparse pair with
      |A| >= t ([e077_exp_bound]); a variant of sparsetoanti at c x = 1/2 makes it anticomplete
      ([e077_avg], [e077_sparse_to_anticomplete]); then the two bounds ([e077_A_bound],
      [e077_B_bound]).
    This is the cleaning argument the candidate note recorded here before. *)

(** *** L1: the integer D-th root *)
Lemma e077_iroot (D n : nat) : 0 < D -> exists r, r ^ D <= n < r.+1 ^ D.
Proof.
(* ex_minn on [fun r => n < r.+1 ^ D] (n itself is a witness: n < n.+1 <= n.+1 ^ D); the least r has
   r ^ D <= n (r = 0: 0 ^ D = 0; r = r'.+1: minimality at r'). *)
move=> D0.
have ex : exists r, n < r.+1 ^ D.
  exists n; apply: (leq_trans (ltnSn n)); rewrite -{1}(expn1 n.+1) leq_pexp2l.
  - by [].
  - by [].
  - by [].
case: (ex_minnP ex) => r hr hmin.
exists r; rewrite hr andbT.
case: r hr hmin => [|r'] hr hmin; first by rewrite exp0n.
by rewrite leqNgt; apply/negP => h; move: (hmin r' h); rewrite ltnn.
Qed.

(** *** L2: degrees into B, averaging and sparse-to-anticomplete

    My variant of the record's lemma sparsetoanti (tex l.373-381, where c x <= 1/4): here c x = 1/2,
    the t vertices of A with the fewest neighbours in B, then the vertices of B with none among
    them. *)
Definition e077_degB (G : sgraph) (B : {set G}) (a : G) : nat := #|[set b in B | a -- b]|.

Lemma e077_edges_between_sum (G : sgraph) (A B : {set G}) :
  edges_between A B = \sum_(a in A) e077_degB B a.
Proof.
(* the pair set partitioned by its first coordinate; each slice reindexed by b |-> (a, b) *)
rewrite /edges_between -sum1_card.
rewrite (partition_big (fun p : G * G => p.1) (mem A)) /=; first last.
apply: eq_bigr => a aA.
rewrite /e077_degB -[RHS]sum1_card.
rewrite (reindex_onto (fun b : G => (a, b)) (fun p : G * G => p.2)) /=; last first.
(* the goals in order: the slice, the reindexing side condition, the partition side condition *)
apply: eq_bigl => b; rewrite !inE aA /= !eqxx !andbT.
by [].
by move=> [x y] /andP[_ /eqP /= ->].
by move=> p; rewrite inE => /and3P[].
Qed.

Lemma e077_avg (G : sgraph) (A B : {set G}) (t : nat) :
  t <= #|A| ->
  exists A' : {set G},
    [/\ A' \subset A, #|A'| = t & #|A| * edges_between A' B <= t * edges_between A B].
Proof.
(* induction on #|A| - t: drop a vertex y of largest degree into B; then
   #|A| * e(A :\ y, B) <= #|A :\ y| * e(A, B), since e(A :\ y, B) <= #|A :\ y| * deg y *)
move=> tA.
rewrite !e077_edges_between_sum.
have main : forall k (A0 : {set G}), #|A0| = k + t ->
  exists A' : {set G}, [/\ A' \subset A0, #|A'| = t &
    #|A0| * (\sum_(a in A') e077_degB B a) <= t * (\sum_(a in A0) e077_degB B a)].
  elim=> [|k IH] A0 hA0.
    by exists A0; rewrite hA0 add0n.
  have [x xA0] : exists x, x \in A0.
    by apply/set0Pn; rewrite -card_gt0 hA0 addSn.
  case: (@arg_maxnP G x (mem A0) (e077_degB B) xA0) => y yA0 ymax.
  have yA : y \in A0 := yA0.
  have ym : forall j, j \in A0 -> e077_degB B j <= e077_degB B y := ymax.
  clear yA0 ymax.
  have hA1 : #|A0 :\ y| = k + t by move: hA0; rewrite (cardsD1 y A0) yA add1n addSn => -[].
  have [A' [A'A1 cA' hA']] := IH _ hA1.
  exists A'; split => //.
    by apply: subset_trans A'A1 (subD1set _ _).
  have key : \sum_(a in A0 :\ y) e077_degB B a <= #|A0 :\ y| * e077_degB B y.
    rewrite -sum_nat_const; apply: leq_sum => j; rewrite inE => /andP[_ jA]; exact: ym.
  rewrite (big_setD1 y yA) /= (cardsD1 y A0) yA add1n.
  move: hA' key; set n1 := #|A0 :\ y|; set e1 := \sum_(a in A0 :\ y) e077_degB B a.
  set s1 := \sum_(a in A') e077_degB B a; set dy := e077_degB B y => hA' key.
  case: (posnP n1) => [n10|n1pos].
    have t0 : t = 0 by move: hA1; rewrite -/n1 n10 => /esym/eqP; rewrite addn_eq0 => /andP[_ /eqP].
    have A'0 : A' = set0 by apply/cards0_eq; rewrite cA' t0.
    by rewrite /s1 A'0 big_set0 muln0.
  rewrite -(leq_pmul2l n1pos).
  apply: (@leq_trans (n1.+1 * (t * e1))).
    by rewrite mulnCA leq_pmul2l.
  rewrite (mulnCA n1.+1) (mulnCA n1) leq_mul2l; apply/orP; right.
  by rewrite mulSn mulnDr leq_add2r.
have [A' [A'A cA' hA']] := main (#|A| - t) A (esym (subnK tA)).
by exists A'; rewrite e077_edges_between_sum.
Qed.

Lemma e077_sparse_to_anticomplete (G : sgraph) (A B : {set G}) (t : nat) :
  [disjoint A & B] -> t <= #|A| -> 2 * t * edges_between A B <= #|A| * #|B| ->
  exists A' B' : {set G},
    [/\ A' \subset A, B' \subset B, #|A'| = t, x58_anticomplete A' B' & #|B| <= 2 * #|B'|].
Proof.
(* A' by e077_avg; then 2 e(A', B) <= #|B|; B' := [set b in B | [forall a in A', ~~ (a -- b)]];
   the rest of B lies in the union of the neighbourhoods in B of A', of size at most e(A', B). *)
move=> dAB tA hs.
have [A' [A'A cA' hA']] := e077_avg B tA.
have h2 : 2 * edges_between A' B <= #|B|.
  case: (posnP #|A|) => [A0|Apos].
    have t0 : t = 0 by apply/eqP; rewrite -leqn0 -A0.
    have A'0 : A' = set0 by apply/cards0_eq; rewrite cA' t0.
    by rewrite A'0 e077_edges_between_sum big_set0 muln0.
  rewrite -(leq_pmul2l Apos) mulnCA.
  apply: leq_trans (_ : 2 * (t * edges_between A B) <= _).
    by rewrite leq_mul2l hA' orbT.
  by rewrite mulnA.
set B' := [set b in B | [forall a in A', ~~ (a -- b)]].
have hN : #|B :\: B'| <= edges_between A' B.
  rewrite e077_edges_between_sum; apply: leq_trans (card_bigcup_leq _ _).
  apply: subset_leq_card; apply/subsetP => b; rewrite !inE => /andP[hb bB].
  move: hb; rewrite bB /= negb_forall => /existsP[a]; rewrite negb_imply negbK => /andP[aA' ab].
  by apply/bigcupP; exists a => //; rewrite inE bB ab.
exists A', B'; split => //.
- by apply/subsetP => b; rewrite inE => /andP[].
- apply/andP; split.
    apply: (disjointW A'A _ dAB); apply/subsetP => b; rewrite inE => /andP[].
    by move=> bB _.
  apply/negP => /neighborP [a [b [aA' bB' ab]]].
  by move: bB'; rewrite inE => /andP[_ /forallP /(_ a)]; rewrite aA' ab.
- have hBB : #|B| = #|B'| + #|B :\: B'|.
    by rewrite -(cardsID B' B) (setIidPr _) //; apply/subsetP => b; rewrite inE => /andP[].
  have hy : 2 * #|B :\: B'| <= #|B| by apply: leq_trans h2; rewrite leq_mul2l hN orbT.
  move: hy; rewrite hBB mul2n -addnn leq_add2r => hy.
  by rewrite mul2n -addnn leq_add2l.
Qed.

(** *** L3: small graphs (n <= D ^ D) *)
Lemma e077_small (G : sgraph) (D : nat) :
  4 <= D -> 1 < #|G| -> D * Delta G < #|G| -> #|G| <= D ^ D ->
  exists A B : {set G},
    [/\ x58_anticomplete A B, 1 ^ D * #|G| ^ 1 <= D ^ D * #|A| ^ D & 1 * #|G| <= D * #|B|].
Proof.
(* A = [set v], B = ~: N[v]; with n = m.+1, #|B| + #|N(v)| = m and D #|N(v)| <= D Delta <= m, so
   D m <= D #|B| + m, i.e. (D - 1) m <= D #|B|, and m.+1 <= 2 m <= (D - 1) m. *)
move=> D4 n1 hD hn.
case/card_gt0P: (ltnW n1) => v _.
exists [set v], (~: N[v]); split.
- apply/andP; split; first by rewrite disjoints1 inE negbK v_in_clneigh.
  apply/negP => /neighborP [a [b [aA bB ab]]].
  move: aA bB; rewrite !inE => /eqP aV; subst a.
  by rewrite ab orbT.
- by rewrite exp1n mul1n expn1 cards1 exp1n muln1.
- have hc : #|N[v]| = #|N(v)|.+1 by rewrite opn_cln (cardsD1 v N[v]) v_in_clneigh.
  have hsum : #|~: N[v]| + #|N(v)|.+1 = #|G| by rewrite -hc addnC cardsC.
  have hk : #|N(v)| <= Delta G by rewrite /Delta; apply: (bigmax_sup v).
  rewrite mul1n.
  have hDk : D * #|N(v)| < #|G| by apply: leq_ltn_trans hD; rewrite leq_mul2l hk orbT.
  have [m hm] : exists m, #|G| = m.+1 by exists #|G|.-1; rewrite prednK // ltnW.
  move: hsum hDk n1; rewrite hm; set b := #|~: N[v]|; set k := #|N(v)| => hsum hDk n1.
  have hbk : b + k = m by move: hsum; rewrite addnS => -[].
  have e1 : D * m <= D * b + m by rewrite -{1}hbk mulnDr leq_add2l -ltnS.
  have e2 : D.-1 * m <= D * b.
    rewrite -(leq_add2r m) -mulSnr prednK //; exact: (leq_trans _ D4).
  have e3 : m.+1 <= 2 * m by rewrite mul2n -addnn -addn1 leq_add2l.
  have e4 : 2 * m <= D.-1 * m by rewrite leq_mul2r -ltnS prednK ?(leq_trans _ D4) ?D4 ?orbT.
  exact: leq_trans e3 (leq_trans e4 e2).
Qed.

(** *** L4: X58's eps-bound (Delta, open) gives X223's (closed) for large n *)
Lemma e077_eps_transfer (G : sgraph) (p d D : nat) :
  2 * d <= p * D -> 2 * d < p * #|G| -> D * Delta G < #|G| -> x223_eps_bounded G p d.
Proof.
(* #|N[v]| = #|N(v)|.+1 <= Delta.+1; 2 d Delta <= p D Delta <= p n and 2 d < p n. *)
move=> h1 h2 h3 v.
have hc : #|N[v]| = #|N(v)|.+1 by rewrite opn_cln (cardsD1 v N[v]) v_in_clneigh.
have hk : #|N(v)| <= Delta G by rewrite /Delta; apply: (bigmax_sup v).
apply: (@leq_ltn_trans (d * (Delta G).+1)); first by rewrite leq_mul2l hc ltnS hk orbT.
rewrite -(ltn_pmul2l (_ : 0 < 2)) // mulnS mulnDr.
have bb : 2 * (d * Delta G) <= p * #|G|.
  rewrite mulnA; apply: leq_trans (_ : p * D * Delta G <= _); first by rewrite leq_mul2r h1 orbT.
  by rewrite -mulnA leq_mul2l ltnW ?orbT.
by rewrite (mul2n (p * #|G|)) -addnn -addSn; exact: leq_add h2 bb.
Qed.

(** *** L5: the exponent inequalities *)

(** t := ceil(2r / D): 2 r <= t D < 2 r + D. *)
Lemma e077_ceil (r D : nat) : 0 < D -> exists t, 2 * r <= t * D /\ t * D < 2 * r + D.
Proof.
(* the least t with 2 r <= t D; minimality bounds it above *)
move=> D0.
have ex : exists t, 2 * r <= t * D by exists (2 * r); rewrite leq_pmulr.
case: (ex_minnP ex) => t ht hmin.
exists t; split => //.
case: t ht hmin => [|t'] ht hmin; first by rewrite mul0n addn_gt0 D0 orbT.
rewrite mulSn addnC ltn_add2r ltnNge; apply/negP => h.
by move: (hmin t' h); rewrite ltnn.
Qed.

(** |A| >= t: d (2t)^s t <= p r^(s+1) <= p n, from 3 d <= p D, 6 <= D, s + 1 <= D and t D <= 3 r. *)
Lemma e077_exp_bound (p d s D r t n : nat) :
  3 * d <= p * D -> 6 <= D -> s.+1 <= D -> 0 < r -> r ^ D <= n -> t * D <= 3 * r ->
  d * ((2 * t) ^ s * t) <= p * n.
Proof.
(* times D^(s+1): d 2^s (t D)^(s+1) <= d 2^s 3^(s+1) r^(s+1),
   and d 2^s 3^(s+1) = 3 d 6^s <= p D D^s *)
move=> h3 D6 sD r0 rn tD.
have D0 : 0 < D by apply: leq_trans D6.
rewrite expnMn -mulnA -expnSr.
apply: (@leq_trans (p * r ^ s.+1)); last first.
  by rewrite leq_mul2l (leq_trans (leq_pexp2l r0 sD) rn) orbT.
have hDp : 0 < D ^ s.+1 by rewrite expn_gt0 D0.
rewrite -(leq_pmul2r hDp).
rewrite -!mulnA -expnMn.
apply: (@leq_trans (d * (2 ^ s * (3 * r) ^ s.+1))).
  by rewrite leq_mul2l leq_mul2l leq_exp2r // tD !orbT.
rewrite expnMn (mulnC (r ^ s.+1) (D ^ s.+1)) !mulnA leq_mul2r; apply/orP; right.
rewrite expnSr mulnA mulnC -(mulnA d) mulnA -expnMn expnS mulnA.
apply: leq_mul h3 _.
case: s sD hDp => [|s'] sD hDp; first by rewrite !expn0.
by rewrite leq_exp2r.
Qed.

(** The A side: (D t)^D >= (2 r)^D >= (r + 1)^D > n. *)
Lemma e077_A_bound (D r t n : nat) :
  0 < r -> n < r.+1 ^ D -> 2 * r <= t * D -> 1 ^ D * n ^ 1 <= D ^ D * t ^ D.
Proof.
move=> r0 hn ht.
rewrite exp1n mul1n expn1 -expnMn; apply: ltnW (leq_trans hn _).
case: D ht hn => [|D'] ht hn; first by rewrite !expn0.
rewrite leq_exp2r // mulnC; apply: leq_trans ht.
by rewrite mul2n -addnn -addn1 leq_add2l.
Qed.

(** The B side: 3 d n <= p D n <= D d |B| <= 2 D d |B'|. *)
Lemma e077_B_bound (p d D n b b' : nat) :
  0 < d -> 3 * d <= p * D -> p * n <= d * b -> b <= 2 * b' -> 1 * n <= D * b'.
Proof.
move=> d0 h3 hb hbb; rewrite mul1n.
have e : d * (3 * n) <= d * (2 * (D * b')).
  rewrite mulnA (mulnC d 3); apply: leq_trans (_ : p * D * n <= _).
    by rewrite leq_mul2r h3 orbT.
  rewrite (mulnC p D) -mulnA; apply: leq_trans (_ : D * (d * b) <= _).
    by rewrite leq_mul2l hb orbT.
  by rewrite mulnCA leq_mul2l (mulnCA 2) leq_mul2l hbb !orbT.
rewrite leq_pmul2l // in e.
rewrite -(leq_pmul2l (_ : 0 < 3)) //; apply: leq_trans e _.
by rewrite leq_mul2r orbT.
Qed.

(** *** L6: the edge *)

(** Conjecture 3.4 for every H gives Conjecture 1.4 for every H, with eps = 1/D. *)
(*@EDGE from=h_free_eps_bounded_sparse_pair_statement to=epsilon_bounded_h_free_anticomplete_pair_statement kind=implies status=verified proof=e077_h_free_eps_bounded_sparse_pair_implies_epsilon_bounded_h_free_anticomplete_pair cite="gc:e077" note="Unconditional. The record's own proof (arXiv:1810.00058v2 tex l.334-366) in nat, with eps = 1/D for D = max(6, s + 1, 3d %/ p + 1) from the source's p, d, s. Graphs with n <= D^D: a vertex against its non-neighbours (e077_small; X58's D Delta(G) < n gives D |B| >= n). Otherwise r, the integer D-th root of n (e077_iroot, r >= D), and t = ceil(2r/D) (e077_ceil); X58's maximum-degree bound gives X223's closed-neighbourhood bound for these n (e077_eps_transfer); the source at c = 1/(2t) gives a c-sparse pair (A, B) with |A| >= t (e077_exp_bound: d (2t)^s t <= p r^(s+1) <= p n) and d |B| >= p n; the t vertices of A with the fewest neighbours in B meet at most |B|/2 of B (e077_avg, e077_sparse_to_anticomplete: a variant of the record's lemma sparsetoanti, tex l.373-381, at c x = 1/2 instead of 1/4); then (D t)^D >= (2r)^D > n (e077_A_bound) and D |B'| >= n (e077_B_bound)." *)
Theorem e077_h_free_eps_bounded_sparse_pair_implies_epsilon_bounded_h_free_anticomplete_pair :
  h_free_eps_bounded_sparse_pair_statement -> epsilon_bounded_h_free_anticomplete_pair_statement.
Proof.
(* D := maxn 6 (maxn s.+1 ((3 * d) %/ p).+1), so p D >= 3 d; eps = 1 / D. n <= D ^ D: e077_small.
   Otherwise r by e077_iroot (r >= D), t by e077_ceil (2 r <= t D <= 3 r), the source at (1, 2 t)
   with e077_eps_transfer, |A| >= t by e077_exp_bound, e077_sparse_to_anticomplete, e077_A_bound,
   e077_B_bound. *)
move=> HS H.
have [p [d [s [p0 pd s0 Hc]]]] := HS H.
pose D := maxn 6 (maxn s.+1 ((3 * d) %/ p).+1).
have D6 : 6 <= D by rewrite leq_maxl.
have Ds : s.+1 <= D by rewrite (leq_trans _ (leq_maxr _ _)) // leq_maxl.
have Dp : 3 * d <= p * D.
  apply: ltnW; apply: (leq_trans (ltn_ceil _ p0)); rewrite mulnC leq_mul2l.
  by rewrite (leq_trans _ (leq_maxr _ _)) ?leq_maxr ?orbT.
have D0 : 0 < D by apply: leq_trans D6.
exists 1, D; split => //; split; first by apply: leq_trans D6.
move=> G G1 Hfree Heps; rewrite /x58_epsilon_bounded mul1n in Heps.
case: (leqP #|G| (D ^ D)) => [small|large].
  (* R1: small graphs *)
  have [A [B [hac hA hB]]] := e077_small (leq_trans (isT : 3 < 6) D6) G1 Heps small.
  by exists A, B.
(* R2: r the integer D-th root of n, r >= D; t = ceil(2 r / D) *)
have [r /andP[rl ru]] := e077_iroot #|G| D0.
have rD : D <= r.
  rewrite leqNgt; apply/negP => hr.
  have h1 : r.+1 ^ D <= D ^ D by rewrite leq_exp2r.
  by move: (leq_ltn_trans h1 large); rewrite ltnNge ltnW.
have r0 : 0 < r by apply: leq_trans rD.
have d0 : 0 < d by apply: leq_trans pd.
have [t [t2 t3]] := e077_ceil r D0.
have tD : t * D <= 3 * r.
  by apply: ltnW; apply: (leq_trans t3); rewrite (mulSn 2 r) addnC leq_add2r.
have t0 : 0 < t.
  move: t2; case: t {t3 tD} => //; rewrite mul0n leqn0 muln_eq0 /= => /eqP r00.
  by move: r0; rewrite r00.
(* R3: the eps transfer, then the source at (a, b) = (1, 2 t) *)
have h2d : 2 * d <= p * D by apply: leq_trans Dp; rewrite leq_mul2r orbT.
have hDn : D < #|G| by apply: leq_ltn_trans large; rewrite -{1}(expn1 D) leq_pexp2l.
have hpn : 2 * d < p * #|G| by apply: leq_ltn_trans h2d _; rewrite ltn_pmul2l.
have Heps' := e077_eps_transfer h2d hpn Heps.
have b0 : 0 < 2 * t by rewrite muln_gt0 t0.
have ab : 1 <= 2 * t by [].
have [A [B [[dAB sp] hA hB]]] := Hc G G1 Hfree Heps' 1 (2 * t) b0 ab.
have tA : t <= #|A|.
  rewrite leqNgt; apply/negP => hlt.
  have hb := e077_exp_bound Dp D6 Ds r0 rl tD.
  move: hA; rewrite exp1n mul1n => hA.
  have hlt' : d * ((2 * t) ^ s * #|A|) < d * ((2 * t) ^ s * t).
    by rewrite ltn_pmul2l // ltn_pmul2l // expn_gt0 b0.
  by move: (leq_trans (leq_ltn_trans hA hlt') hb); rewrite ltnn.
(* R4: sparse to anticomplete; R5: the two bounds *)
have sp' : 2 * t * edges_between A B <= #|A| * #|B| by move: sp; rewrite mul1n.
have [A' [B' [A'A B'B cA' hac hBB]]] := e077_sparse_to_anticomplete dAB tA sp'.
exists A', B'; split => //; split.
  by rewrite cA'; exact: e077_A_bound r0 ru t2.
exact: e077_B_bound d0 Dp hB hBB.
Qed.

(** ** e109 -- directed forcing implies directed Sidorenko (CANDIDATE).

    The source endpoint arxiv:2210.16971#01 is recorded BLOCKED: its Rocq body
    ([directed_forcing_cyclic_statement]) is a PLACEHOLDER whose conclusion is
    the Sidorenko property rather than the forcing property, because forcing is a
    graph-limit notion with no finite form available here.  The corpus argument
    (forcing => Sidorenko by an interpolation / intermediate-value argument on
    oriented graphons, plus Theorem 1.5 for oriented forests) therefore has no
    faithful formal counterpart, and the placeholder does NOT entail the target
    either: it carries the extra hypothesis "the underlying graph has a cycle",
    which the bipartite target does not (oriented forests are a genuine case of
    Conjecture 1.4).  Recorded as a candidate. *)
(*@EDGE from=directed_forcing_cyclic_statement to=directed_sidorenko_bipartite_statement kind=implies status=candidate proved=false cite="gc:e109" note="Source endpoint is a BLOCKED placeholder (Sidorenko conclusion, not forcing). Even as stated it does not close: the placeholder assumes a cycle in the underlying graph, while the target also covers oriented forests." *)

(** ** e116 -- Erdos-Hajnal implies its VC-dimension specialisation.

    The reduction is now FORMAL (the two missing ingredients live in
    Extremal.foundations.vc).  For a fixed [d], let [H_d := shatter_graph d.+1]
    be the bipartite gadget on ['I_(d+1) + {set 'I_(d+1)}] in which [inr S] is
    adjacent exactly to the [inl i] with [i \in S].  Then:

    - the ['I_(d+1)]-side [shatter_side d.+1] (of size d+1) is SHATTERED by the
      neighbourhoods -- the subset cut out of it by [N(inr S)] is exactly [S] --
      so [H_d] has VC dimension at least d+1 ([not_vc_dim_leq_shatter_graph]);
    - VC dimension is MONOTONE under induced subgraphs: an [isubgraph]
      [i : F -> G] sends neighbourhood traces to neighbourhood traces
      ([opn_cap_imset]), hence shattered sets to shattered sets of the same size
      ([vc_dim_leq_isubgraph]).

    So a graph [G] of VC dimension at most [d] has no induced copy of [H_d], and
    Erdos-Hajnal for the single graph [H := H_d] applies.  Its conclusion
    [#|G| ^ a <= (maxn omega alpha) ^ b] is turned into the target's
    [#|G| <= #|S| ^ q] with [q := b]: [#|G| <= #|G| ^ a] (as [0 < a] and
    [0 < #|G|]), and [maxn omega alpha] is realised by an actual clique or
    stable set ([clique_witness] / [stable_witness], foundations/ramsey.v), whose
    cardinal is then raised to the b-th power.  The empty host is handled
    separately ([S := set0], a clique, and [#|G| = 0]) because the target has no
    non-emptiness guard while Erdos-Hajnal does. *)
Theorem the_erdos_hajnal_implies_vc_dimension_erdos_hajnal :
  the_erdos_hajnal_statement -> vc_dimension_erdos_hajnal_statement.
Proof.
move=> EH d _.
have [a [b [a0 [ab Hcore]]]] := EH (shatter_graph d.+1).
have b0 : 0 < b by exact: leq_trans a0 ab.
exists b; split => // G Hvc.
have Hfree : ~ has_induced_copy (shatter_graph d.+1) G.
  case=> i; apply: (@not_vc_dim_leq_shatter_graph d).
  exact: (@vc_dim_leq_isubgraph _ _ i d Hvc).
have [G0|G0] := posnP #|G|.
  exists set0; split; last by rewrite G0.
  by apply/orP; left; apply/cliqueP; apply: small_clique; rewrite cards0.
have Hb := Hcore G G0 Hfree.
have [K /and3P[_ clK oK]] := clique_witness [set: G].
have [A /and3P[_ stA aA]] := stable_witness [set: G].
have Hkey : #|G| <= (maxn #|K| #|A|) ^ b.
  apply: leq_trans (leq_trans Hb _); first by rewrite -{1}(expn1 #|G|) leq_pexp2l.
  by rewrite leq_exp2r // geq_max !leq_max oK aA orbT.
case: (leqP #|A| #|K|) => [AK|KA].
  by exists K; rewrite clK; split => //; move: Hkey; rewrite (maxn_idPl AK).
by exists A; rewrite stA orbT; split => //; move: Hkey; rewrite (maxn_idPr (ltnW KA)).
Qed.

(*@EDGE from=the_erdos_hajnal_statement to=vc_dimension_erdos_hajnal_statement kind=implies status=verified proof=the_erdos_hajnal_implies_vc_dimension_erdos_hajnal cite="gc:e116" note="H_d := shatter_graph d.+1 (bipartite gadget on 'I_(d+1) + {set 'I_(d+1)}, inr S ~ inl i iff i in S): its 'I_(d+1)-side is shattered, so VC-dim(H_d) > d (foundations/vc.v, not_vc_dim_leq_shatter_graph), and VC-dim is monotone under isubgraphs (opn_cap_imset, vc_dim_leq_isubgraph); hence every G with x223_vc_dim_leq G d is H_d-induced-free. EH at H = H_d gives #|G|^a <= (maxn omega alpha)^b; q := b, using #|G| <= #|G|^a and the clique/stable witnesses of ramsey.v. Empty host handled by S = set0." *)

Print Assumptions x223_eps_bounded_implies_x58_epsilon_bounded.
Print Assumptions x118_edges_betweenE.
Print Assumptions x120_edges_betweenE.
Print Assumptions x223_edges_between_card_cross.
Print Assumptions epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair.
Print Assumptions ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite.
Print Assumptions the_erdos_hajnal_implies_vc_dimension_erdos_hajnal.
Print Assumptions e077_h_free_eps_bounded_sparse_pair_implies_epsilon_bounded_h_free_anticomplete_pair.
