(** * Chromatic.conjectures.grounding_X268 -- grounding certificates for wave X268 (2026-10-31)

    For each of the three rows: hyp_inhabited (the conditions of the body hold together at a small instance, and
    the statement gives its consequence) and not_trivially_true (a variant without one hypothesis is false and
    implies the statement); and, in every row, the helper_sanity groups of the four X268.v helpers.
    - arxiv:2209.09107#01: at K_2 and C = 1 the matching of its edge leaves AT = 1, the empty one AT = 2 > 3 / 2;
      the statement's constant is at least 1 (an edgeless graph with a vertex).  Without "Delta is the maximum
      degree of G" (any D in its place) the row is false at D = 0: K_(2C+1) minus a matching keeps at least
      2 C^2 edges, so some outdegree is at least C (the averaging bound |E| + |V| <= |V| k of g268_at_lower).
    - arxiv:2202.09118#04: the guard chi(G) > c' omega(G)^d' holds at the iterated Mycielski graphs of
      Chromatic.applications.cochromatic_gap (clique number 4, chromatic number n + 7); without it the row is false
      at K_1 (chi <= 1 everywhere).  K_1 is self-isolating (the paper's proof for complete graphs, at k = 1).
    - studies:std_plummer_zha_conjecture: the Petersen graph is 3-connected, internally 4-connected and a
      pentagraph, checked by enumeration ([vm_compute] on its duplicate-free walks and on breadth-first searches);
      without the pentagraph hypothesis the row is false at K_4 (3-connected, vacuously internally 4-connected,
      chi = 4).  P_5 is not internally 4-connected; K_3 and C_7 are not pentagraphs. *)

From GTBase Require Import base common set_pairs induced_cycles petersen path_graphs.
From Chromatic.foundations Require Import alon_tarsi.
From Chromatic.applications.cochromatic_gap Require Import mycielski_gap cochromatic_gap.
From Chromatic.conjectures Require Import X268.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** arxiv:2209.09107#01: the Alon-Tarsi number ********************************************************* *)

(** ** Counting an orientation *)

(* The outdegrees of an arc set sum to its number of arcs. *)
Lemma g268_sum_outdegree (G : sgraph) (A : {set G * G}) : \sum_(v : G) at_outdegree A v = #|A|.
Proof.
rewrite /at_outdegree (eq_bigr (fun v => \sum_(w | (v, w) \in A) 1)) => [v _|].
  by rewrite -sum1_card; apply: eq_bigl => w; rewrite inE.
by rewrite pair_big_dep /= -sum1_card; apply: eq_bigl => -[x y].
Qed.

(* An orientation of G (every arc an edge, every edge exactly one arc) has as many arcs as G has edges. *)
Lemma g268_card_orientation (G : sgraph) (A : {set G * G}) :
  (forall x y : G, (x, y) \in A -> x -- y) ->
  (forall x y : G, x -- y -> ((x, y) \in A) (+) ((y, x) \in A)) -> #|A| = #|E(G)|.
Proof.
move=> h1 h2.
have inj : {in A &, injective (fun p : G * G => [set p.1; p.2])}.
  move=> [x y] [x' y'] /= hp hq he.
  have xy := h1 _ _ hp; have xy' := h1 _ _ hq.
  have : x \in [set x'; y'] by rewrite -he !inE eqxx.
  have : y \in [set x'; y'] by rewrite -he !inE eqxx orbT.
  rewrite !inE => /orP[/eqP ey | /eqP ey] /orP[/eqP ex | /eqP ex].
  - by move: xy; rewrite ex ey sg_irrefl.
  - by move: (h2 _ _ xy); rewrite hp ex ey hq.
  - by rewrite ex ey.
  - by move: xy; rewrite ex ey sg_irrefl.
rewrite -(card_in_imset inj); apply: eq_card => e.
apply/imsetP/edgesP => [[[x y] hp ->] | [x [y [-> xy]]]].
  by exists x, y; split=> //; exact: h1.
move: (h2 _ _ xy); case hxy: ((x, y) \in A); case hyx: ((y, x) \in A) => //= _.
  by exists (x, y).
by exists (y, x) => //=; rewrite setUC.
Qed.

(* A matching has at most #|G| / 2 edges. *)
Lemma g268_matching_card (G : sgraph) (M : {set {set G}}) : matching M -> 2 * #|M| <= #|G|.
Proof.
case=> hsub hdis.
have triv : trivIset M.
  apply/trivIsetP => e1 e2 h1 h2 ne; apply/pred0P => x /=; apply/negP => /andP[x1 x2].
  by move/eqP: ne; apply; exact: hdis x1 x2.
have two e : e \in M -> #|e| = 2.
  by move/hsub/edgesP => [x [y [-> xy]]]; rewrite cards2 (sg_edgeNeq xy).
have -> : 2 * #|M| = \sum_(e in M) #|e|.
  by rewrite mulnC -sum_nat_const; apply: eq_bigr => e /two.
by rewrite (eqP triv); exact: max_card.
Qed.

(* An arc (x, y) gives x a positive outdegree. *)
Lemma g268_outdegree_pos (G : sgraph) (A : {set G * G}) (x y : G) : (x, y) \in A -> 0 < at_outdegree A x.
Proof. by move=> h; apply/card_gt0P; exists y; rewrite inE. Qed.

(* Every outdegree is less than k, so |E(G)| + |G| <= |G| k: some outdegree is at least the average |E| / |V|. *)
Lemma g268_at_lower (G : sgraph) (k : nat) : x268_at_le G k -> #|E(G)| + #|G| <= #|G| * k.
Proof.
case=> A [h1 h2 _ h4].
rewrite -(g268_card_orientation h1 h2) -g268_sum_outdegree.
have hs : \sum_(v : G) (at_outdegree A v).+1 <= \sum_(v : G) k by apply: leq_sum => v _; exact: h4.
move: hs; rewrite sum_nat_const cardT -cardE.
have e : \sum_(v : G) (at_outdegree A v).+1 = \sum_(v : G) at_outdegree A v + #|G|.
  under eq_bigr => v _ do rewrite -addn1.
  by rewrite big_split /= sum_nat_const cardT -cardE muln1.
by rewrite -e mulnC.
Qed.

(* A vertex forces k >= 1, an edge forces k >= 2. *)
Lemma g268_at_vertex (G : sgraph) (k : nat) (v : G) : x268_at_le G k -> 0 < k.
Proof. by case=> A [_ _ _ h4]; exact: leq_ltn_trans (leq0n _) (h4 v). Qed.

Lemma g268_at_edge (G : sgraph) (k : nat) (x y : G) : x -- y -> x268_at_le G k -> 1 < k.
Proof.
move=> xy [A [_ h2 _ h4]]; have := h2 x y xy.
case hxy: ((x, y) \in A) => /=.
  by move=> _; exact: leq_ltn_trans (g268_outdegree_pos hxy) (h4 x).
by case hyx: ((y, x) \in A) => //= _; exact: leq_ltn_trans (g268_outdegree_pos hyx) (h4 y).
Qed.

(* Every degree is less than the order. *)
Lemma g268_Delta_le (G : sgraph) : Delta G <= #|G|.-1.
Proof.
apply/bigmax_leqP => x _.
have h0 : 0 < #|G| by apply/card_gt0P; exists x.
rewrite -ltnS (ltn_predK h0) -cardsT; apply: proper_card; apply/properP; split; first exact: subsetT.
by exists x; rewrite ?inE ?sg_irrefl.
Qed.

(* A single arc between two distinct vertices is an Alon-Tarsi orientation of itself: its only Eulerian
   sub-digraph is the empty one. *)
Lemma g268_single_arc_at (G : sgraph) (a b : G) : a != b -> at_alon_tarsi [set (a, b)].
Proof.
move=> ab.
have nE : ~~ at_eulerian [set (a, b)].
  apply/negP => /forallP /(_ a) /eqP.
  rewrite /at_outdegree /at_indegree.
  have -> : [set w | (a, w) \in [set (a, b)]] = [set b] by apply/setP => w; rewrite !inE xpair_eqE eqxx.
  have -> : [set w | (w, a) \in [set (a, b)]] = set0.
    by apply/setP => w; rewrite !inE xpair_eqE eq_sym (negbTE ab) andbF.
  by rewrite cards1 cards0.
have hE : at_eulerian_subgraphs [set (a, b)] = [set set0].
  apply/setP => B; rewrite !inE subset1.
  case: (B =P set0) => [-> | hB]; first by rewrite orbT at_empty_eulerian.
  by case: (B =P [set (a, b)]) => [-> | _] //=; rewrite (negbTE nE).
rewrite /at_alon_tarsi /at_even_eulerian /at_odd_eulerian hE.
have -> : [set B in [set set0] | ~~ odd #|B|] = [set set0 : {set G * G}].
  by apply/setP => B; rewrite !inE; case: (B =P set0) => [-> | ]; rewrite ?cards0.
have -> : [set B in [set set0] | odd #|B|] = set0 :> {set {set G * G}}.
  by apply/setP => B; rewrite !inE; case: (B =P set0) => [-> | ]; rewrite ?cards0.
by rewrite cards1 cards0.
Qed.

Local Notation o20 := (@Ordinal 2 0 isT).
Local Notation o21 := (@Ordinal 2 1 isT).

(* AT(K_2) = 2. *)
Lemma g268_at_K2 : x268_at_le 'K_2 2.
Proof.
exists [set (o20, o21)]; split.
- by move=> x y; rewrite inE xpair_eqE => /andP[/eqP -> /eqP ->].
- by move=> [[|[|x]] hx] // [[|[|y]] hy] //=; rewrite !inE.
- exact: g268_single_arc_at.
- move=> v; rewrite ltnS; apply: leq_trans (subset_leq_card (B := [set o21]) _) _; last by rewrite cards1.
  by apply/subsetP => w; rewrite !inE xpair_eqE => /andP[_ ->].
Qed.

Lemma g268_at_K2_not1 : ~ x268_at_le 'K_2 1.
Proof. by move/(@g268_at_edge 'K_2 1 o20 o21 isT). Qed.

(* Two distinct vertices of K_2 span it. *)
Lemma g268_K2_pair (x y : 'K_2) : x != y -> [set x; y] = [set: 'K_2].
Proof. by move=> xy; apply/eqP; rewrite eqEcard subsetT cardsT card_ord cards2 xy. Qed.

Definition g268_am_hyp_claim : Prop :=
  [/\ matching [set [set: 'K_2]],
      x268_at_le (del_edge_set 'K_2 [set [set: 'K_2]]) 1,
      2 * 1 <= Delta 'K_2 + 2 * 1,
      ~ (exists k : nat, 2 * k <= Delta 'K_2 + 2 * 1 /\ x268_at_le (del_edge_set 'K_2 set0) k) &
      (alon_tarsi_matching_removal_statement ->
         exists C : nat, 1 <= C /\ forall G : sgraph, exists M : {set {set G}},
           matching M /\ exists k : nat, 2 * k <= Delta G + 2 * C /\ x268_at_le (del_edge_set G M) k)].

Theorem g268_am_hyp_inhabited : g268_am_hyp_claim.
Proof.
have DK2 : Delta 'K_2 <= 1 by have := g268_Delta_le 'K_2; rewrite card_ord.
split.
- split.
  + move=> e; rewrite inE => /eqP ->; apply/edgesP; exists o20, o21; split=> //.
    by rewrite g268_K2_pair.
  + by move=> e1 e2; rewrite !inE => /eqP -> /eqP ->.
- exists set0; split.
  + by move=> x y; rewrite inE.
  + move=> x y; rewrite del_edge_setE => /andP[xy].
    have nxy : x != y by rewrite (sg_edgeNeq xy).
    by rewrite inE (@g268_K2_pair x y nxy) eqxx.
  + exact: at_empty_alon_tarsi.
  + move=> v; rewrite /at_outdegree (_ : [set w | (v, w) \in set0] = set0) ?cards0 //.
    by apply/setP => w; rewrite !inE.
- by rewrite leq_addl.
- case=> k [hk hat].
  have e : @edge_rel (del_edge_set 'K_2 set0) o20 o21 by rewrite del_edge_setE inE.
  have k2 := g268_at_edge e hat.
  move: (leq_trans hk (leq_add DK2 (leqnn (2 * 1)))) => h.
  by have := leq_trans (leq_mul (leqnn 2) k2) h.
- case=> C h; exists C; split=> //.
  have [M [_ [k [hk hat]]]] := h 'K_1.
  have k1 := @g268_at_vertex (del_edge_set 'K_1 M) k (@Ordinal 1 0 isT) hat.
  have DK1 : Delta 'K_1 = 0 by apply/eqP; rewrite -leqn0; have := g268_Delta_le 'K_1; rewrite card_ord.
  by move: hk; rewrite DK1 add0n leq_mul2l /=; exact: leq_trans k1.
Qed.

(* The statement without the hypothesis that Delta is the maximum degree of G: any D in its place. *)
Definition g268_am_variant : Prop :=
  exists C : nat, forall (D : nat) (G : sgraph), exists M : {set {set G}},
    matching M /\ exists k : nat, 2 * k <= D + 2 * C /\ x268_at_le (del_edge_set G M) k.

Definition g268_am_ntt_claim : Prop :=
  ~ g268_am_variant /\ (g268_am_variant -> alon_tarsi_matching_removal_statement).

Theorem g268_am_not_trivially_true : g268_am_ntt_claim.
Proof.
split; last by case=> C h; exists C => G; exact: h.
case=> C h; have [M [hM [k [hk hat]]]] := h 0 'K_(2 * C).+1.
have := g268_at_lower hat.
rewrite edges_del_edge_set !card_del_edge_set card_ord.
have hMs : M \subset E('K_(2 * C).+1) by apply/subsetP; case: hM.
rewrite cardsD (setIidPr hMs) card_edge_Kn.
have hm := g268_matching_card hM; rewrite card_ord in hm.
have hkC : k <= C by move: hk; rewrite add0n leq_mul2l.
have bin : 'C((2 * C).+1, 2) = (2 * C).+1 * C by rewrite bin2 /= mulnCA mul2n half_double.
have mC : #|M| <= C.
  rewrite -ltnS -(ltn_pmul2l (isT : 0 < 2)); apply: leq_ltn_trans hm _.
  by rewrite mulnS add2n ltnS.
rewrite bin => hX.
have hX2 : (2 * C).+1 * C - #|M| + (2 * C).+1 <= (2 * C).+1 * C.
  by apply: leq_trans hX _; rewrite leq_mul2l hkC orbT.
have mX : #|M| <= (2 * C).+1 * C by apply: leq_trans mC _; exact: leq_pmull.
move: hX2; rewrite -(leq_add2r #|M|) addnAC subnK // leq_add2l => hn.
by move: (leq_trans hn mC); rewrite ltnNge -(leq_pmul2l (isT : 0 < 2)) ?leq_pmull.
Qed.


(** ** arxiv:2202.09118#04: self-isolating graphs ********************************************************** *)

(** ** The guard is satisfiable, and without it the definition fails *)

(* The iterated Mycielski graphs: clique number 4, chromatic number n + 7. *)
Lemma g268_guard_sat (c' d' : nat) : exists G : sgraph, c' * ω([set: G]) ^ d' < χ([set: G]).
Proof.
exists (gap_graph (c' * 4 ^ d')); have [ho [_ hc]] := gap_graph_parameters (c' * 4 ^ d').
by rewrite ho hc addnS ltnS leq_addr.
Qed.

Definition g268_si_hyp_claim : Prop :=
  (forall c' d' : nat, exists G : sgraph, c' * ω([set: G]) ^ d' < χ([set: G])) /\
  (all_graphs_self_isolating_statement ->
     forall (H : sgraph) (c d : nat), exists (G : sgraph) (A : {set G}), c * ω(A) ^ d < χ(A)).

Theorem g268_si_hyp_inhabited : g268_si_hyp_claim.
Proof.
split; first exact: g268_guard_sat.
move=> h H c d; have [c' [d' hc]] := h H c d.
have [G hG] := g268_guard_sat c' d'; have [A [hA _]] := hc G hG.
by exists G, A.
Qed.

(* The statement without the guard chi(G) > c' omega(G)^d'. *)
Definition g268_si_no_guard : Prop :=
  forall (H : sgraph) (c d : nat) (G : sgraph),
    exists A : {set G}, c * ω(A) ^ d < χ(A) /\
      (induced_free (induced A) H \/ exists S : {set G}, inhabited (induced S ≃ H) /\ anticomplete S A).

Definition g268_si_ntt_claim : Prop :=
  ~ g268_si_no_guard /\ (g268_si_no_guard -> all_graphs_self_isolating_statement).

Theorem g268_si_not_trivially_true : g268_si_ntt_claim.
Proof.
split; last by move=> h H c d; exists 0, 0 => G _; exact: h.
move=> h; have [A [hA _]] := h 'K_1 1 0 'K_1.
move: hA; rewrite expn0 muln1 ltnNge; apply/negP/negPn.
by apply: leq_trans (leq_chi A) _; apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.

(** ** K_1 is self-isolating (2202.09118v1, source.tex l.179-200, at k = 1) *)

Lemma g268_chi_col (G : sgraph) (A : {set G}) : exists2 P : {set {set G}}, coloring P A & #|P| = χ(A).
Proof.
rewrite /chi_mem.
have eA : [set x in mem A] = A by apply/setP => x; rewrite inE.
rewrite eA; case: arg_minnP => [|P hP _]; first exact: trivial_coloringP.
by exists P.
Qed.

(* The chromatic number is subadditive under union. *)
Lemma g268_chiU (G : sgraph) (A B : {set G}) : χ(A :|: B) <= χ(A) + χ(B).
Proof.
have [P hP eP] := g268_chi_col A.
have [Q hQ eQ] := g268_chi_col (B :\: A).
have eU : A :|: B = A :|: (B :\: A) by apply/setP => x; rewrite !inE; case: (x \in A); rewrite ?orbT.
move: (hP) (hQ) => /andP[/and3P[cP tP nP] sP] /andP[/and3P[cQ tQ nQ] sQ].
have hPQ : coloring (P :|: Q) (A :|: (B :\: A)).
  apply/andP; split.
  - apply/and3P; split.
    + by rewrite /cover bigcup_setU -!/(cover _) (eqP cP) (eqP cQ).
    + apply: trivIsetU => //; rewrite (eqP cP) (eqP cQ) disjoint_sym.
      by apply/pred0P => x /=; rewrite !inE; case: (x \in A); rewrite ?andbF.
    + by rewrite inE negb_or nP nQ.
  - apply/forall_inP => S; rewrite inE => /orP[hS | hS].
    + exact: (forall_inP sP S hS).
    + exact: (forall_inP sQ S hS).
rewrite eU; apply: leq_trans (color_bound hPQ) _.
apply: leq_trans (leq_card_setU P Q) _.
by rewrite eP eQ leq_add2l sub_chi // subsetDl.
Qed.

(* ... and so is it under a union over a finite index set. *)
Lemma g268_chi_bigcup (G : sgraph) (I : finType) (K : {set I}) (F : I -> {set G}) :
  χ(\bigcup_(i in K) F i) <= \sum_(i in K) χ(F i).
Proof.
elim/big_rec2: _ => [|i U n _ hU]; first by rewrite chi0.
exact: leq_trans (g268_chiU _ _) (leq_add (leqnn _) hU).
Qed.

(* A one-vertex induced subgraph is K_1. *)
Lemma g268_induced1_K1 (G : sgraph) (x : G) : inhabited (induced [set x] ≃ 'K_1).
Proof.
have xx : x \in [set x] by rewrite inE.
pose f : induced [set x] -> 'K_1 := fun _ => ord0.
pose g : 'K_1 -> induced [set x] := fun _ => Sub x xx.
constructor; apply: (@Diso' _ _ f g).
- by move=> [y hy]; apply: val_inj; rewrite /f /g /=; move: hy; rewrite inE => /eqP ->.
- by move=> i; rewrite /f [i]ord1.
- move=> [u hu] [v hv]; rewrite /f /= sg_irrefl /=.
  have eu : u = x by move: (hu); rewrite inE => /eqP.
  have ev : v = x by move: (hv); rewrite inE => /eqP.
  by change (false = (u -- v)); rewrite eu ev sg_irrefl.
Qed.

(* K_1 is self-isolating: with c' = c + 1 and d' = d + 1, a maximum clique K covers V(G) together with the sets
   A_x of non-neighbours of its vertices x, so chi(G) <= |K| + sum_x chi(A_x); some A_x has chi(A_x) > c
   omega(A_x)^d, and {x} is a K_1 anticomplete to it. *)
Lemma g268_K1_self_isolating : x268_self_isolating 'K_1.
Proof.
move=> c d; exists c.+1, d.+1 => G; case: (omegaP [set: G]) => K hK hG.
pose Ax (x : G) : {set G} := [set y | (y != x) && ~~ (x -- y)].
case: (boolP [exists x in K, c * ω(Ax x) ^ d < χ(Ax x)]) => [/exists_inP [x xK hx] | hno].
  exists (Ax x); split=> //; right; exists [set x]; split; first exact: g268_induced1_K1.
  rewrite /anticomplete; apply/andP; split.
    by rewrite disjoints_subset; apply/subsetP => y; rewrite !inE => /eqP ->; rewrite eqxx.
  by apply/neighborNP => a b; rewrite !inE => /eqP -> /andP[_].
exfalso.
have hcov : [set: G] \subset K :|: \bigcup_(x in K) Ax x.
  apply/subsetP => y _; rewrite inE; case yK: (y \in K) => //=.
  case: (boolP [exists x in K, ~~ (x -- y)]) => [/exists_inP [x xK nxy] | hall].
    apply/bigcupP; exists x => //; rewrite inE nxy andbT.
    by apply/eqP => e; rewrite e xK in yK.
  have hsub : K \subset N(y).
    apply/subsetP => z zK; rewrite in_opn sgP.
    by move/exists_inPn: hall => /(_ z zK) /negPn.
  by have := maxclique_opn (in_setT y) hK hsub; rewrite yK.
have hb x : x \in K -> χ(Ax x) <= c * #|K| ^ d.
  move=> xK; move/exists_inPn: hno => /(_ x xK); rewrite -leqNgt => h.
  apply: leq_trans h _; rewrite leq_mul2l; apply/orP; right.
  have ho : ω(Ax x) <= #|K| by rewrite (card_maxclique hK); exact: sub_omega (subsetT _).
  by case: d {hG} => [|d']; rewrite ?expn0 // leq_exp2r.
have h3 : \sum_(x in K) χ(Ax x) <= #|K| * (c * #|K| ^ d).
  by rewrite -sum_nat_const; apply: leq_sum.
have hchi := leq_trans (sub_chi hcov)
  (leq_trans (g268_chiU _ _) (leq_add (leq_chi K) (leq_trans (g268_chi_bigcup K Ax) h3))).
have kk : #|K| <= #|K| ^ d.+1 by case: #|K| => // n; rewrite -{1}(expn1 n.+1) leq_pexp2l.
have := leq_trans hG hchi; rewrite mulnCA -expnS mulSn => h.
by have := leq_trans h (leq_add kk (leqnn _)); rewrite ltnn.
Qed.


(** ** studies:std_plummer_zha_conjecture: the Petersen graph, K_4, P_5, K_3 and C_7 ************************ *)

Local Notation Pg := petersen_ord.
Local Notation O10 i := (@Ordinal 10 i isT).


Definition g268_pv : seq Pg :=
  [:: O10 0; O10 1; O10 2; O10 3; O10 4; O10 5; O10 6; O10 7; O10 8; O10 9].

Lemma g268_pv_all (x : Pg) : x \in g268_pv.
Proof. by case: x => -[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]] Hx //=; apply/eqP. Qed.

Arguments g268_pv : simpl never.

(* Duplicate-free walks with n arcs, built by extension at the end. *)
Fixpoint g268_walks (n : nat) : seq (seq Pg) :=
  match n with
  | 0 => [seq [:: x] | x <- g268_pv]
  | n'.+1 => flatten [seq [seq rcons w y | y <- g268_pv & @edge_rel Pg (last (O10 0) w) y && (y \notin w)]
                     | w <- g268_walks n']
  end.

Lemma g268_walksP (x : Pg) (p : seq Pg) :
  path (--) x p -> uniq (x :: p) -> x :: p \in g268_walks (size p).
Proof.
elim/last_ind: p => [|q y IH].
  move=> _ _; exact: (map_f (fun z : Pg => [:: z]) (g268_pv_all x)).
rewrite rcons_path size_rcons => /andP[hq hy].
rewrite -rcons_cons rcons_uniq => /andP[hny hu].
apply/flatten_mapP; exists (x :: q); first exact: IH.
apply: map_f; rewrite mem_filter g268_pv_all andbT /=.
by rewrite hy hny.
Qed.

(* A duplicate-free cycle is a walk of the enumeration whose last vertex is adjacent to its first. *)
Definition g268_closes (w : seq Pg) : bool := @edge_rel Pg (last (O10 0) w) (head (O10 0) w).

Lemma g268_ucycle_walk (c : seq Pg) :
  ucycle (--) c -> 0 < size c -> c \in g268_walks (size c).-1 /\ g268_closes c.
Proof.
case: c => [|x p] // /andP[hc hu] _; split.
  by move: (hc); rewrite /= rcons_path => /andP[hp _]; exact: g268_walksP hp hu.
by move: hc; rewrite /= rcons_path => /andP[_ h]; rewrite /g268_closes /=.
Qed.

Lemma g268_no_short_cycle :
  all (fun w => ~~ g268_closes w) (g268_walks 2) && all (fun w => ~~ g268_closes w) (g268_walks 3).
Proof. by vm_compute. Qed.

Lemma g268_petersen_girth : girth_geq Pg 5.
Proof.
move=> c hc h2; rewrite leqNgt; apply/negP => h5.
have [hw hcl] := g268_ucycle_walk hc (ltnW (ltnW h2)).
have /andP[h2' h3'] := g268_no_short_cycle.
have : (size c).-1 = 2 \/ (size c).-1 = 3.
  by case: (size c) h2 h5 => [|[|[|[|[|n]]]]] //= _ _; [left | right].
by case=> hs; rewrite hs in hw; [move/allP: h2' | move/allP: h3'] => /(_ c hw); rewrite hcl.
Qed.

Lemma g268_no_hole7 : all (fun w => ~~ (g268_closes w && cyclic_chordlessb w)) (g268_walks 6).
Proof. by vm_compute. Qed.

Lemma g268_no_hole9 : all (fun w => ~~ (g268_closes w && cyclic_chordlessb w)) (g268_walks 8).
Proof. by vm_compute. Qed.

Lemma g268_petersen_odd_chordless (c : seq Pg) : chordless_cycle c -> odd (size c) -> size c = 5.
Proof.
move=> [hc [h2 hch]] hodd.
have [hw hcl] := g268_ucycle_walk hc (ltnW (ltnW h2)).
have hle : size c <= 10.
  by move: hc => /andP[_ /card_uniqP <-]; rewrite (leq_trans (subset_leq_card (subset_predT _))) // card_ord.
have hg := g268_petersen_girth hc h2.
have hch' := introT (cyclic_chordlessP c) hch.
have hs : size c = 5 \/ (size c).-1 = 6 \/ (size c).-1 = 8.
  move: h2 hle hg hodd; case: (size c) => [|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]] //= *; tauto.
case: hs => [// | [] hs]; rewrite hs in hw.
- by move/allP: g268_no_hole7 => /(_ c hw); rewrite hcl hch'.
- by move/allP: g268_no_hole9 => /(_ c hw); rewrite hcl hch'.
Qed.

(* Breadth-first reachability avoiding the vertices of [rem]. *)
Fixpoint g268_reach (rem : seq Pg) (n : nat) (R : seq Pg) : seq Pg :=
  if n is n'.+1 then
    g268_reach rem n'
      (R ++ [seq y <- g268_pv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel Pg x y) R])
  else R.

Lemma g268_reachP (S : {set Pg}) (rem : seq Pg) (r : Pg) :
  (forall y, (y \in S) = (y \in rem)) ->
  forall n R, (forall x, x \in R ->
      x \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: Pg] :\: S)) (--)) r x) ->
  forall y, y \in g268_reach rem n R ->
    y \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: Pg] :\: S)) (--)) r y.
Proof.
move=> hS; elim=> [|n IH] R hR y; first exact: hR.
move=> hy; apply: (IH (R ++ [seq y <- g268_pv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel Pg x y) R])
  _ y hy) => x.
rewrite mem_cat => /orP[/hR // |].
rewrite mem_filter => /andP[/andP[/andP[hx _] /hasP[z hz hzx]] _]; split=> //.
have [hzr hcz] := hR z hz; apply: connect_trans hcz (connect1 _).
by rewrite /preliminaries.restrict_mem /= !inE !hS hzr hx hzx.
Qed.

Definition g268_conn_ok (rem : seq Pg) : bool :=
  let r := head (O10 0) [seq y <- g268_pv | y \notin rem] in
  let L := g268_reach rem 10 [:: r] in
  all (fun y => (y \in rem) || (y \in L)) g268_pv.

Lemma g268_connected_of (S : {set Pg}) (rem : seq Pg) :
  (forall y, (y \in S) = (y \in rem)) -> g268_conn_ok rem -> connected ([set: Pg] :\: S).
Proof.
move=> hS; rewrite /g268_conn_ok; cbv zeta.
case hf: [seq y <- g268_pv | y \notin rem] => [|r f] hall.
  move=> x y hx _; exfalso; move: hx; rewrite !inE hS andbT => hx.
  by have := mem_filter (fun y => y \notin rem) x g268_pv; rewrite hf hx g268_pv_all in_nil.
have hr : r \notin rem by have := mem_head r f; rewrite -hf mem_filter => /andP[].
apply: (@connected_center _ r) => [y|]; last by rewrite !inE hS hr.
rewrite !inE hS andbT => hy.
have hreach : y \in g268_reach rem 10 [:: r].
  by move/allP: hall => /(_ y (g268_pv_all y)); rewrite (negbTE hy) orFb.
have [] // := @g268_reachP S rem r hS 10 [:: r] _ y hreach.
by move=> x; rewrite inE => /eqP ->; split=> //; exact: connect0.
Qed.

Lemma g268_conn_ok2 : all (fun a => all (fun b => g268_conn_ok [:: a; b]) g268_pv) g268_pv && g268_conn_ok [::].
Proof. by vm_compute. Qed.

Lemma g268_conn_ok3 :
  all (fun a => all (fun b => all (fun d =>
    g268_conn_ok [:: a; b; d] ||
    has (fun v => all (fun y => @edge_rel Pg v y == (y \in [:: a; b; d])) g268_pv) g268_pv)
  g268_pv) g268_pv) g268_pv.
Proof. by vm_compute. Qed.

Lemma g268_petersen_3conn : k_connected Pg 3.
Proof.
split; first by rewrite card_ord.
move=> S hS; have [h2 h0] := andP g268_conn_ok2.
have ok2 a b : g268_conn_ok [:: a; b].
  by move/allP: h2 => /(_ a (g268_pv_all a)) /allP /(_ b (g268_pv_all b)).
have : #|S| = 0 \/ #|S| = 1 \/ #|S| = 2 by move: hS; case: #|S| => [|[|[|n]]]; auto.
case=> [/cards0_eq -> | [/eqP/cards1P [a ->] | /eqP/cards2P [a [b [_ ->]]]]].
- by apply: (@g268_connected_of _ [::] _ h0) => y; rewrite !inE.
- by apply: (@g268_connected_of _ [:: a; a] _ (ok2 a a)) => y; rewrite !inE orbb.
- by apply: (@g268_connected_of _ [:: a; b] _ (ok2 a b)) => y; rewrite !inE.
Qed.

Lemma g268_petersen_int4 : x268_internally_four_connected Pg.
Proof.
move=> S h3 hnc.
have [a aS] : exists a, a \in S by apply/set0Pn; rewrite -card_gt0 h3.
have /cards2P [b [d [_ hbd]]] : #|S :\ a| == 2.
  by move: h3; rewrite (cardsD1 a S) aS add1n => -[->].
have hmem y : (y \in S) = (y \in [:: a; b; d]).
  by rewrite -(setD1K aS) hbd !inE.
have := g268_conn_ok3; move/allP => /(_ a (g268_pv_all a)) /allP /(_ b (g268_pv_all b)).
move/allP => /(_ d (g268_pv_all d)) /orP [hok | /hasP [v _ hv]].
  by exfalso; apply: hnc; exact: g268_connected_of hmem hok.
exists v; apply/setP => y; rewrite in_opn hmem.
by move/allP: hv => /(_ y (g268_pv_all y)) /eqP.
Qed.

Lemma g268_petersen_hyp : [/\ k_connected Pg 3, x268_internally_four_connected Pg & x268_pentagraph Pg].
Proof.
split; [exact: g268_petersen_3conn | exact: g268_petersen_int4 |].
by split; [exact: g268_petersen_girth | exact: g268_petersen_odd_chordless].
Qed.

(** ** Complete graphs, paths and cycles *)

(* Every vertex set of a complete graph is connected. *)
Lemma g268_Kn_connected (n : nat) (A : {set 'K_n}) : connected A.
Proof.
move=> x y hx hy; case: (x =P y) => [-> | /eqP ne]; first exact: connect0.
by apply: connect1; rewrite /preliminaries.restrict_mem /= hx hy.
Qed.

Lemma g268_K4_hyp : k_connected 'K_4 3 /\ x268_internally_four_connected 'K_4.
Proof.
split; first by split; [rewrite card_ord | move=> S _; exact: g268_Kn_connected].
by move=> S _ hnc; exfalso; apply: hnc; exact: g268_Kn_connected.
Qed.

Lemma g268_chi_K4 : χ([set: 'K_4]) = 4.
Proof. by rewrite chi_clique ?cardsT ?card_ord // => x y _ _. Qed.

Local Notation o5 i := (@Ordinal 5 i isT).

(* P_5 is not internally 4-connected: deleting {0, 2, 4} separates 1 from 3, and no vertex has three
   neighbours. *)
Lemma g268_P5_not_i4 : ~ x268_internally_four_connected (ordinal_path 5).
Proof.
move=> h; have [] := h [set o5 0; o5 2; o5 4].
- by rewrite -setUA cardsU1 cards2 !inE.
- move/(_ (o5 1) (o5 3)); rewrite !inE => /(_ isT isT) /connectP [[|z p] hp e] //.
  clear e; move: hp => /andP[hz _]; move: hz; rewrite /preliminaries.restrict_mem /= !inE.
  by case: z => -[|[|[|[|[|?]]]]] ? //=.
- move=> v hv; have hD : #|N(v)| <= Delta (ordinal_path 5) by exact: (leq_bigmax v).
  by move: (leq_trans hD (ordinal_path_Delta 5)); rewrite hv -setUA cardsU1 cards2 !inE.
Qed.

Local Notation o3 i := (@Ordinal 3 i isT).
Local Notation o7 i := (@Ordinal 7 i isT).

(* K_3 has a 3-cycle, and C_7 is itself a chordless 7-cycle. *)
Lemma g268_K3_not_pentagraph : ~ x268_pentagraph 'K_3.
Proof. by case=> hg _; have := hg [:: o3 0; o3 1; o3 2] isT isT. Qed.

Lemma g268_C7_not_pentagraph : ~ x268_pentagraph (cycle_graph 7).
Proof.
pose c : seq (cycle_graph 7) := [:: o7 0; o7 1; o7 2; o7 3; o7 4; o7 5; o7 6].
case=> _ h; have hc : chordless_cycle c by apply/chordless_cycleP; vm_compute.
by have := h _ hc isT.
Qed.

(** ** The certificates of studies:std_plummer_zha_conjecture and the helper sanity groups ***************** *)

Definition g268_pz_hyp_claim : Prop :=
  [/\ k_connected petersen_ord 3, x268_internally_four_connected petersen_ord, x268_pentagraph petersen_ord &
      (plummer_zha_pentagraph_three_colourable_statement -> χ([set: petersen_ord]) <= 3)].

Theorem g268_pz_hyp_inhabited : g268_pz_hyp_claim.
Proof. by have [h3 h4 h5] := g268_petersen_hyp; split=> // h; exact: h _ h3 h4 h5. Qed.

(* The statement without its pentagraph hypothesis. *)
Definition g268_pz_no_pentagraph : Prop :=
  forall G : sgraph, k_connected G 3 -> x268_internally_four_connected G -> χ([set: G]) <= 3.

Definition g268_pz_ntt_claim : Prop :=
  ~ g268_pz_no_pentagraph /\ (g268_pz_no_pentagraph -> plummer_zha_pentagraph_three_colourable_statement).

Theorem g268_pz_not_trivially_true : g268_pz_ntt_claim.
Proof.
split; last by move=> h G h3 h4 _; exact: h.
by move=> h; have [h3 h4] := g268_K4_hyp; move: (h _ h3 h4); rewrite g268_chi_K4.
Qed.

Definition g268_at_helper_claim : Prop := x268_at_le 'K_2 2 /\ ~ x268_at_le 'K_2 1.

Theorem g268_at_helper_sanity : g268_at_helper_claim.
Proof. exact: (conj g268_at_K2 g268_at_K2_not1). Qed.

Definition g268_si_helper_claim : Prop := x268_self_isolating 'K_1.

Theorem g268_si_helper_sanity : g268_si_helper_claim.
Proof. exact: g268_K1_self_isolating. Qed.

Definition g268_i4_helper_claim : Prop :=
  [/\ x268_internally_four_connected petersen_ord, x268_internally_four_connected 'K_4 &
      ~ x268_internally_four_connected (ordinal_path 5)].

Theorem g268_i4_helper_sanity : g268_i4_helper_claim.
Proof. by split; [exact: g268_petersen_int4 | case: g268_K4_hyp | exact: g268_P5_not_i4]. Qed.

Definition g268_pg_helper_claim : Prop :=
  [/\ x268_pentagraph petersen_ord, ~ x268_pentagraph 'K_3 & ~ x268_pentagraph (cycle_graph 7)].

Theorem g268_pg_helper_sanity : g268_pg_helper_claim.
Proof.
split; [split | exact: g268_K3_not_pentagraph | exact: g268_C7_not_pentagraph].
- exact: g268_petersen_girth.
- exact: g268_petersen_odd_chordless.
Qed.
