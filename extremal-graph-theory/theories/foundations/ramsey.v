(** * Extremal.foundations.ramsey — clique / stable-set witnesses and the
    Erdős–Szekeres bound in Erdős–Hajnal shape.

    Reusable ingredients of the "multicolour Erdős–Hajnal implies Erdős–Hajnal"
    reduction (corpus edge e115) and of the VC-dimension specialisation (e116):

    - [clique_witness] / [stable_witness]: a set realising ω / α, needed whenever a
      statement asks for an explicit clique or stable SET rather than the numeric
      invariants.
    - [card_bigcup_leq]: the union bound on cardinals (mathcomp-analysis has it as
      [card_big_setU], but that lives in the axiom-bearing classical layer, so it
      is reproved here).
    - [omega_leq1_stable]: ω(A) <= 1 means A is stable.
    - [ramsey_card_leq]: the Erdős–Szekeres bound in the form
      [ω(A) <= k -> #|A| <= (α(A) + 1) ^ k], i.e. a graph with no clique of size
      k+1 on n vertices has a stable set of size ~ n^(1/k).  This is the
      OFF-DIAGONAL Ramsey bound; the diagonal bound R(k,k) <= 4^k is useless for
      Erdős–Hajnal (it only gives a logarithmic-size clique/stable set, whereas
      Erdős–Hajnal needs a polynomial one).
    - [ramsey_eh_bound]: its Erdős–Hajnal packaging
      [#|G| <= (maxn ω α) ^ (2 * k)] for non-empty G with ω <= k. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Witnesses for the clique and independence numbers *)

Lemma clique_witness (G : sgraph) (A : {set G}) :
  exists S : {set G}, [&& S \subset A, cliqueb S & ω(A) <= #|S|].
Proof.
case: omegaP => K; rewrite !inE -andbA => /and3P[subK clK _].
by exists K; rewrite subK clK leqnn.
Qed.

Lemma stable_witness (G : sgraph) (A : {set G}) :
  exists S : {set G}, [&& S \subset A, stable S & α(A) <= #|S|].
Proof.
case: alphaP => K; rewrite !inE -andbA => /and3P[subK stK _].
by exists K; rewrite subK stK leqnn.
Qed.

(** ** The union bound on cardinals *)

Lemma card_bigcup_leq (I T : finType) (P : {pred I}) (F : I -> {set T}) :
  #|\bigcup_(i | P i) F i| <= \sum_(i | P i) #|F i|.
Proof.
elim/big_ind2 : _ => // [|m A n B Am Bn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU _ _)) // leq_add.
Qed.

(** ** Monotonicity of alpha and the ω <= 1 degeneracy *)

Lemma sub_alpha (G : sgraph) (A B : {set G}) : A \subset B -> α(A) <= α(B).
Proof.
move=> subAB; case: alphaP => S; rewrite !inE -andbA => /and3P[subSA stS _].
by apply: stabset_bound; rewrite inE (subset_trans subSA subAB) stS.
Qed.

Lemma omega_leq1_stable (G : sgraph) (A : {set G}) : ω(A) <= 1 -> stable A.
Proof.
move=> oA; apply/stableP => x y xA yA; apply/negP => xy.
have xNy : x != y by apply: contraTneq xy => ->; rewrite sg_irrefl.
have card2 : #|[set x; y]| = 2 by rewrite cards2 xNy.
have H2 : 1 < ω(A).
  rewrite -card2; apply: clique_bound; rewrite inE subUset !sub1set xA yA /=.
  apply/cliqueP => u v; rewrite !inE.
  move=> /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->] ne //.
  - by rewrite eqxx in ne.
  - by rewrite sg_sym.
  - by rewrite eqxx in ne.
by move: oA; rewrite leqNgt H2.
Qed.

(** ** Erdős–Szekeres: no clique of size k+1 forces a stable set of size ~ n^(1/k)

    [#|A| <= (α(A) + 1) ^ k] whenever [ω(A) <= k].  Proof by induction on k: a
    MAXIMUM stable set S inside A dominates A (a vertex of A with no neighbour in
    S would enlarge S), so A is covered by the #|S| = α(A) closed neighbourhoods
    [N[s] :&: A]; each [N(s) :&: A] has clique number at most k-1 (a clique
    inside it plus s is a clique of A), so the induction hypothesis bounds it by
    [(α(A)+1)^(k-1)], and
    [α * ((α+1)^(k-1) + 1) <= (α+1)^k] because [α <= (α+1)^(k-1)]. *)
Lemma ramsey_card_leq (G : sgraph) (k : nat) :
  forall A : {set G}, ω(A) <= k -> #|A| <= (α(A) + 1) ^ k.
Proof.
elim: k => [|k IHk] A oA.
  have /eqP -> : A == set0 by rewrite -omega_eq0 -leqn0.
  by rewrite cards0.
case: k IHk oA => [_ oA|k IHk oA].
  rewrite expn1; apply: leq_trans (leq_addr 1 (α(A))).
  by apply: stabset_bound; rewrite inE subxx /= (omega_leq1_stable oA).
have [S /and3P[subS stS aS]] := stable_witness A.
have cardS : #|S| = α(A).
  by apply/eqP; rewrite eqn_leq aS andbT; apply: stabset_bound; rewrite inE subS stS.
have cover : A \subset \bigcup_(s in S) (N[s] :&: A).
  apply/subsetP => v vA; apply/bigcupP.
  have [/existsP[s /andP[sS vNs]]|Hno] :=
    boolP [exists s, (s \in S) && (v \in N[s])].
    by exists s => //; rewrite inE vNs vA.
  have vnS : v \notin S.
    apply: contraNN Hno => vS; apply/existsP; exists v.
    by rewrite vS v_in_clneigh.
  have stvS : stable (v |: S).
    apply/stableP => x y; rewrite !inE.
    move=> /predU1P[->|xS] /predU1P[->|yS].
    - by rewrite sg_irrefl.
    - apply/negP => vy; apply: (negP Hno); apply/existsP; exists y.
      have yv : y -- v by rewrite sg_sym.
      by rewrite yS in_cln /dominates yv orbT.
    - apply/negP => xv; apply: (negP Hno); apply/existsP; exists x.
      by rewrite xS in_cln /dominates xv orbT.
    - by move/stableP: stS; apply.
  have hc : #|v |: S| <= α(A).
    by apply: stabset_bound; rewrite inE stvS andbT subUset sub1set vA subS.
  by move: hc; rewrite cardsU1 vnS add1n cardS ltnn.
have term : forall s, s \in S -> #|N[s] :&: A| <= (α(A) + 1) ^ (k.+1) + 1.
  move=> s sS.
  have sA : s \in A by apply: (subsetP subS).
  have sub1 : N[s] :&: A \subset s |: (N(s) :&: A).
    apply/subsetP => v; rewrite inE in_cln /dominates !inE.
    move=> /andP[/orP[/eqP <-|vNs] vA]; first by rewrite eqxx.
    by rewrite vNs vA orbT.
  have h1 : #|N[s] :&: A| <= #|N(s) :&: A| + 1.
    apply: leq_trans (subset_leq_card sub1) _.
    by rewrite cardsU1 addnC leq_add2l leq_b1.
  apply: leq_trans h1 _; rewrite leq_add2r.
  have oNs : ω(N(s) :&: A) <= k.+1.
    have [K /and3P[subK clK oK]] := clique_witness (N(s) :&: A).
    have subKN : K \subset N(s) by apply: subset_trans subK _; exact: subsetIl.
    have subKA : K \subset A by apply: subset_trans subK _; exact: subsetIr.
    have snK : s \notin K.
      by apply/negP => sK; move: (subsetP subKN _ sK); rewrite inE sg_irrefl.
    have hcl : #|s |: K| <= ω(A).
      apply: clique_bound; rewrite inE subUset sub1set sA subKA /=.
      by apply/cliqueP; apply: cliqueU1 => //; apply/cliqueP.
    move: hcl; rewrite cardsU1 snK add1n => hcl.
    apply: leq_trans oK _; rewrite -ltnS.
    exact: leq_trans hcl oA.
  apply: leq_trans (IHk _ oNs) _.
  by rewrite leq_exp2r // leq_add2r sub_alpha // subsetIr.
have tE : α(A) <= (α(A) + 1) ^ (k.+1).
  apply: leq_trans (leq_pexp2l (_ : 0 < α(A) + 1) (_ : 1 <= k.+1)) => //.
  by rewrite expn1 leq_addr.
  by rewrite addn1.
have key : #|A| <= \sum_(s in S) #|N[s] :&: A|.
  by apply: leq_trans (subset_leq_card cover) _; exact: card_bigcup_leq.
apply: leq_trans key _.
have step : \sum_(s in S) #|N[s] :&: A|
            <= \sum_(s in S) ((α(A) + 1) ^ (k.+1) + 1).
  by apply: leq_sum => s sS; exact: term s sS.
apply: leq_trans step _; rewrite sum_nat_const cardS.
have arith : α(A) * ((α(A) + 1) ^ (k.+1) + 1)
             <= (α(A) + 1) * (α(A) + 1) ^ (k.+1).
  by rewrite mulnDr muln1 mulnDl mul1n leq_add2l.
by apply: leq_trans arith _; rewrite -expnS.
Qed.

(** The Erdős–Hajnal packaging: for a non-empty graph with no clique of size
    k+1, [#|G| <= (maxn ω α) ^ (2 * k)].  The factor 2 absorbs the "+1" of
    [ramsey_card_leq] ([M + 1 <= M ^ 2] as soon as [2 <= M]); the degenerate
    [maxn ω α = 1] case is a one-vertex graph. *)
Lemma ramsey_eh_bound (G : sgraph) (k : nat) :
  0 < #|G| -> ω([set: G]) <= k ->
  #|G| <= (maxn ω([set: G]) α([set: G])) ^ (2 * k).
Proof.
move=> G0 oG.
have o1 : 0 < ω([set: G]) by rewrite lt0n omega_eq0 -cards_eq0 -lt0n cardsT.
have k1 : 0 < k by apply: leq_trans o1 oG.
have Hr := ramsey_card_leq oG.
set M := maxn ω([set: G]) α([set: G]).
have M1 : 0 < M by rewrite leq_max o1.
case: (ltnP 1 M) => [M2|M1'].
  have h2M : M + 1 <= 2 * M by rewrite mul2n -addnn leq_add2l.
  have hMM : 2 * M <= M * M by rewrite leq_mul2r M2 orbT.
  have hM2 : M + 1 <= M ^ 2 by rewrite (expnS M 1) expn1; exact: leq_trans h2M hMM.
  have hA : α([set: G]) + 1 <= M + 1 by rewrite leq_add2r leq_maxr.
  rewrite -cardsT; apply: leq_trans Hr _; rewrite expnM leq_exp2r //.
  exact: leq_trans hA hM2.
have oM : ω([set: G]) <= 1 by apply: leq_trans (leq_maxl _ _) M1'.
have aM : α([set: G]) <= 1 by apply: leq_trans (leq_maxr _ _) M1'.
have hG0 : #|[set: G]| <= α([set: G]).
  by apply: stabset_bound; rewrite inE subxx /= (omega_leq1_stable oM).
rewrite cardsT in hG0.
have M1e : M = 1 by apply/eqP; rewrite eqn_leq M1' M1.
by rewrite M1e exp1n; apply: leq_trans hG0 aM.
Qed.

(** [alpha_compl] is ABORTED in coq-graph-theory's coloring.v (only its
    [omega_compl] companion is proved), so it is established here: stable sets of
    the complement are exactly the cliques ([stable_compl]), hence the two
    [\max] indices agree. *)
Lemma alpha_compl (G : sgraph) (A : {set G}) : α(A : {set compl G}) = ω(A).
Proof. by apply: eq_bigl => B; rewrite !inE stable_compl. Qed.

(** The complementary form: no STABLE set of size k+1 forces the same bound
    (apply the previous one to the complement, where ω and α swap). *)
Lemma ramsey_eh_bound_alpha (G : sgraph) (k : nat) :
  0 < #|G| -> α([set: G]) <= k ->
  #|G| <= (maxn ω([set: G]) α([set: G])) ^ (2 * k).
Proof.
move=> G0 aG.
have oC : ω([set: compl G]) <= k by rewrite omega_compl.
have := ramsey_eh_bound (G := compl G) G0 oC.
by rewrite omega_compl alpha_compl maxnC.
Qed.

(** ** Induced copies inside a clique / a stable set

    If [H] is complete on at most [#|K|] vertices and [K] is a clique of [G],
    then [H] embeds into [K] as an INDUCED subgraph (both graphs have all their
    distinct pairs adjacent); dually for edgeless [H] inside a stable set.  The
    embedding is [enum_val o widen_ord o enum_rank]. *)
Lemma isubgraph_of_clique (H G : sgraph) (K : {set G}) :
  (forall x y : H, x != y -> x -- y) -> cliqueb K -> #|H| <= #|K| -> H ⇀ G.
Proof.
move=> Hcompl /cliqueP clK le.
pose f (v : H) : G := enum_val (widen_ord le (enum_rank v)).
have fK : forall v, f v \in K by move=> v; exact: enum_valP.
have wo_inj : injective (widen_ord le).
  by move=> i j /(congr1 (@nat_of_ord _)) /= ij; apply/val_inj.
have f_inj : injective f by move=> x y /enum_val_inj/wo_inj/enum_rank_inj.
apply: (ISubgraph f_inj) => x y.
have [->|xy] := eqVneq x y; first by rewrite !sg_irrefl.
have fxy : f x != f y by apply: contraNN xy => /eqP/f_inj ->.
by rewrite (Hcompl _ _ xy) (clK _ _ (fK x) (fK y) fxy).
Qed.

Lemma isubgraph_of_stable (H G : sgraph) (K : {set G}) :
  (forall x y : H, ~~ (x -- y)) -> stable K -> #|H| <= #|K| -> H ⇀ G.
Proof.
move=> Hempty /stableP stK le.
pose f (v : H) : G := enum_val (widen_ord le (enum_rank v)).
have fK : forall v, f v \in K by move=> v; exact: enum_valP.
have wo_inj : injective (widen_ord le).
  by move=> i j /(congr1 (@nat_of_ord _)) /= ij; apply/val_inj.
have f_inj : injective f by move=> x y /enum_val_inj/wo_inj/enum_rank_inj.
apply: (ISubgraph f_inj) => x y.
by rewrite (negbTE (Hempty x y)) (negbTE (stK _ _ (fK x) (fK y))).
Qed.
