(** * Extremal.conjectures.implications_D2ram — relative implication/refutation
    edges among milestone D2ram's five open-problem nodes.

    Each *scheduled* edge is a Qed-closed RELATIVE theorem
    [Theorem <A>_implies_<B> : A_statement -> B_statement] provable WITHOUT
    resolving either endpoint, restricted to the plan §6 verified-literature set
    (the Qed gate is the safeguard; a false edge must fail to compile, and a
    candidate whose exact endpoints do not match is NOT forced — policy §6 / R4).

    ── RESULT FOR D2ram: ONE VERIFIED edge — (1) multicolour EH => (5) EH. ──

    D2ram's five nodes (carriers in brackets):

      (1) multicolour_erdos_hajnal_statement
            [symmetric edge-colourings col : 'I_n -> 'I_n -> 'I_m of K_n, with a
             fixed m-colour pattern chi : 'I_k -> 'I_k -> 'I_m using all m colours]
            — every K_n-colouring has a chi-coloured K_k OR an n^eps set spanning
              <= m-1 colours.
      (2) complete_bipartite_subgraphs_of_perfect_graphs_statement
            [sgraph G and its complement compl G]
            — every perfect G on n vertices: G or G-bar has a complete bipartite
              subgraph with both parts >= n^{1-o(1)}.
      (3) chromatic_number_of_common_graphs_statement
            [sgraph H; 2-edge-colourings rel 'I_n of K_n]
            — common graphs have bounded chromatic number.
      (4) ramsey_properties_of_cayley_graphs_statement
            [finite abelian group gT; connection set S : {set gT}]
            — a fixed c: every abelian gT has a symmetric S whose Cayley graph
              has neither clique nor independent set of size > c*log|gT|.
      (5) the_erdos_hajnal_statement
            [sgraph H (forbidden) and sgraph G (host)]
            — every fixed H: every H-induced-free G has a clique or an independent
              set of size |V(G)|^{delta(H)}.

    §6 verified-literature edge table: contains NO edge with any D2ram node as an
    endpoint (its edges are chromatic/cycle/flow/directed: Petersen-colouring,
    Berge–Fulkerson, CDC, 4-flow<=>3-edge-colouring). No forbidden/withdrawn edge
    (Reed=>B-K, list-total=>Behzad, list-Hadwiger=>Hadwiger, CH=>Seymour-2nd-nbhd)
    touches D2ram either. The one edge closed here comes from the CORPUS relation
    table instead (gc:e115, (1) => (5)); it is Qed-closed below.

    ── The one genuine mathematical link: (1) generalises (5). ──

    The multicolour Erdős–Hajnal conjecture (1) is the natural Ramsey-coloured
    generalisation of the Erdős–Hajnal conjecture (5): with m = 2 colours, a
    graph G is the 2-edge-colouring of K_{|V(G)|} that paints {x,y} colour 1 when
    [x -- y] and colour 0 otherwise; a 2-colour pattern chi is then a graph H on k
    vertices.  Under that dictionary:
      • [contains_pattern chi col]  <->  G contains an INDUCED copy of H
        ([has_induced_copy H G]);  so the host being H-induced-free kills the
        first disjunct of (1);
      • the surviving disjunct gives a set A with [n^a <= #|A|^b] and
        [#|palette_on col A| <= m - 1 = 1]: a single colour inside A, i.e. A is a
        CLIQUE (colour 1) or an INDEPENDENT set (colour 0), hence
        [#|A| <= maxn ω(G) α(G)];
      • monotonicity of [_ ^ b] then yields [#|G|^a <= (maxn ω α)^b], and
        [b' := maxn a b] repairs the [a <= b] guard of (5) (using ω(G) >= 1 for a
        nonempty G).
    This is exactly the textbook "multicolour EH ⊇ EH" reduction.

    ── The base cases the dictionary does NOT cover, and how they are closed. ──

    The reduction is blocked at (1)'s [uses_all_colours chi] hypothesis. With the
    forced m = 2, [uses_all_colours] demands chi use BOTH colours, i.e. the
    forbidden graph H has at least one edge AND at least one non-edge.  (5)
    quantifies over EVERY H, including:
      • H complete (all edges) — chi is monochromatically 1, [uses_all_colours]
        FAILS, so (1) cannot be instantiated; H-induced-freeness then says only
        that G has no clique on |V(H)| vertices;
      • H edgeless on >= 2 vertices — chi is monochromatically 0, same failure;
        H-induced-freeness says G has no stable set on |V(H)| vertices;
      • H with at most one vertex — then EVERY non-empty G contains an induced
        copy of H, so the row's hypothesis is contradictory and the bound is free.
    These monochromatic base cases are exactly a RAMSEY statement, and it is now
    formalised in the repository (Extremal.foundations.ramsey):
    [ramsey_card_leq] proves the Erdős–Szekeres bound
    [ω(A) <= k -> #|A| <= (α(A) + 1) ^ k], packaged as
    [ramsey_eh_bound]/[ramsey_eh_bound_alpha]:
    [#|G| <= (maxn ω α) ^ (2 * k)] for a non-empty G with no clique
    (resp. no stable set) on k+1 vertices.  NB the DIAGONAL bound R(k,k) <= 4^k
    is useless here: it yields a clique/stable set of size ~log n, while
    Erdős–Hajnal needs a POLYNOMIAL one; the off-diagonal form above is what the
    two base cases require.  With those lemmas the edge closes under Qed and is
    recorded as VERIFIED below.

    The REVERSE direction (5) => (1) is not scheduled either: (5) is the 2-state
    (edge/non-edge) graph instance, strictly weaker than the m-colour conjecture
    (1), so it cannot entail (1); recorded in prose only (no annotation), since it
    is "not derivable" rather than a withdrawn/false claim.

    All remaining pairs are independent in both directions over heterogeneous
    carriers: (2) perfect-graph bipartite structure, (3) bounded χ of common
    graphs, and (4) Cayley-graph Ramsey existence over abelian groups share no
    logical shape with one another or with (1)/(5); no map turns one into another.

    This file imports the five node statements to confirm they are in scope and
    that this module compiles axiom-free. *)

From mathcomp Require Import all_boot all_fingroup.
From GTBase Require Import base.
From Extremal.foundations Require Import ramsey.
From Extremal Require Import conjectures.D2ram.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The m = 2 dictionary: graphs as 2-edge-colourings of K_n.

    [b2o] sends a boolean to a colour of ['I_2] (injectively, and every colour is
    hit: [b2o_cases]).  A graph [H] on [k = #|H|] vertices becomes the pattern
    [chi i j = b2o (enum_val i -- enum_val j)] on ['I_k], and a host [G] becomes
    the colouring [gcol x y = b2o (enum_val x -- enum_val y)] of [K_#|G|].  Under
    that dictionary [contains_pattern chi gcol] is exactly "G has an induced copy
    of H" ([contains_pattern_isubgraph]), and a set of vertices spanning at most
    [m - 1 = 1] colour is exactly a clique or a stable set
    ([palette_clique_or_stable]). *)

Definition b2o (b : bool) : 'I_2 :=
  if b then Ordinal (isT : 1 < 2) else Ordinal (isT : 0 < 2).

Lemma b2o_inj : injective b2o.
Proof. by move=> [] [] // /(congr1 (@nat_of_ord 2)). Qed.

Lemma b2o_cases (c : 'I_2) : c = b2o false \/ c = b2o true.
Proof.
case: c => [[|[|m]] Hm] //; first by left; apply/val_inj.
by right; apply/val_inj.
Qed.

Definition chi (H : sgraph) (i j : 'I_#|H|) : 'I_2 := b2o (enum_val i -- enum_val j).

Lemma chi_sym (H : sgraph) (i j : 'I_#|H|) : chi i j = chi j i.
Proof. by rewrite /chi sg_sym. Qed.

Lemma chi_rank (H : sgraph) (x y : H) :
  chi (enum_rank x) (enum_rank y) = b2o (x -- y).
Proof. by rewrite /chi !enum_rankK. Qed.

Definition gcol (G : sgraph) (x y : 'I_#|G|) : 'I_2 := b2o (enum_val x -- enum_val y).

Lemma gcol_sym (G : sgraph) (x y : 'I_#|G|) : gcol x y = gcol y x.
Proof. by rewrite /gcol sg_sym. Qed.

Lemma contains_pattern_isubgraph (H G : sgraph) :
  contains_pattern (@chi H) (@gcol G) -> has_induced_copy H G.
Proof.
case=> g [g_inj Hg]; apply: inhabits.
pose f (v : H) : G := enum_val (g (enum_rank v)).
have f_inj : injective f by move=> x y /enum_val_inj/g_inj/enum_rank_inj.
apply: (ISubgraph f_inj) => x y.
have [->|xy] := eqVneq x y; first by rewrite !sg_irrefl.
have rxy : enum_rank x != enum_rank y by apply: contraNN xy => /eqP/enum_rank_inj ->.
apply: b2o_inj.
have -> : b2o (f x -- f y) = gcol (g (enum_rank x)) (g (enum_rank y)) by [].
by rewrite (Hg _ _ rxy) chi_rank.
Qed.

Lemma palette_clique_or_stable (G : sgraph) (A : {set 'I_#|G|}) :
  #|palette_on (@gcol G) A| <= 1 ->
  cliqueb (enum_val @: A) || stable (enum_val @: A).
Proof.
move=> Hpal.
have memP : forall x y : 'I_#|G|, x \in A -> y \in A -> x != y ->
    gcol x y \in palette_on (@gcol G) A.
  move=> x y xA yA xy; rewrite inE.
  by apply/existsP; exists x; apply/existsP; exists y; rewrite xA yA xy eqxx.
have Huniq : forall c1 c2, c1 \in palette_on (@gcol G) A ->
    c2 \in palette_on (@gcol G) A -> c1 = c2.
  move=> c1 c2 h1 h2; apply/eqP; apply/negPn/negP => ne.
  have sub2 : [set c1; c2] \subset palette_on (@gcol G) A.
    by rewrite subUset !sub1set h1 h2.
  have h2c := subset_leq_card sub2.
  rewrite cards2 ne /= in h2c.
  by move: Hpal; rewrite leqNgt h2c.
case: (boolP [exists x, exists y,
        [&& x \in A, y \in A, x != y & gcol x y == b2o true]]) => [Hex|Hno].
  case/existsP: Hex => x0 /existsP[y0 /and4P[x0A y0A x0y0 /eqP Hc0]].
  apply/orP; left; apply/cliqueP => u v /imsetP[x xA ->] /imsetP[y yA ->] ne.
  have xy : x != y by apply: contraNN ne => /eqP ->.
  have Hgc : gcol x y = b2o true by rewrite -Hc0; apply: Huniq; apply: memP.
  by move: Hgc; rewrite /gcol => /b2o_inj ->.
apply/orP; right; apply/stableP => u v /imsetP[x xA ->] /imsetP[y yA ->].
have [->|xy] := eqVneq x y; first by rewrite sg_irrefl.
move: Hno; rewrite negb_exists => /forallP/(_ x).
rewrite negb_exists => /forallP/(_ y).
rewrite xA yA xy /= => Hnc.
by apply: contraNN Hnc => adj; rewrite /gcol adj eqxx.
Qed.

(** ** e115 — multicolour Erdős–Hajnal implies Erdős–Hajnal.

    Three cases on the forbidden graph H (see the module header):
    - [#|H| <= 1]: every non-empty G contains an induced copy of H (a single
      vertex is a clique), so the row's hypothesis is contradictory.
    - H complete / H edgeless: [uses_all_colours] fails for m = 2, so the source
      is unusable; H-induced-freeness bounds ω (resp. α) by [#|H| - 1] and the
      Erdős–Szekeres bound [ramsey_eh_bound] (resp. [ramsey_eh_bound_alpha]) of
      Extremal.foundations.ramsey gives the conclusion with a = 1 and
      b = 2 * (#|H| - 1).
    - otherwise H has an edge and a non-edge, so [chi] uses both colours and the
      source applies at k = #|H|, m = 2: the first disjunct contradicts
      H-induced-freeness, and the second gives a set A with
      [#|G| ^ a <= #|A| ^ b] spanning at most one colour, i.e. a clique or a
      stable set of the same size, whence
      [#|G| ^ a <= (maxn ω α) ^ b <= (maxn ω α) ^ (maxn a b)]; the exponent pair
      [(a, maxn a b)] repairs the [a <= b] guard of the target (using
      [0 < maxn ω α] for a non-empty G). *)
Theorem multicolour_erdos_hajnal_implies_the_erdos_hajnal :
  multicolour_erdos_hajnal_statement -> the_erdos_hajnal_statement.
Proof.
move=> MEH H.
have [Hsmall|Hbig] := leqP #|H| 1.
  have Hall : forall x y : H, x = y.
    move=> x y; apply/eqP; apply/negPn/negP => ne.
    have h2 := subset_leq_card (subsetT [set x; y]).
    rewrite cards2 ne /= cardsT in h2.
    by move: Hsmall; rewrite leqNgt h2.
  exists 1, 1; split => //; split => // G G0 Hfree.
  exfalso; apply: Hfree.
  have /card_gt0P[v _] := G0.
  apply: inhabits; apply: (@isubgraph_of_clique H G [set v]).
  - by move=> x y xy; move: xy; rewrite (Hall x y) eqxx.
  - by apply/cliqueP; exact: clique1.
  - by rewrite cards1.
have H0 : 0 < #|H| := ltnW Hbig.
have [Hcompl|Hncompl] := boolP [forall x : H, forall y : H, (x != y) ==> (x -- y)].
  exists 1, (2 * (#|H|).-1); split => //; split.
    by rewrite muln_gt0 /= -subn1 subn_gt0.
  move=> G G0 Hfree.
  have Hc : forall x y : H, x != y -> x -- y.
    by move=> x y; apply/implyP; move/forallP/(_ x)/forallP/(_ y): Hcompl.
  have oG : ω([set: G]) < #|H|.
    rewrite ltnNge; apply/negP => Hge.
    have [K /and3P[_ clK oK]] := clique_witness [set: G].
    apply: Hfree; apply: inhabits.
    exact: (isubgraph_of_clique Hc clK (leq_trans Hge oK)).
  have oG' : ω([set: G]) <= (#|H|).-1 by rewrite -ltnS prednK.
  by rewrite expn1; exact: ramsey_eh_bound G0 oG'.
have [Hemp|Hnemp] := boolP [forall x : H, forall y : H, ~~ (x -- y)].
  exists 1, (2 * (#|H|).-1); split => //; split.
    by rewrite muln_gt0 /= -subn1 subn_gt0.
  move=> G G0 Hfree.
  have He : forall x y : H, ~~ (x -- y).
    by move=> x y; move/forallP/(_ x)/forallP/(_ y): Hemp.
  have aG : α([set: G]) < #|H|.
    rewrite ltnNge; apply/negP => Hge.
    have [K /and3P[_ stK aK]] := stable_witness [set: G].
    apply: Hfree; apply: inhabits.
    exact: (isubgraph_of_stable He stK (leq_trans Hge aK)).
  have aG' : α([set: G]) <= (#|H|).-1 by rewrite -ltnS prednK.
  by rewrite expn1; exact: ramsey_eh_bound_alpha G0 aG'.
have [x1 [y1 Hxy1]] : exists x y : H, x -- y.
  move: Hnemp; rewrite negb_forall => /existsP[x]; rewrite negb_forall => /existsP[y].
  by rewrite negbK => xy; exists x, y.
have [x0 [y0 [Hne0 Hnadj0]]] : exists x y : H, x != y /\ ~~ (x -- y).
  move: Hncompl; rewrite negb_forall => /existsP[x]; rewrite negb_forall => /existsP[y].
  by rewrite negb_imply => /andP[xy nadj]; exists x, y.
have chi_all : uses_all_colours (@chi H).
  move=> c; case: (b2o_cases c) => ->.
  - exists (enum_rank x0), (enum_rank y0); split.
      by apply: contraNN Hne0 => /eqP/enum_rank_inj/eqP.
    by rewrite chi_rank (negbTE Hnadj0).
  - exists (enum_rank x1), (enum_rank y1); split.
      apply: contraNN (_ : x1 != y1) => [/eqP/enum_rank_inj/eqP //|].
      by apply: contraTneq Hxy1 => ->; rewrite sg_irrefl.
    by rewrite chi_rank Hxy1.
have [a [b [a0 [b0 Hcore]]]] := MEH #|H| 2 (@chi H) Hbig isT (@chi_sym H) chi_all.
exists a, (maxn a b); split => //; split; first exact: leq_maxl.
move=> G G0 Hfree.
have [Hcp|[A [Acard Apal]]] := Hcore #|G| (@gcol G) (@gcol_sym G).
  by case: (Hfree (contains_pattern_isubgraph Hcp)).
have Hcs := palette_clique_or_stable (G:=G) Apal.
set S := enum_val @: A.
have cardS : #|S| = #|A| by rewrite /S card_imset //; exact: enum_val_inj.
have SM : #|S| <= maxn ω([set: G]) α([set: G]).
  case/orP: Hcs => [clS|stS].
    by apply: leq_trans (leq_maxl _ _); apply: clique_bound; rewrite inE subsetT clS.
  by apply: leq_trans (leq_maxr _ _); apply: stabset_bound; rewrite inE subsetT stS.
have o1 : 0 < ω([set: G]) by rewrite lt0n omega_eq0 -cards_eq0 -lt0n cardsT.
have M1 : 0 < maxn ω([set: G]) α([set: G]) by rewrite leq_max o1.
have step3 : #|S| ^ b <= (maxn ω([set: G]) α([set: G])) ^ b by rewrite leq_exp2r.
have step4 : (maxn ω([set: G]) α([set: G])) ^ b
             <= (maxn ω([set: G]) α([set: G])) ^ (maxn a b).
  by apply: leq_pexp2l; [exact: M1|exact: leq_maxr].
apply: (leq_trans Acard); rewrite -cardS.
exact: leq_trans step3 step4.
Qed.

(*@EDGE from=multicolour_erdos_hajnal_statement to=the_erdos_hajnal_statement kind=implies status=verified proof=multicolour_erdos_hajnal_implies_the_erdos_hajnal cite="gc:e115" note="m=2 dictionary: chi i j = b2o (enum_val i -- enum_val j) on 'I_#|H|, gcol on 'I_#|G|; contains_pattern <-> has_induced_copy (contains_pattern_isubgraph), palette <= m-1 = 1 <-> clique or stable set (palette_clique_or_stable); exponents (a, maxn a b) repair the a <= b guard. The monochromatic base cases uses_all_colours excludes (H complete / H edgeless / #|H| <= 1) are closed by the Erdos-Szekeres bound of foundations/ramsey.v (ramsey_card_leq: omega(A) <= k -> #|A| <= (alpha(A)+1)^k, packaged as ramsey_eh_bound / ramsey_eh_bound_alpha), NOT by the diagonal R(k,k) <= 4^k bound, which is too weak (logarithmic, not polynomial)." *)

(** Sanity: all five D2ram nodes are in scope as [Prop]s.  The only edge among
    them is the verified (1) => (5) above; the remaining pairs are independent in
    both directions (see the module header). *)
Remark D2ram_nodes_in_scope :
  (multicolour_erdos_hajnal_statement : Prop) = multicolour_erdos_hajnal_statement /\
  (complete_bipartite_subgraphs_of_perfect_graphs_statement : Prop) = complete_bipartite_subgraphs_of_perfect_graphs_statement /\
  (chromatic_number_of_common_graphs_statement : Prop) = chromatic_number_of_common_graphs_statement /\
  (ramsey_properties_of_cayley_graphs_statement : Prop) = ramsey_properties_of_cayley_graphs_statement /\
  (the_erdos_hajnal_statement : Prop) = the_erdos_hajnal_statement.
Proof. do 4 (split; [reflexivity|]); reflexivity. Qed.

Print Assumptions multicolour_erdos_hajnal_implies_the_erdos_hajnal.
