(** * Minor.conjectures.implications_X220 — corpus-relation edges of wave X220

    The confirmed implies/equivalent_to edges of meta/corpus_relations.json whose
    endpoints are X220 rows.  e072 is VERIFIED (the two polynomial tree-alpha
    questions really are equivalent); e052 and e078 stay status=candidate, each
    resting on a substantive graph-theoretic argument that is not (yet) available
    here.  No false edge is forced: axiom-free, only [Qed]-closed results live in
    this file.

    What is proved for e052: two of the four source hypotheses ([clique_free_no_K],
    [even_hole_free_no_KB]) and the edge modulo the two wall containments
    ([e052_modulo_wall]); see the block above that theorem.  What is proved for
    e072: both halves of the "K_{t,t}-free iff induced biclique number < t"
    dictionary, the existence of the induced biclique number and the exact unit
    shift of a polynomial with natural coefficients. *)

From GTBase Require Import base.
From Minor.foundations Require Import containment width_params hole_containments.
From Minor.conjectures Require Import X27 X42 X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Proved bridge lemmas for e072 **************************************)

(** The Horner evaluation of a list of NATURAL coefficients is monotone. *)
Lemma x220_poly_eval_mono (p : seq nat) (a b : nat) :
  a <= b -> x220_poly_eval p a <= x220_poly_eval p b.
Proof.
move=> ab; elim: p => [|c q IH] //=.
by rewrite leq_add2l leq_mul.
Qed.

(** A graph whose induced biclique number is [s] has no induced ['K_s+1,s+1]. *)
Lemma x220_ibn_free (G : sgraph) (s : nat) :
  x220_ibn G s -> ~ has_induced_copy G (KB s.+1 s.+1).
Proof. by case=> _ /(_ s.+1) max /max; rewrite ltnn. Qed.

(** ** e072 : the two polynomial tree-alpha questions are EQUIVALENT (PROVED)

    Corpus argument (gc:e072): the source paper states the two questions are
    equivalent restatements of each other, via the dictionary "G is
    ['K_t,t]-free iff its induced biclique number is at most t-1", plus the fact
    that the classes [fun G => tree_mu_le G m] are exactly the maximal classes of
    bounded induced matching treewidth.

    Re-derivation.  Both halves of the dictionary are now available:

    - the induced biclique number EXISTS for every finite simple graph
      ([x220_ibn_exists]): the [s] with an induced ['K_s,s] form a nonempty
      ([s = 0], the empty graph) and bounded ([2s <= #|G|]) set of naturals, and
      [has_induced_copy] is DECIDABLE
      ([Minor.foundations.containment.has_induced_copyP]), so [ex_maxn] produces
      the maximum with no classical axiom;
    - it is monotone: an induced ['K_s,s] contains an induced ['K_t,t] for
      [t <= s] ([Minor.foundations.containment.has_induced_copy_KB_le], by
      widening both sides with [widen_ord]);
    - [x220_ibn_free] (already above) is the converse half.

    Source ⟹ target: the polynomial [p] of the source works unchanged.  Given
    [G] with no induced ['K_t,t] and [tree_mu_le G m], let [t0] be the induced
    biclique number of [G]; then [t0 < t] (otherwise monotonicity would produce
    the forbidden ['K_t,t]), so the source gives [tree_alpha_le G (p t0)] and
    [p t0 <= p t] by [x220_poly_eval_mono].

    Target ⟹ source: the degenerate case [m = 0], which the target excludes by
    its positivity hypothesis, needs NO separate argument -- apply the target at
    [maxn m 1] and use monotonicity of [tree_mu_le] in its bound
    ([Minor.foundations.width_params.tree_mu_leW]).  Given [x220_ibn G t],
    [x220_ibn_free] says [G] has no induced ['K_(t+1),(t+1)], so the target
    yields [tree_alpha_le G (p (t+1))]; the polynomial exhibited for the source
    is therefore the SHIFT of [p], and [poly_shift] below realises
    [x220_poly_eval (poly_shift p) t = x220_poly_eval p t.+1] exactly, by
    coefficient-wise addition of lists ([poly_add]). *)

(** *** Coefficient-wise addition and the unit shift of a polynomial *)

Fixpoint poly_add (p q : seq nat) : seq nat :=
  if p is a :: p' then (if q is b :: q' then (a + b) :: poly_add p' q' else p)
  else q.

Lemma poly_addE (p q : seq nat) (x : nat) :
  x220_poly_eval (poly_add p q) x = x220_poly_eval p x + x220_poly_eval q x.
Proof.
elim: p q => [q|a p IH [|b q]] /=; first by rewrite add0n.
- by rewrite addn0.
- by rewrite IH mulnDr addnACA.
Qed.

Fixpoint poly_shift (p : seq nat) : seq nat :=
  if p is a :: q then poly_add (poly_add [:: a] (poly_shift q)) (0 :: poly_shift q)
  else [::].

Lemma poly_shiftE (p : seq nat) (x : nat) :
  x220_poly_eval (poly_shift p) x = x220_poly_eval p x.+1.
Proof.
elim: p => [//|a q IH].
have e : poly_shift (a :: q)
       = poly_add (poly_add [:: a] (poly_shift q)) (0 :: poly_shift q) by [].
by rewrite e !poly_addE /= IH muln0 addn0 add0n mulSn addnA.
Qed.

(** *** Existence of the induced biclique number *)

Lemma x220_ibn_exists (G : sgraph) : exists t : nat, x220_ibn G t.
Proof.
have exP : exists s : nat, isubgraphb (KB s s) G.
  exists 0; apply/has_induced_copyP; apply: has_induced_copy_empty.
  by rewrite card_KB.
have ubP : forall s : nat, isubgraphb (KB s s) G -> s <= #|G|.
  move=> s hs; apply: leq_trans (leq_addr s s) _.
  by rewrite -card_KB; apply: has_induced_copy_card; apply/has_induced_copyP.
case: (ex_maxnP exP ubP) => t Pt maxt.
exists t; split; first exact/has_induced_copyP.
by move=> s /has_induced_copyP hs; exact: maxt.
Qed.

(** *** The two directions *)

Theorem e072_biclique_to_ktt :
  bounded_tree_mu_polynomial_biclique_tree_alpha_statement ->
  tree_mu_ktt_free_polynomial_tree_alpha_statement.
Proof.
move=> src m _; have [p Hp] := src m; exists p => t G ktt mu.
have [t0 ibn0] := x220_ibn_exists G.
case: ibn0 => c0 max0.
have t0t : t0 <= t.
  rewrite leqNgt; apply/negP => tt0.
  by apply: ktt; exact: has_induced_copy_KB_le (ltnW tt0) c0.
apply: tree_alpha_leW (@x220_poly_eval_mono p t0 t t0t) _.
by apply: Hp => //; split.
Qed.

Theorem e072_ktt_to_biclique :
  tree_mu_ktt_free_polynomial_tree_alpha_statement ->
  bounded_tree_mu_polynomial_biclique_tree_alpha_statement.
Proof.
move=> tgt m; have [p Hp] := tgt (maxn m 1) (leq_maxr m 1).
exists (poly_shift p) => G t mu ibn.
rewrite poly_shiftE; apply: Hp; first exact: x220_ibn_free ibn.
exact: tree_mu_leW (leq_maxl m 1) mu.
Qed.

Theorem bounded_tree_mu_polynomial_biclique_tree_alpha_equiv_tree_mu_ktt_free_polynomial_tree_alpha :
  bounded_tree_mu_polynomial_biclique_tree_alpha_statement <->
  tree_mu_ktt_free_polynomial_tree_alpha_statement.
Proof.
split.
- exact: e072_biclique_to_ktt.
- exact: e072_ktt_to_biclique.
Qed.

(** ** e052 — the two settled containments, and the two wall ones left ******

    [four_family_free_logarithmic_treewidth_statement] ⟹
    [even_hole_kt_free_logarithmic_treewidth_statement] (gc:e052).

    Re-derivation.  Given the target's [t], apply the source at [s := maxn t 5] and
    keep its constant [c]; both rows use the SAME treewidth encoding ([tw_le]) and the
    same logarithmic envelope, so the conclusion transfers verbatim, and [s] is chosen
    BEFORE the source's [exists c], so no choice principle is needed (contrast e053).
    Two of the four hypotheses are now discharged:

    - [~ has_induced_copy G 'K_s] : an induced copy of ['K_s] is a clique on [s]
      vertices ([Minor.foundations.hole_containments.isubgraph_K_clique]) and
      [x220_clique_free G t] with [t <= s] forbids it;
    - [~ has_induced_copy G (KB s s)] : ['K_s,s] with [s >= 2] carries an induced
      four-cycle, which is an even hole ([KB_even_hole], on [four_cycle_hole]).

    The two that are LEFT are the wall containments.  They are TRUE as encoded — a
    machine search shows that [x220_wall s] has, for every [s >= 5], an INDUCED
    subgraph that is a subdivision of ['K_2,3] (for [s = 5], the two degree-three
    vertices [(2,1)] and [(2,3)] joined by three induced, pairwise non-adjacent paths of
    lengths 2, 4 and 10; for [s <= 4] there is none, the wall being then a chain of at
    most three bricks), and an induced theta of the wall stays an induced theta after
    the wall is subdivided, because a subdivision of a subdivision of ['K_2,3] is again
    one.  What is missing is therefore not the mathematics but two pieces of
    machinery: (i) the explicit 17-vertex induced theta inside the 25-vertex
    [x220_wall 5], with its chordlessness checked edge by edge, and (ii) the
    COMPOSITION lemma "if [S] induces a theta in [K] and [W] is a subdivision of [K],
    then the vertex set of [W] over [S] induces a subdivision of that theta", i.e. the
    composition of two [subdiv_model]s, which this development does not have.  The
    line-graph variant needs, on top of that, "the line graph of a theta whose branch
    vertices are non-adjacent contains an induced prism" ([sline_subdiv_wall_has_prism]).
    [e052_modulo_wall] states the edge modulo exactly those two containments; the even
    holes of a theta and of a prism themselves are now available
    ([subdiv_KB23_even_hole], [prism_even_hole]). *)

Lemma clique_free_no_K (G : sgraph) (t s : nat) :
  t <= s -> x220_clique_free G t -> ~ has_induced_copy G 'K_s.
Proof.
move=> ts cf [i]; have [S cS cardS] := isubgraph_K_clique i.
by move: (cf S cS); rewrite cardS ltnNge ts.
Qed.

Lemma even_hole_free_no_KB (G : sgraph) (s : nat) :
  2 <= s -> x27_even_hole_free G -> ~ has_induced_copy G (KB s s).
Proof.
by move=> s2 eh [i]; case: (KB_even_hole i s2) => c [hc pc]; exact: (eh c hc pc).
Qed.

Lemma even_hole_free_no_copy_of (G W : sgraph) :
  x27_even_hole_free G -> (exists c : seq W, x27_hole c /\ ~~ odd (size c)) ->
  ~ has_induced_copy G W.
Proof.
move=> eh [c [hc pc]] [i]; apply: (eh [seq i x | x <- c]).
  exact: isubgraph_hole.
by rewrite size_map.
Qed.

Theorem e052_modulo_wall :
  (forall (s : nat) (W : sgraph), 5 <= s -> is_subdivision_of W (x220_wall s) ->
     exists c : seq W, x27_hole c /\ ~~ odd (size c)) ->
  (forall (s : nat) (W : sgraph), 5 <= s -> is_subdivision_of W (x220_wall s) ->
     exists c : seq (sline_graph W), x27_hole c /\ ~~ odd (size c)) ->
  four_family_free_logarithmic_treewidth_statement ->
  even_hole_kt_free_logarithmic_treewidth_statement.
Proof.
move=> wall lwall src t.
have [c Hc] := src (maxn t 5); exists c => G eh cf.
have t5 : 5 <= maxn t 5 := leq_maxr t 5.
apply: Hc.
- exact: (clique_free_no_K (leq_maxl t 5) cf).
- by apply: even_hole_free_no_KB eh; apply: leq_trans t5.
- by move=> W hW; apply: even_hole_free_no_copy_of eh (wall _ W t5 hW).
- by move=> W hW; apply: even_hole_free_no_copy_of eh (lwall _ W t5 hW).
Qed.

(** ** Candidate edges ****************************************************)


(*@EDGE from=four_family_free_logarithmic_treewidth_statement to=even_hole_kt_free_logarithmic_treewidth_statement kind=implies status=candidate proved=false cite="gc:e052" note="Corpus argument: an (even hole, K_t)-free graph satisfies the four-family hypothesis at s = max(t,5), because K_{s,s} contains an induced C_4, every induced subdivision of the s-by-s wall contains an induced theta, the line graph of such a subdivision contains an induced prism, and every theta and every prism contains an even hole. Quantifier-wise the edge is FINE (s is chosen before the source's exists c) and both rows use the same tw_le envelope, so no bridge is needed. TWO of the four hypotheses are now PROVED here: clique_free_no_K (an induced K_s is a clique of size s, foundations/hole_containments.v isubgraph_K_clique) and even_hole_free_no_KB (K_{s,s} with s>=2 carries an induced C_4, which is an even hole: KB_even_hole on four_cycle_hole); the theta and prism even-hole containments themselves are also PROVED (foundations/hole_containments.v subdiv_KB23_even_hole, prism_even_hole). BLOCKED on the two WALL containments, which are true but unformalised: a machine search confirms x220_wall s has an induced subdivision of K_2,3 exactly for s >= 5 (for s = 5: (2,1) and (2,3) joined by induced pairwise non-adjacent paths of lengths 2, 4, 10; for s <= 4 the wall is a chain of at most three bricks and has none), so what is missing is (i) that explicit 17-vertex induced theta inside the 25-vertex wall and (ii) the COMPOSITION of two subdiv_models (an induced theta of K stays an induced theta in every subdivision of K), plus for the line-graph variant sline_subdiv_wall_has_prism. Theorem e052_modulo_wall in this file states the edge modulo exactly those two containments." *)

(*@EDGE from=bounded_tree_mu_polynomial_biclique_tree_alpha_statement to=tree_mu_ktt_free_polynomial_tree_alpha_statement kind=equiv status=verified proved=true proof=bounded_tree_mu_polynomial_biclique_tree_alpha_equiv_tree_mu_ktt_free_polynomial_tree_alpha cite="gc:e072" note="The source paper states the two questions are equivalent, via 'G is K_{t,t}-free iff its induced biclique number is at most t-1'. Both halves of the dictionary are now proved: x220_ibn_free (this file) and, newly, the EXISTENCE of the induced biclique number (x220_ibn_exists, from decidability of has_induced_copy — foundations/containment.v has_induced_copyP — plus ex_maxn) and its monotonicity (has_induced_copy_KB_le, widening both sides of K_{t,t}). The degenerate case m = 0, excluded by the target's positivity hypothesis, is absorbed by applying the target at maxn m 1 and tree_mu_leW. Target => source also needs the exact unit shift of a polynomial with natural coefficients (poly_shift / poly_shiftE, this file)." *)

(*@EDGE from=small_hereditary_class_bounded_twin_width_statement to=polynomial_expansion_bounded_twin_width_statement kind=implies status=refuted-direction cite="gc:e078" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): source row is DISPROVED upstream; the annotation documents a historical route, not a live implication. Earlier note: Corpus argument: a class of polynomial expansion is small and may be taken hereditary (expansion is monotone under subgraphs), so the Small Conjecture bounds its twin-width. Not closed here: 'polynomial expansion implies small' is the counting theorem of Twin-width II and is not available; note also that the source row is recorded upstream as DISPROVED, so this edge documents a historical route, not a live one." *)

Print Assumptions clique_free_no_K.
Print Assumptions even_hole_free_no_KB.
Print Assumptions even_hole_free_no_copy_of.
Print Assumptions e052_modulo_wall.
Print Assumptions x220_poly_eval_mono.
Print Assumptions x220_ibn_free.
Print Assumptions poly_shiftE.
Print Assumptions x220_ibn_exists.
Print Assumptions bounded_tree_mu_polynomial_biclique_tree_alpha_equiv_tree_mu_ktt_free_polynomial_tree_alpha.
