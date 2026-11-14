(** * Minor.conjectures.implications_X220 — corpus-relation edges of wave X220

    The confirmed implies/equivalent_to edges of meta/corpus_relations.json whose
    endpoints are X220 rows.  e052 and e072 are VERIFIED (e052: four-family-free
    implies (even hole, K_t)-free with logarithmic treewidth; e072: the two
    polynomial tree-alpha questions really are equivalent); e078 is a
    refuted-direction annotation.  No false edge is forced: axiom-free, only
    [Qed]-closed results live in this file.

    What is proved for e052: the four source hypotheses, two in the block above
    [e052_modulo_wall] and the two wall containments in the e052 section after it,
    hence the edge.  What is proved for e072: both halves of the "K_{t,t}-free iff
    induced biclique number < t" dictionary, the existence of the induced biclique
    number and the exact unit shift of a polynomial with natural coefficients. *)

From GTBase Require Import base.
From GTBase Require induced_cycles.
From Minor.foundations Require Import containment width_params hole_containments.
From Minor.conjectures Require Import X27 X42 X220.
From GTBase Require poly_nat.
From mathcomp Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Proved bridge lemmas for e072 **************************************)

(** The Horner evaluation of a list of NATURAL coefficients is monotone. *)
Lemma x220_poly_eval_mono (p : seq nat) (a b : nat) :
  a <= b -> x220_poly_eval p a <= x220_poly_eval p b.
Proof. exact: GTBase.poly_nat.horner_nat_mono. Qed.

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
elim: p q => [q|a p IH [|b q]]; first by rewrite /x220_poly_eval GTBase.poly_nat.horner_nat_nil add0n.
- by rewrite /x220_poly_eval GTBase.poly_nat.horner_nat_nil addn0.
- have -> : poly_add (a :: p) (b :: q) = (a + b) :: poly_add p q by [].
  move: IH; rewrite /x220_poly_eval => IH.
  by rewrite !GTBase.poly_nat.horner_nat_cons IH mulnDr addnACA.
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
rewrite e !poly_addE; move: IH; rewrite /x220_poly_eval => IH.
rewrite !GTBase.poly_nat.horner_nat_cons GTBase.poly_nat.horner_nat_nil IH.
by rewrite muln0 addn0 add0n mulSn addnA.
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

(** ** e052 — the four containments: two settled here, the two wall ones below ***

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

    The two other hypotheses are the wall containments, PROVED in the e052 section
    after this block's theorem (2026-11-14), and with them the edge:
    - (H1) [e052_wall_even_hole]: for [s >= 5], every subdivision [W] of
      [x220_wall s] has an even hole.  In [x220_wall 5] the branch vertices [(2,1)]
      and [(2,3)] are joined by induced, pairwise non-adjacent paths of lengths 2, 4
      and 10 (a 15-vertex theta); its three cycles, on 6, 12 and 14 vertices, are
      holes ([e052_c12_hole] and the next two, by computation), carried into
      [x220_wall s] by an induced embedding ([e052_wall_embed]) and into [W] by
      [kch_hole]: the image of a hole of [K] under an exact [subdiv_model] is a hole
      of [size c] plus the path sizes ([kch_size]; [fch_hole] for any length).  Each
      theta edge lies on two of the three cycles, so the three image sizes add up to
      an even number and one of them is even.
    - (H2) [e052_line_even_hole]: a hole [x_0 ... x_(n-1)] of [W] with [n >= 4] gives
      the hole of the edges [{x_i, x_(i+1)}] in [sline_graph W], of the same size
      ([e052_line_hole]), so no prism is needed.  The machine search recorded here
      earlier found no induced theta in [x220_wall s] for [s <= 4], which is why the
      source is applied at [s >= 5].  The even holes of a theta and of a prism
      ([subdiv_KB23_even_hole], [prism_even_hole]) stay available. *)

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

(** ** e052 — the two wall containments, and the edge ************************

    [kch_hole] generalises [fch_hole] (foundations/hole_containments.v) from induced
    4-cycles to holes of any length: the image of a hole of [K] under an exact
    [subdiv_model] of [K] is a hole of the host.  The wall has girth 6, so the
    4-cycle version cannot serve.  The wall theta, the parity of its three cycles and
    the line graph then give (H1) and (H2) of [e052_modulo_wall]. *)

(** In a uniq cyclic list on at least three entries, no pair is consecutive in both directions. *)
Lemma kch_pairs_antisym (T : eqType) (w0 : T) (s : seq T) (x y : T) :
  uniq (w0 :: s) -> 2 < size (w0 :: s) ->
  (x, y) \in spairs (w0 :: s ++ [:: w0]) -> (y, x) \in spairs (w0 :: s ++ [:: w0]) -> False.
Proof.
move=> u n2; rewrite spairs_closeE.
set L := w0 :: s; set R := s ++ [:: w0].
have szR : size R = size L by rewrite /R size_cat addn1.
have succlt : forall i, i < size L -> (if i < size s then i.+1 else 0) < size L.
  by move=> i hi; case: ifP => //.
have nthR : forall i, i < size L -> nth w0 R i = nth w0 L (if i < size s then i.+1 else 0).
  move=> i hi; rewrite /R nth_cat; case: ifP => his //.
  have -> : i - size s = 0 by apply/eqP; rewrite subn_eq0 -ltnS; exact: hi.
  by [].
have pairE : forall a b, (a, b) \in zip L R ->
    exists2 i, i < size L & (a = nth w0 L i) /\ (b = nth w0 L (if i < size s then i.+1 else 0)).
  move=> a b /(nthP (w0, w0)) [i]; rewrite size_zip szR minnn => hi.
  rewrite nth_zip ?szR // => -[<- <-].
  by exists i => //; rewrite nthR.
move=> /pairE [i hi [xi yi]] /pairE [j hj [yj xj]].
have ij : (if i < size s then i.+1 else 0) = j.
  by apply/eqP; rewrite -(nth_uniq w0 (succlt i hi) hj u) -yi -yj eqxx.
have ji : (if j < size s then j.+1 else 0) = i.
  by apply/eqP; rewrite -(nth_uniq w0 (succlt j hj) hi u) -xi -xj eqxx.
move: n2 hi hj ij ji; rewrite /L /= !ltnS.
case: ifP => [hi'|/negbT hi']; case: ifP => [hj'|/negbT hj'].
- move=> _ _ _ e1 e2; rewrite -e1 in e2; by have := leqnn i; rewrite -{1}e2 ltnNge leqnSn.
- by move=> s1 _ _ e1 e2; move: hj'; rewrite -e1 -e2 s1.
- by move=> s1 _ _ e1 e2; move: hi'; rewrite -e2 -e1 s1.
- by move=> s1 _ _ _ e2; move: hi'; rewrite -e2 (ltn_trans _ s1).
Qed.

(** A flatten of pairwise disjoint uniq blocks is uniq. *)
Lemma kch_uniq_flatten (T U : eqType) (f : T -> seq U) (ps : seq T) :
  uniq ps -> (forall p, p \in ps -> uniq (f p)) ->
  (forall p q z, p \in ps -> q \in ps -> p != q -> z \in f p -> z \notin f q) ->
  uniq (flatten (map f ps)).
Proof.
elim: ps => [|p ps IH] //= /andP[pn up] uf dj.
rewrite cat_uniq (uf p (mem_head p ps)) IH //=.
- by move=> q qs; apply: uf; rewrite in_cons qs orbT.
- by move=> q q' z qs q's; apply: dj; rewrite in_cons ?qs ?q's orbT.
rewrite andbT; apply/hasPn => z /flattenP [q' /mapP [q qs ->] zq]; apply/negP => zp.
have pq : p != q by apply: contraNneq pn => ->.
have qs' : q \in p :: ps by rewrite in_cons qs orbT.
by move: (dj p q z (mem_head p ps) qs' pq zp); rewrite zq.
Qed.

(** The first and second components of the cyclic pairs. *)
Lemma kch_pairs_fst (T : Type) (w0 : T) (s : seq T) :
  unzip1 (spairs (w0 :: s ++ [:: w0])) = w0 :: s.
Proof.
by rewrite spairs_closeE unzip1_zip // size_cat addn1.
Qed.

Lemma kch_pairs_snd (T : Type) (w0 : T) (s : seq T) :
  unzip2 (spairs (w0 :: s ++ [:: w0])) = s ++ [:: w0].
Proof.
by rewrite spairs_closeE unzip2_zip // size_cat addn1.
Qed.

(** A map that is uniq on a list is injective on it. *)
Lemma kch_uniq_map_inj (T U : eqType) (f : T -> U) (s : seq T) :
  uniq (map f s) -> {in s &, injective f}.
Proof.
elim: s => [|a s IH] //= /andP[fa us] p q; rewrite !in_cons.
case/orP=> [/eqP->|ps]; case/orP=> [/eqP->|qs] e //.
- by move: fa; rewrite e (map_f f qs).
- by move: fa; rewrite -e (map_f f ps).
- exact: IH.
Qed.

(** Every consecutive pair of a path is an edge of the relation. *)
Lemma kch_path_pairs (T : eqType) (e : rel T) (x : T) (s : seq T) (a b : T) :
  path e x s -> (a, b) \in spairs (x :: s) -> e a b.
Proof.
elim: s x => [|y s IH] x //= /andP[exy ps].
rewrite in_cons xpair_eqE -/(spairs (y :: s)) => /orP[/andP[/eqP-> /eqP->] //|]; exact: IH.
Qed.

Section KCycle.
Variables (K G : sgraph) (m : subdiv_model K G).

Local Notation B := (sdm_branch m).
Local Notation P := (sdm_path m).

Definition kch_block (p : K * K) : seq G := B p.1 :: P p.1 p.2.

(** The image of a walk [x :: xs] of [K]: one block per consecutive pair. *)
Fixpoint kch_walk (x : K) (xs : seq K) : seq G :=
  if xs is y :: ys then kch_block (x, y) ++ kch_walk y ys else [::].

Lemma kch_walkE (x : K) (xs : seq K) :
  kch_walk x xs = flatten [seq kch_block p | p <- spairs (x :: xs)].
Proof.
elim: xs x => [|y ys IH] x //=; by rewrite IH.
Qed.

Lemma kch_walk_path (x : K) (xs : seq K) :
  path (--) x xs -> xs != [::] ->
  path (--) (B x) (rcons (behead (kch_walk x xs)) (B (last x xs))).
Proof.
elim: xs x => [|y ys IH] x // /andP[xy pys] _.
case: ys IH pys => [|z zs] IH pys.
  by rewrite /= cats0; exact: fch_pathP.
have -> : behead (kch_walk x [:: y, z & zs]) = P x y ++ B y :: behead (kch_walk y (z :: zs)) by [].
rewrite (_ : last x [:: y, z & zs] = last y (z :: zs)) //.
apply: sd_path_cat3; first exact: fch_pathP.
exact: IH.
Qed.

Lemma kch_walk_head (x : K) (xs : seq K) :
  xs != [::] -> kch_walk x xs = B x :: behead (kch_walk x xs).
Proof.
by case: xs.
Qed.

Lemma kch_walk_size (x : K) (xs : seq K) :
  size (kch_walk x xs) = size xs + sumn [seq size (P p.1 p.2) | p <- spairs (x :: xs)].
Proof.
elim: xs x => [|y ys IH] x //=; rewrite size_cat /= IH; case: ys IH => [|z zs] IH;
  rewrite /= ?addn0 ?addnS //; rewrite !addSn !addnA; congr _.+1; rewrite addnAC.
by rewrite [size zs + _]addnC addnAC.
Qed.

(** The consecutive pairs of the walk's image closed by [B] of its last vertex. *)
Lemma kch_walk_spairs (x : K) (xs : seq K) :
  spairs (kch_walk x xs ++ [:: B (last x xs)])
  = flatten [seq spairs (B p.1 :: rcons (P p.1 p.2) (B p.2)) | p <- spairs (x :: xs)].
Proof.
elim: xs x => [|y ys IH] x //.
case: ys IH => [|z zs] IH.
  by rewrite /kch_walk /kch_block /= !cats0 -!cats1.
have hw : kch_walk y (z :: zs) = B y :: behead (kch_walk y (z :: zs)) by [].
rewrite (_ : kch_walk x [:: y, z & zs] = (B x :: P x y) ++ kch_walk y (z :: zs)) //.
rewrite -catA hw [(B y :: _) ++ _]cat_cons spairs_cat_mid rcons_cons -[B y :: _ ++ _]cat_cons -hw.
rewrite (_ : last x [:: y, z & zs] = last y (z :: zs)) // IH; by rewrite spairs_cons.
Qed.

(** The image of the closed walk along the hole [w0 :: s]. *)
Definition kch_cycle (w0 : K) (s : seq K) : seq G := kch_walk w0 (s ++ [:: w0]).

(** The image of a hole is a hole; the hole and [subdiv_rep m] are explicit premises. *)
Lemma kch_cp_edge (w0 : K) (s : seq K) (p : K * K) :
  induced_cycles.hole (w0 :: s) -> p \in spairs (w0 :: s ++ [:: w0]) -> p.1 -- p.2.
Proof.
move=> hc hp; case: hc => /andP[cyc _] _; case: p hp => a b hp /=.
apply: (kch_path_pairs _ hp); by move: cyc; rewrite /cycle cats1.
Qed.

Lemma kch_cycleP (w0 : K) (s : seq K) :
  induced_cycles.hole (w0 :: s) -> cycle (--) (kch_cycle w0 s).
Proof.
move=> hc.
case: hc => /andP[cyc _] _.
have ne : s ++ [:: w0] != [::] by case: s {cyc}.
rewrite /kch_cycle (kch_walk_head w0 ne) /=.
have := kch_walk_path (x := w0) (xs := s ++ [:: w0]); rewrite cats1 last_rcons -cats1.
apply; last exact: ne.
by move: cyc; rewrite /cycle cats1.
Qed.

Lemma kch_uniq (w0 : K) (s : seq K) :
  induced_cycles.hole (w0 :: s) -> uniq (kch_cycle w0 s).
Proof.
move=> hc; set cp := spairs (w0 :: s ++ [:: w0]).
case: (hc) => /andP[_ u] [n3 _].
have u1 : uniq (unzip1 cp) by rewrite kch_pairs_fst.
have finj := kch_uniq_map_inj u1.
rewrite /kch_cycle kch_walkE.
apply: kch_uniq_flatten.
- exact: map_uniq u1.
- by move=> p hp; apply: fch_block_uniq; exact: (kch_cp_edge hc hp).
move=> p q z hp hq pq zp.
have p1q1 : q.1 != p.1.
  by apply: contraNneq pq => e; apply/eqP; apply: finj.
apply: (fch_blocks_disj (kch_cp_edge hc hq) (kch_cp_edge hc hp) p1q1 _ zp).
apply/negP => /eqP e.
have q1p2 : q.1 = p.2.
  have : q.1 \in [set p.1; p.2] by rewrite -e !inE eqxx.
  by rewrite !inE (negbTE p1q1) => /eqP.
have p1q2 : p.1 = q.2.
  have : p.1 \in [set q.1; q.2] by rewrite e !inE eqxx.
  by rewrite !inE eq_sym (negbTE p1q1) => /eqP.
apply: (kch_pairs_antisym (x := p.1) (y := p.2) u (ltnW n3)).
  by case: p hp {pq zp p1q1 e q1p2 p1q2}.
by rewrite -q1p2 p1q2; case: q hq {pq p1q1 e q1p2 p1q2}.
Qed.

Lemma kch_chordless (w0 : K) (s : seq K) (x y : G) :
  subdiv_rep m -> induced_cycles.hole (w0 :: s) ->
  x \in kch_cycle w0 s -> y \in kch_cycle w0 s -> x -- y -> x != y ->
  seq_cyclic_consecutiveb (kch_cycle w0 s) x y.
Proof.
move=> rep hc hx hy xy nxy; set cp := spairs (w0 :: s ++ [:: w0]).
case: (hc) => /andP[_ uc] [n3 chc].
have memK : forall z, (z \in kch_cycle w0 s) = has (fun p => z \in kch_block p) cp.
  move=> z; rewrite /kch_cycle kch_walkE.
  apply/flattenP/hasP => [[b /mapP [p hp ->] zb]|[p hp zp]]; first by exists p.
  by exists (kch_block p) => //; apply: map_f.
have fstin : forall p, p \in cp -> p.1 \in w0 :: s.
  by move=> p hp; rewrite -(kch_pairs_fst w0 s); apply: map_f.
have sndin : forall p, p \in cp -> p.2 \in w0 :: s.
  move=> p hp; have : p.2 \in s ++ [:: w0] by rewrite -(kch_pairs_snd w0 s); apply: map_f.
  by rewrite mem_cat !inE orbC => /orP[->|->]; rewrite ?orbT.
have branchin : forall w, B w \in kch_cycle w0 s -> w \in w0 :: s.
  move=> w; rewrite memK => /hasP [p hp]; rewrite /kch_block in_cons => /orP[/eqP e|hw].
  - by rewrite (sdm_inj e); apply: fstin.
  - by move: (fch_avoid m w (kch_cp_edge hc hp)); rewrite hw.
have foreign : forall u v z, u -- v -> (forall p, p \in cp -> [set u; v] != [set p.1; p.2]) ->
    z \in P u v -> z \notin kch_cycle w0 s.
  move=> u v z uv ne hz; rewrite memK; apply/hasPn => p hp.
  rewrite /kch_block in_cons negb_or; apply/andP; split.
  - exact: (@sdm_avoid K G m u v p.1 z uv hz).
  - exact: (fch_disj uv (kch_cp_edge hc hp) (ne p hp) hz).
have ne : s ++ [:: w0] != [::] by rewrite cats1; apply/eqP => /(congr1 size); rewrite size_rcons.
have lw : last w0 (s ++ [:: w0]) = w0 by rewrite cats1 last_rcons.
have flatE : forall q, (q \in spairs (kch_cycle w0 s ++ [:: B w0]))
    = has (fun p => q \in spairs (B p.1 :: rcons (P p.1 p.2) (B p.2))) cp.
  move=> q; rewrite /kch_cycle.
  have -> : B w0 = B (last w0 (s ++ [:: w0])) by rewrite lw.
  rewrite kch_walk_spairs.
  apply/flattenP/hasP => [[b /mapP [p hp ->] qb]|[p hp qp]]; first by exists p.
  by exists (spairs (B p.1 :: rcons (P p.1 p.2) (B p.2))) => //; apply: (map_f (fun p : K * K => _) hp).
have consecE : forall a b, (a, b) \in cp -> sd_consec (B a) (B b) (P a b) x y ->
    seq_cyclic_consecutiveb (kch_cycle w0 s) x y.
  move=> a b hab; rewrite sd_consec_spairs => hxy.
  have hk : kch_cycle w0 s = B w0 :: behead (kch_cycle w0 s).
    by rewrite /kch_cycle (kch_walk_head w0 ne).
  rewrite hk consec_spairs -cat_cons -hk !flatE.
  by case/orP: hxy => h; apply/orP; [left|right]; apply/hasP; exists (a, b).
case: rep => _ /(_ x y xy) [u [v [uv hcs]]].
have only : forall a b, a -- b -> sd_consec (B a) (B b) (P a b) x y -> a \notin w0 :: s -> False.
  move=> a b ab hcs' na.
  have ne_sets : forall p, p \in cp -> [set a; b] != [set p.1; p.2].
    move=> p hp; apply: set2_neql.
    - by apply: contraNneq na => ->; apply: fstin.
    - by apply: contraNneq na => ->; apply: sndin.
  have out : forall z, z \in B a :: rcons (P a b) (B b) -> z \in kch_cycle w0 s -> z = B b.
    move=> z; rewrite in_cons mem_rcons in_cons => /orP[/eqP->|/orP[/eqP->//|hz]] hzk.
    - by move: na; rewrite (branchin a hzk).
    - by move: hzk; rewrite (negbTE (foreign a b z ab ne_sets hz)).
  move: hcs'; rewrite sd_consec_spairs => /orP[] /mem_spairs /andP[h1 h2].
  - by move: nxy; rewrite (out x h1 hx) (out y h2 hy) eqxx.
  - by move: nxy; rewrite (out y h1 hy) (out x h2 hx) eqxx.
have hcs' : sd_consec (B v) (B u) (P v u) x y by rewrite (sdm_pathC m uv) -sd_consec_sym.
have vu : v -- u by rewrite sg_sym.
have uin : u \in w0 :: s by apply/negPn/negP => /(only u v uv hcs).
have vin : v \in w0 :: s by apply/negPn/negP => /(only v u vu hcs').
move: (chc u v uin vin uv); rewrite consec_spairs => /orP[h|h].
- exact: (consecE u v h hcs).
- exact: (consecE v u h hcs').
Qed.

Lemma kch_size (w0 : K) (s : seq K) :
  size (kch_cycle w0 s) = size (w0 :: s) + sumn [seq size (P p.1 p.2) | p <- spairs (w0 :: s ++ [:: w0])].
Proof.
by rewrite /kch_cycle kch_walk_size size_cat addn1.
Qed.

Lemma kch_hole (w0 : K) (s : seq K) :
  subdiv_rep m -> induced_cycles.hole (w0 :: s) -> induced_cycles.hole (kch_cycle w0 s).
Proof.
move=> rep hc.
split; first by rewrite /ucycle (kch_cycleP hc) (kch_uniq hc).
split; last by apply/induced_cycles.cyclic_chordless_edge_neq => x y hx hy xy nxy;
  exact: (kch_chordless rep hc hx hy xy nxy).
rewrite kch_size; case: hc => _ [n3 _]; exact: leq_trans n3 (leq_addr _ _).
Qed.

End KCycle.

(** ** The wall theta *)

Notation e052v i j := ((@Ordinal 5 i isT, @Ordinal 5 j isT) : x220_wall 5).

Definition e052_c12 : seq (x220_wall 5) :=
  [:: e052v 2 1; e052v 2 2; e052v 2 3; e052v 1 3; e052v 1 2; e052v 1 1].
Definition e052_c13 : seq (x220_wall 5) :=
  [:: e052v 2 1; e052v 2 2; e052v 2 3; e052v 2 4; e052v 3 4; e052v 3 3; e052v 4 3; e052v 4 2;
      e052v 4 1; e052v 3 1; e052v 3 0; e052v 2 0].
Definition e052_c23 : seq (x220_wall 5) :=
  [:: e052v 2 1; e052v 1 1; e052v 1 2; e052v 1 3; e052v 2 3; e052v 2 4; e052v 3 4; e052v 3 3;
      e052v 4 3; e052v 4 2; e052v 4 1; e052v 3 1; e052v 3 0; e052v 2 0].

Lemma e052_c12_hole : induced_cycles.hole e052_c12.
Proof. by apply/induced_cycles.holeP; vm_compute. Qed.
Lemma e052_c13_hole : induced_cycles.hole e052_c13.
Proof. by apply/induced_cycles.holeP; vm_compute. Qed.
Lemma e052_c23_hole : induced_cycles.hole e052_c23.
Proof. by apply/induced_cycles.holeP; vm_compute. Qed.

(** The 5-wall sits induced in every s-wall with s >= 5. *)
Definition e052_wall_fun (s0 : nat) (h : 5 <= s0) (u : x220_wall 5) : x220_wall s0 :=
  (widen_ord h u.1, widen_ord h u.2).

Lemma e052_wall_fun_inj (s0 : nat) (h : 5 <= s0) : injective (e052_wall_fun h).
Proof.
by move=> [a b] [c d] /= [e1 e2]; congr pair; apply: val_inj.
Qed.

Lemma e052_wall_fun_mono (s0 : nat) (h : 5 <= s0) :
  {mono e052_wall_fun h : x y / x -- y >-> x -- y}.
Proof.
by move=> [a b] [c d].
Qed.

Definition e052_wall_embed (s0 : nat) (h : 5 <= s0) : x220_wall 5 ⇀ x220_wall s0 :=
  ISubgraph (@e052_wall_fun_inj s0 h) (@e052_wall_fun_mono s0 h).

(** (H1) Every subdivision of the s-wall, s >= 5, has an even hole. *)
Lemma e052_wall_even_hole (s0 : nat) (W : sgraph) :
  5 <= s0 -> is_subdivision_of W (x220_wall s0) -> exists c : seq W, x27_hole c /\ ~~ odd (size c).
Proof.
move=> h [m rep].
pose i := e052_wall_embed h.
have H12 := kch_hole rep (isubgraph_hole i e052_c12_hole).
have H13 := kch_hole rep (isubgraph_hole i e052_c13_hole).
have H23 := kch_hole rep (isubgraph_hole i e052_c23_hole).
pose f (p : x220_wall s0 * x220_wall s0) := size (sdm_path m p.1 p.2).
pose P1 := [:: (i (e052v 2 1), i (e052v 2 2)); (i (e052v 2 2), i (e052v 2 3))].
pose P2 := [:: (i (e052v 2 1), i (e052v 1 1)); (i (e052v 1 1), i (e052v 1 2));
               (i (e052v 1 2), i (e052v 1 3)); (i (e052v 1 3), i (e052v 2 3))].
pose P2r := [:: (i (e052v 2 3), i (e052v 1 3)); (i (e052v 1 3), i (e052v 1 2));
                (i (e052v 1 2), i (e052v 1 1)); (i (e052v 1 1), i (e052v 2 1))].
pose P3 := [:: (i (e052v 2 3), i (e052v 2 4)); (i (e052v 2 4), i (e052v 3 4));
               (i (e052v 3 4), i (e052v 3 3)); (i (e052v 3 3), i (e052v 4 3));
               (i (e052v 4 3), i (e052v 4 2)); (i (e052v 4 2), i (e052v 4 1));
               (i (e052v 4 1), i (e052v 3 1)); (i (e052v 3 1), i (e052v 3 0));
               (i (e052v 3 0), i (e052v 2 0)); (i (e052v 2 0), i (e052v 2 1))].
set k12 := kch_cycle _ _ _ in H12.
set k13 := kch_cycle _ _ _ in H13.
set k23 := kch_cycle _ _ _ in H23.
have sym : forall a b : x220_wall 5, a -- b -> f (i b, i a) = f (i a, i b).
  by move=> a b ab; rewrite /f /= (sdm_pathC m (_ : i a -- i b)) ?size_rev.
have E12 : size k12 = 6 + (sumn (map f P1) + sumn (map f P2r)).
  by rewrite /k12 kch_size -sumn_cat -map_cat.
have E13 : size k13 = 12 + (sumn (map f P1) + sumn (map f P3)).
  by rewrite /k13 kch_size -sumn_cat -map_cat.
have E23 : size k23 = 14 + (sumn (map f P2) + sumn (map f P3)).
  by rewrite /k23 kch_size -sumn_cat -map_cat.
have E2 : sumn (map f P2r) = sumn (map f P2).
  rewrite /= (sym (e052v 1 3) (e052v 2 3)) // (sym (e052v 1 2) (e052v 1 3)) //.
  rewrite (sym (e052v 1 1) (e052v 1 2)) // (sym (e052v 2 1) (e052v 1 1)) //.
  by rewrite /i /=; lia.
have par : ~~ odd (size k12 + size k13 + size k23).
  rewrite E12 E13 E23 E2.
  set A := sumn [seq f p | p <- P1]; set B := sumn [seq f p | p <- P2].
  set C := sumn [seq f p | p <- P3].
  have -> : 6 + (A + B) + (12 + (A + C)) + (14 + (B + C)) = 2 * (16 + A + B + C) by lia.
  by rewrite oddM.
case o12 : (odd (size k12)); last by exists k12; split; [exact: H12 | rewrite o12].
case o13 : (odd (size k13)); last by exists k13; split; [exact: H13 | rewrite o13].
case o23 : (odd (size k23)); last by exists k23; split; [exact: H23 | rewrite o23].
by move: par; rewrite !oddD o12 o13 o23.
Qed.

(** ** (H2): the line graph *)

(** [hole_map] with injectivity and adjacency asked only on the cycle's entries. *)
Lemma e052_hole_map_in (G H : sgraph) (f : H -> G) (c : seq H) :
  {in c &, injective f} -> {in c &, forall x y, (f x -- f y) = (x -- y)} ->
  induced_cycles.hole c -> induced_cycles.hole (map f c).
Proof.
move=> finj fE [/andP[cyc uc] [sz ch]]; split; [apply/andP; split|split].
- by rewrite cycle_map (@eq_in_cycle _ (mem c) _ (@edge_rel H)) ?cyc.
- by rewrite map_inj_in_uniq.
- by rewrite size_map.
move=> u v /mapP[x xc ->] /mapP[y yc ->]; rewrite fE // => xy.
have := ch x y xc yc xy; rewrite /seq_cyclic_consecutiveb -map_rot.
by case/orP=> h; apply/orP; [left | right]; exact: mem_zip_map h.
Qed.

(** A hole of [W] gives a hole of the same size in its line graph: the edges [x -- next c x]. *)
Lemma e052_line_hole (W : sgraph) (c : seq W) :
  induced_cycles.hole c -> exists c' : seq (sline_graph W), induced_cycles.hole c' /\ size c' = size c.
Proof.
case: c => [|w0 s] hc; first by case: hc => _ [].
have [/andP[cyc uc] [sz ch]] := hc.
set c := w0 :: s in hc cyc uc sz ch *.
have nxt : forall x, x \in c -> x -- next c x by move=> x xc; exact: (next_cycle cyc xc).
have antis : forall x y, (x, y) \in zip c (rot 1 c) -> (y, x) \in zip c (rot 1 c) -> False.
  move=> x y; rewrite /c rot1_cons -cats1 -spairs_closeE.
  exact: (kch_pairs_antisym uc (ltnW sz)).
have e0 : [set w0; next c w0] \in E(W) by rewrite in_edges; apply: nxt; rewrite mem_head.
pose d0 : sline_graph W := exist _ [set w0; next c w0] e0.
pose f (x : W) : sline_graph W := insubd d0 [set x; next c x].
have fv : forall x, x \in c -> val (f x) = [set x; next c x].
  by move=> x xc; rewrite /f insubdK // in_edges; exact: nxt.
have zipE : forall x y, x \in c -> ((x, y) \in zip c (rot 1 c)) = (next c x == y).
  by move=> x y xc; rewrite seq_zip_nextE // xc.
have ninj : {in c &, injective (next c)}.
  by move=> x y _ _ /(congr1 (path.prev c)); rewrite !path.prev_next.
exists (map f c); split; last by rewrite size_map.
apply: e052_hole_map_in hc.
- move=> x y xc yc /(congr1 val); rewrite !fv // => e.
  have : x \in [set y; next c y] by rewrite -e !inE eqxx.
  rewrite !inE => /orP[/eqP //|/eqP xny].
  have : y \in [set x; next c x] by rewrite e !inE eqxx.
  rewrite !inE => /orP[/eqP -> //|/eqP ynx].
  case: (antis x y); first by rewrite zipE // ynx.
  by rewrite zipE // xny.
move=> x y xc yc.
have -> : (f x -- f y) = (val (f x) != val (f y)) && (val (f x) :&: val (f y) != set0) by [].
rewrite !fv //; apply/idP/idP.
- case/andP => ne /set0Pn [z].
  rewrite !inE => /andP [/orP[/eqP zx|/eqP zn] /orP[/eqP zy|/eqP zm]].
  + by move: ne; rewrite -zx -zy eqxx.
  + by rewrite sg_sym -[x]zx zm; apply: nxt.
  + by rewrite -[y]zy zn; apply: nxt.
  + by move: ne; rewrite (ninj x y xc yc (etrans (esym zn) zm)) eqxx.
move=> xy; have nxy : x != y by rewrite (sg_edgeNeq xy).
have := ch x y xc yc xy; rewrite /seq_cyclic_consecutiveb !zipE // => /orP[/eqP ynx|/eqP xny].
- apply/andP; split.
  + apply/negP => /eqP e.
    have : x \in [set y; next c y] by rewrite -e !inE eqxx.
    rewrite !inE (negbTE nxy) /= => /eqP xny.
    by case: (antis x y); rewrite zipE // ?ynx ?xny.
  + by apply/set0Pn; exists y; rewrite !inE ynx !eqxx !orbT.
- apply/andP; split.
  + apply/negP => /eqP e.
    have : y \in [set x; next c x] by rewrite e !inE eqxx.
    rewrite !inE eq_sym (negbTE nxy) /= => /eqP ynx.
    by case: (antis x y); rewrite zipE //; apply/eqP; [exact: (esym ynx) | exact: xny].
  + by apply/set0Pn; exists x; rewrite !inE xny !eqxx !orbT.
Qed.

(** (H2) Every subdivision of the s-wall, s >= 5, has an even hole in its line graph. *)
Lemma e052_line_even_hole (s0 : nat) (W : sgraph) :
  5 <= s0 -> is_subdivision_of W (x220_wall s0) ->
  exists c : seq (sline_graph W), x27_hole c /\ ~~ odd (size c).
Proof.
move=> h hW; have [c [hc ev]] := e052_wall_even_hole h hW.
have [c' [hc' sz]] := e052_line_hole hc.
by exists c'; split; [exact: hc' | rewrite sz].
Qed.

(** ** e052, VERIFIED: the edge is e052_modulo_wall applied to (H1) and (H2). *)
Theorem four_family_free_logarithmic_treewidth_implies_even_hole_kt_free_logarithmic_treewidth :
  four_family_free_logarithmic_treewidth_statement ->
  even_hole_kt_free_logarithmic_treewidth_statement.
Proof. exact: (e052_modulo_wall (@e052_wall_even_hole) (@e052_line_even_hole)). Qed.

(** ** Candidate edges ****************************************************)


(*@EDGE from=four_family_free_logarithmic_treewidth_statement to=even_hole_kt_free_logarithmic_treewidth_statement kind=implies status=verified proof=four_family_free_logarithmic_treewidth_implies_even_hole_kt_free_logarithmic_treewidth cite="gc:e052" note="Rocq-only, by e052_modulo_wall (this file) and its two wall containments, both proved here. (H1) e052_wall_even_hole: every subdivision W of x220_wall s, s >= 5, has an even hole. The 15-vertex theta of x220_wall 5 (branch vertices (2,1) and (2,3), paths of lengths 2, 4 and 10) gives three holes on 6, 12 and 14 vertices (by computation), carried into x220_wall s by an induced embedding and into W by kch_hole (fch_hole generalised to holes of any length: the image of a hole of K under an exact subdiv_model is a hole). Each theta edge lies on two of the three cycles, so the three image sizes add up to an even number and one hole is even. (H2) e052_line_even_hole: a hole on n >= 4 vertices of W gives the hole of its n edges in sline_graph W (e052_line_hole), so no prism is needed." *)

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
Print Assumptions kch_hole.
Print Assumptions e052_wall_even_hole.
Print Assumptions e052_line_even_hole.
Print Assumptions four_family_free_logarithmic_treewidth_implies_even_hole_kt_free_logarithmic_treewidth.
