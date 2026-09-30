(** * Minor.foundations.hole_containments -- even holes inside the forbidden configurations

    The X27 / X42 / X220 rows forbid even HOLES ([x27_hole], an induced cycle on more
    than three vertices), while the rows they are compared with forbid CONFIGURATIONS
    (an induced [C_4], an induced ['K_s,s], an induced theta, an induced prism).  Every
    corpus argument between those rows needs the containments

      "this configuration contains an even hole"

    together with the transport of a hole along an [isubgraph] (an induced copy of a
    graph with an even hole has an even hole).  This file collects them, on top of one
    piece of shared machinery:

    - [spairs s], the list of CONSECUTIVE PAIRS of [s].  Both [sd_consec]
      (foundations/containment.v) and [x27_consecutive_in_cycle]
      (conjectures/X27.v) are membership in a list of consecutive pairs -- of a path in
      the first case, of a cyclic rotation in the second -- and [spairs_cat_mid] is the
      one equation that lets a cycle assembled from several subdivision paths inherit
      its chordlessness from those paths.
    - [four_cycle_hole] : four vertices carrying the four cycle edges and neither
      diagonal form a hole.  This settles the [C_4] and the ['K_s,s] containment
      outright ([KB_even_hole]).
    - [isubgraph_hole] : holes transport along induced copies.
    - [fch_hole] : the cycle obtained by concatenating the four subdivision paths along
      an INDUCED 4-cycle of the model graph of a [subdiv_model] is a hole of the host,
      of length [4] plus the sum of the four path sizes ([fch_size]).  This is the
      shared engine for the theta and the prism: a theta is a subdivision of ['K_2,3]
      and a prism one of the 3-prism, and in both model graphs the configuration used
      by the parity argument is an induced 4-cycle. *)

From GTBase Require Export base.
From Minor.foundations Require Import containment.
From Minor.conjectures Require Import X27 X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Consecutive pairs of a sequence ************************************)

Fixpoint spairs (T : Type) (s : seq T) : seq (T * T) :=
  match s with
  | x :: ((y :: _) as s') => (x, y) :: spairs s'
  | _ => [::]
  end.

Lemma spairs_cons (T : Type) (x y : T) (s : seq T) :
  spairs (x :: y :: s) = (x, y) :: spairs (y :: s).
Proof. by []. Qed.

Lemma spairsE (T : Type) (s : seq T) : spairs s = zip s (behead s).
Proof.
elim: s => [|x s IH] //; case: s IH => [|y s] IH //.
by rewrite spairs_cons IH.
Qed.

(** The one equation behind every chordlessness proof below: cutting a sequence at an
    interior vertex splits its consecutive pairs. *)
Lemma spairs_cat_mid (T : Type) (s : seq T) (b : T) (q : seq T) :
  spairs (s ++ b :: q) = spairs (rcons s b) ++ spairs (b :: q).
Proof.
elim: s => [|x s IH] //; case: s IH => [|y s] IH //.
rewrite cat_cons rcons_cons in IH.
by rewrite !rcons_cons !spairs_cons cat_cons IH.
Qed.

Lemma spairs_rcons2 (T : Type) (s : seq T) (a b : T) :
  spairs (rcons (rcons s a) b) = spairs (rcons s a) ++ [:: (a, b)].
Proof.
elim: s => [|x s IH] //; case: s IH => [|y s] IH //.
rewrite !rcons_cons in IH.
by rewrite !rcons_cons !spairs_cons cat_cons IH.
Qed.

Lemma spairs_closeE (T : Type) (z : T) (s : seq T) (x : T) :
  spairs (x :: s ++ [:: z]) = zip (x :: s) (s ++ [:: z]).
Proof.
elim: s x => [|y s IH] x //.
by rewrite cat_cons spairs_cons IH.
Qed.

Lemma mem_spairs (T : eqType) (s : seq T) (x y : T) :
  (x, y) \in spairs s -> (x \in s) && (y \in s).
Proof.
elim: s => [|a s IH] //; case: s IH => [|b s] IH // h.
rewrite spairs_cons in_cons xpair_eqE in h.
case/orP: h => [/andP[/eqP-> /eqP->]|hin].
- by rewrite mem_head in_cons mem_head orbT.
- case/andP: (IH hin) => hx hy; apply/andP; split.
  + by rewrite in_cons hx orbT.
  + by rewrite in_cons hy orbT.
Qed.

Lemma mem_spairs_rev (T : eqType) (s : seq T) (x y : T) :
  ((x, y) \in spairs (rev s)) = ((y, x) \in spairs s).
Proof.
elim: s => [|a s IH] //; case: s IH => [|b s] IH //.
rewrite spairs_cons !rev_cons spairs_rcons2 -rev_cons mem_cat IH.
by rewrite !inE !xpair_eqE andbC orbC.
Qed.

(** *** The two consecutiveness predicates, in [spairs] form *)

Lemma sd_consec_spairs (G : sgraph) (a b : G) (p : seq G) (x y : G) :
  sd_consec a b p x y
  = ((x, y) \in spairs (a :: rcons p b)) || ((y, x) \in spairs (a :: rcons p b)).
Proof. by rewrite /sd_consec !spairsE. Qed.

Lemma sd_consec_sym (G : sgraph) (a b : G) (p : seq G) (x y : G) :
  sd_consec a b p x y = sd_consec b a (rev p) x y.
Proof.
rewrite !sd_consec_spairs.
have -> : b :: rcons (rev p) a = rev (a :: rcons p b) by rewrite rev_cons rev_rcons.
by rewrite !mem_spairs_rev orbC.
Qed.

Lemma consec_spairs (G : sgraph) (a : G) (s : seq G) (x y : G) :
  x27_consecutive_in_cycle (a :: s) x y
  = ((x, y) \in spairs (a :: s ++ [:: a])) || ((y, x) \in spairs (a :: s ++ [:: a])).
Proof. by rewrite /x27_consecutive_in_cycle rot1_cons -cats1 spairs_closeE. Qed.

(** ** Four vertices with the four cycle edges and no diagonal form a hole ***)

Lemma four_cycle_hole (G : sgraph) (a b c d : G) :
  a -- b -> b -- c -> c -- d -> d -- a ->
  ~~ (a -- c) -> ~~ (b -- d) -> a != c -> b != d ->
  x27_hole [:: a; b; c; d].
Proof.
move=> ab bc cd da nac nbd ac bd.
have e1 := sg_edgeNeq ab; have e2 := sg_edgeNeq bc; have e3 := sg_edgeNeq cd.
have e4 : (a == d) = false by rewrite eq_sym; exact: sg_edgeNeq da.
have e5 : (a == c) = false by exact/negbTE.
have e6 : (b == d) = false by exact/negbTE.
split; first by rewrite /ucycle /= ab bc cd da !inE e1 e2 e3 e4 e5 e6.
split => // x y hx hy xy nxy.
suff h : ((x, y) \in [:: (a, b); (b, c); (c, d); (d, a)])
      || ((y, x) \in [:: (a, b); (b, c); (c, d); (d, a)]).
  by rewrite /x27_consecutive_in_cycle /=.
have nac' : ~~ (c -- a) by rewrite sgP.
have nbd' : ~~ (d -- b) by rewrite sgP.
move: hx hy xy nxy; rewrite !inE -!orbA.
case/or4P => /eqP->; case/or4P => /eqP-> xy nxy;
  rewrite ?inE ?xpair_eqE ?eqxx ?andbT ?orbT;
  first [ done
        | by rewrite eqxx in nxy
        | by rewrite xy in nac
        | by rewrite xy in nbd
        | by rewrite xy in nac'
        | by rewrite xy in nbd' ].
Qed.

(** ** Transport of a hole along an induced copy **************************)

Lemma mem_zip_map (T1 T2 : eqType) (f : T1 -> T2) (s t : seq T1) (a b : T1) :
  (a, b) \in zip s t -> (f a, f b) \in zip (map f s) (map f t).
Proof.
elim: s t => [|x s IH] [|y t] //= h.
rewrite in_cons xpair_eqE; rewrite in_cons xpair_eqE in h.
case/orP: h => [/andP[/eqP-> /eqP->]|/IH ->]; last by rewrite orbT.
by rewrite !eqxx.
Qed.

Lemma isubgraph_hole (G H : sgraph) (i : H ⇀ G) (c : seq H) :
  x27_hole c -> x27_hole [seq i x | x <- c].
Proof.
case=> [/andP[cyc uc] [sz ind]].
have iinj : injective (isubgraph_fun i) by exact: isubgraph_inj i.
have imono : forall x y : H, (i x -- i y) = (x -- y) by move=> x y; rewrite isubgraph_mono.
have rel_eq : relpre (isubgraph_fun i) (@sedge G) =2 (@sedge H).
  by move=> x y; rewrite /relpre /= imono.
split.
  apply/andP; split; last by rewrite (map_inj_uniq iinj).
  by rewrite cycle_map (eq_cycle rel_eq).
split; first by rewrite size_map.
move=> x y /mapP[u hu ->] /mapP[v hv ->]; rewrite imono => uv.
rewrite (inj_eq (isubgraph_inj i)) => nuv.
have := ind u v hu hv uv nuv; rewrite /x27_consecutive_in_cycle -map_rot.
by case/orP => h; apply/orP; [left|right]; exact: mem_zip_map.
Qed.

(** ** Small set and clique toolkit ***************************************)

Lemma sub_card_exact (T : finType) (A : {set T}) (n : nat) :
  n <= #|A| -> exists2 B : {set T}, B \subset A & #|B| = n.
Proof.
move=> nA; exists [set x in take n (enum A)].
  by apply/subsetP => x; rewrite inE => /mem_take; rewrite mem_enum.
rewrite cardsE (card_uniqP _); last by apply: take_uniq; exact: enum_uniq.
by rewrite size_takel // -cardE.
Qed.

Lemma clique_sub (G : sgraph) (S T : {set G}) : clique S -> T \subset S -> clique T.
Proof. by move=> cS /subsetP sub x y hx hy; apply: cS; apply: sub. Qed.

(** An induced copy of ['K_t] is a clique on [t] vertices. *)
Lemma isubgraph_K_clique (G : sgraph) (t : nat) (i : ('K_t) ⇀ G) :
  exists2 S : {set G}, clique S & #|S| = t.
Proof.
exists [set i x | x : ('K_t)].
  move=> u v /imsetP[x _ ->] /imsetP[y _ ->] xy.
  by rewrite isubgraph_mono /edge_rel/= -(inj_eq (isubgraph_inj i)).
by rewrite card_imset ?card_ord //; exact: isubgraph_inj i.
Qed.

(** ['K_s,s] with [s >= 2] carries a four-cycle without diagonals, so an induced copy
    of it in [G] yields an even hole of [G]. *)
Lemma KB_even_hole (G : sgraph) (s : nat) (i : (KB s s) ⇀ G) :
  2 <= s -> exists c : seq G, x27_hole c /\ ~~ odd (size c).
Proof.
move=> s2.
have lt0 : 0 < s by apply: leq_trans s2.
have E : forall u v : KB s s, (i u -- i v) = (u -- v).
  by move=> u v; rewrite isubgraph_mono.
have D : forall u v : KB s s, (i u == i v) = (u == v).
  by move=> u v; rewrite (inj_eq (isubgraph_inj i)).
exists [:: i (inl (Ordinal lt0)); i (inr (Ordinal lt0));
           i (inl (Ordinal s2)); i (inr (Ordinal s2))]; split=> //.
by apply: four_cycle_hole; rewrite ?E ?D.
Qed.

(** An induced four-cycle is an even hole. *)
Lemma C4_even_hole (G : sgraph) (i : (cycle_graph 4) ⇀ G) :
  exists c : seq G, x27_hole c /\ ~~ odd (size c).
Proof.
have E : forall u v : cycle_graph 4, (i u -- i v) = (u -- v).
  by move=> u v; rewrite isubgraph_mono.
have D : forall u v : cycle_graph 4, (i u == i v) = (u == v).
  by move=> u v; rewrite (inj_eq (isubgraph_inj i)).
exists [:: i (@Ordinal 4 0 isT); i (@Ordinal 4 1 isT);
           i (@Ordinal 4 2 isT); i (@Ordinal 4 3 isT)]; split=> //.
by apply: four_cycle_hole; rewrite ?E ?D.
Qed.

(** ** Generic helpers on two-element sets ********************************)

Lemma set2_neql (T : finType) (u v u' v' : T) :
  u != u' -> u != v' -> [set u; v] != [set u'; v'].
Proof.
move=> h1 h2; apply/eqP => e.
have : u \in [set u'; v'] by rewrite -e !inE eqxx.
by rewrite !inE (negbTE h1) (negbTE h2).
Qed.

Lemma set2_neqr (T : finType) (u v u' v' : T) :
  v != u' -> v != v' -> [set u; v] != [set u'; v'].
Proof. by move=> h1 h2; rewrite setUC; exact: set2_neql. Qed.

Lemma uniq_cat2 (T : eqType) (s t : seq T) :
  uniq s -> uniq t -> (forall z : T, z \in t -> z \notin s) -> uniq (s ++ t).
Proof.
move=> us ut h; rewrite cat_uniq us ut /= andbT.
by apply/hasPn => z hz; exact: h.
Qed.

(** ** The hole along an induced 4-cycle of the model graph ****************

    [m] is a subdivision model of [K] inside [G] and [w0 -- w1 -- w2 -- w3 -- w0]
    is an INDUCED 4-cycle of [K].  Concatenating the four subdivision paths gives a
    hole of [G] whose length is [4] plus the sum of the four path sizes. *)

Section FourCycleModel.
Variables (K G : sgraph) (m : subdiv_model K G).
Hypothesis rep : subdiv_rep m.
Variables w0 w1 w2 w3 : K.
Hypothesis e01 : w0 -- w1.
Hypothesis e12 : w1 -- w2.
Hypothesis e23 : w2 -- w3.
Hypothesis e30 : w3 -- w0.
Hypothesis n02 : ~~ (w0 -- w2).
Hypothesis n13 : ~~ (w1 -- w3).
Hypothesis d02 : w0 != w2.
Hypothesis d13 : w1 != w3.

Local Notation B := (sdm_branch m).
Local Notation P := (sdm_path m).

Definition fch_cycle : seq G :=
  B w0 :: P w0 w1 ++ B w1 :: P w1 w2 ++ B w2 :: P w2 w3 ++ B w3 :: P w3 w0.

(** *** Distinctness of the four branch vertices *)

Lemma fch_d01 : w0 != w1. Proof. by rewrite (sg_edgeNeq e01). Qed.
Lemma fch_d12 : w1 != w2. Proof. by rewrite (sg_edgeNeq e12). Qed.
Lemma fch_d23 : w2 != w3. Proof. by rewrite (sg_edgeNeq e23). Qed.
Lemma fch_d30 : w3 != w0. Proof. by rewrite (sg_edgeNeq e30). Qed.

(** *** Avoidance and disjointness, in usable form *)

Lemma fch_avoid (u v w : K) : u -- v -> B w \notin P u v.
Proof.
move=> uv; apply/negP => h.
by move: (@sdm_avoid K G m u v w (B w) uv h); rewrite eqxx.
Qed.

Lemma fch_disj (u v u' v' : K) (z : G) :
  u -- v -> u' -- v' -> [set u; v] != [set u'; v'] ->
  z \in P u v -> z \notin P u' v'.
Proof.
move=> uv u'v' ne hz; apply/negP => hz'.
by rewrite (@sdm_disj K G m u v u' v' z uv u'v' hz hz') eqxx in ne.
Qed.

(** *** Membership in the cycle *)

Lemma fch_memE (z : G) : (z \in fch_cycle) =
  (z == B w0) || (z \in P w0 w1) || (z == B w1) || (z \in P w1 w2) ||
  (z == B w2) || (z \in P w2 w3) || (z == B w3) || (z \in P w3 w0).
Proof.
rewrite /fch_cycle; do 4!(rewrite ?in_cons ?mem_cat).
by rewrite -!orbA.
Qed.

Lemma fch_branch_in (u : K) : B u \in fch_cycle -> u \in [:: w0; w1; w2; w3].
Proof.
move=> h; rewrite !inE.
move: h; rewrite fch_memE.
rewrite (negbTE (fch_avoid u e01)) (negbTE (fch_avoid u e12)).
rewrite (negbTE (fch_avoid u e23)) (negbTE (fch_avoid u e30)).
by rewrite !(inj_eq (@sdm_inj K G m)) -!orbA !orFb orbF.
Qed.

Lemma fch_foreign_path (u v : K) (z : G) :
  u -- v -> [set u; v] != [set w0; w1] -> [set u; v] != [set w1; w2] ->
  [set u; v] != [set w2; w3] -> [set u; v] != [set w3; w0] ->
  z \in P u v -> z \notin fch_cycle.
Proof.
move=> uv s0 s1 s2 s3 hz; rewrite fch_memE.
rewrite (negbTE (fch_disj uv e01 s0 hz)) (negbTE (fch_disj uv e12 s1 hz)).
rewrite (negbTE (fch_disj uv e23 s2 hz)) (negbTE (fch_disj uv e30 s3 hz)).
have nb : forall w : K, (z == B w) = false.
  by move=> w; apply/negbTE; exact: (@sdm_avoid K G m u v w z uv hz).
by rewrite !nb.
Qed.

Lemma fch_foreign_branch (u : K) :
  u \notin [:: w0; w1; w2; w3] -> B u \notin fch_cycle.
Proof. by apply: contraNN; exact: fch_branch_in. Qed.

(** *** The cycle really is a cycle *)

Lemma sd_path_cat3 (a b c : G) (p q : seq G) :
  path (--) a (rcons p b) -> path (--) b (rcons q c) ->
  path (--) a (rcons (p ++ b :: q) c).
Proof.
move=> h1 h2.
have -> : rcons (p ++ b :: q) c = rcons p b ++ rcons q c.
  by rewrite rcons_cat rcons_cons cat_rcons.
by rewrite cat_path last_rcons h1 h2.
Qed.

Lemma fch_pathP (u v : K) : u -- v -> path (--) (B u) (rcons (P u v) (B v)).
Proof. by move=> uv; case/andP: (sdm_pathP m uv). Qed.

Lemma fch_uniqP (u v : K) : u -- v -> uniq (B u :: rcons (P u v) (B v)).
Proof. by move=> uv; case/andP: (sdm_pathP m uv). Qed.

Lemma fch_cycleP : cycle (--) fch_cycle.
Proof.
rewrite /fch_cycle /=.
apply: sd_path_cat3; first exact: fch_pathP e01.
apply: sd_path_cat3; first exact: fch_pathP e12.
apply: sd_path_cat3; first exact: fch_pathP e23.
exact: fch_pathP e30.
Qed.

(** *** Uniqueness *)

Lemma fch_block_uniq (u v : K) : u -- v -> uniq (B u :: P u v).
Proof.
move=> uv; move: (fch_uniqP uv); rewrite -rcons_cons rcons_uniq.
by case/andP.
Qed.

Lemma fch_blocks_disj (u v u' v' : K) :
  u -- v -> u' -- v' -> u != u' -> [set u; v] != [set u'; v'] ->
  forall z : G, z \in (B u' :: P u' v') -> z \notin (B u :: P u v).
Proof.
move=> uv u'v' uu' su z; rewrite in_cons => /orP[/eqP->|hz].
- rewrite in_cons negb_or (inj_eq (@sdm_inj K G m)) eq_sym uu' /=.
  exact: (fch_avoid u' uv).
- rewrite in_cons negb_or; apply/andP; split.
  + exact: (@sdm_avoid K G m u' v' u z u'v' hz).
  + apply: (fch_disj u'v' uv _ hz).
    by rewrite eq_sym.
Qed.

Lemma fch_blocks_nhas (u v u' v' : K) :
  u -- v -> u' -- v' -> u != u' -> [set u; v] != [set u'; v'] ->
  ~~ has (mem (B u :: P u v)) (B u' :: P u' v').
Proof.
move=> uv u'v' uu' su; apply/hasPn => z hz.
exact: (fch_blocks_disj uv u'v' uu' su).
Qed.

Lemma fch_uniq : uniq fch_cycle.
Proof.
have d03 : w0 != w3 by rewrite eq_sym fch_d30.
have d10 : w1 != w0 by rewrite eq_sym fch_d01.
have d20 : w2 != w0 by rewrite eq_sym d02.
have s0112 := @set2_neql _ w0 w1 w1 w2 fch_d01 d02.
have s0123 := @set2_neql _ w0 w1 w2 w3 d02 d03.
have s0130 := @set2_neqr _ w0 w1 w3 w0 d13 d10.
have s1223 := @set2_neql _ w1 w2 w2 w3 fch_d12 d13.
have s1230 := @set2_neql _ w1 w2 w3 w0 d13 d10.
have s2330 := @set2_neql _ w2 w3 w3 w0 fch_d23 d20.
have blocksE : fch_cycle = (B w0 :: P w0 w1) ++ (B w1 :: P w1 w2)
                           ++ (B w2 :: P w2 w3) ++ (B w3 :: P w3 w0).
  by rewrite /fch_cycle !cat_cons.
rewrite blocksE.
apply: uniq_cat2; first exact: (fch_block_uniq e01).
- apply: uniq_cat2; first exact: (fch_block_uniq e12).
  + apply: uniq_cat2; first exact: (fch_block_uniq e23).
    * exact: (fch_block_uniq e30).
    * exact: (fch_blocks_disj e23 e30 fch_d23 s2330).
  + move=> z; rewrite mem_cat => /orP[hz|hz].
    * exact: (fch_blocks_disj e12 e23 fch_d12 s1223 hz).
    * exact: (fch_blocks_disj e12 e30 d13 s1230 hz).
- move=> z; rewrite !mem_cat => /orP[hz|/orP[hz|hz]].
  + exact: (fch_blocks_disj e01 e12 fch_d01 s0112 hz).
  + exact: (fch_blocks_disj e01 e23 d02 s0123 hz).
  + exact: (fch_blocks_disj e01 e30 d03 s0130 hz).
Qed.

(** *** Chordlessness *)

Lemma cat4_snoc (a0 a1 a2 a3 a4 : G) (p0 p1 p2 p3 : seq G) :
  (a0 :: p0 ++ a1 :: p1 ++ a2 :: p2 ++ a3 :: p3) ++ [:: a4]
  = a0 :: p0 ++ a1 :: p1 ++ a2 :: p2 ++ a3 :: p3 ++ [:: a4].
Proof. by rewrite cat_cons -catA cat_cons -catA cat_cons -catA cat_cons. Qed.

Lemma spairs_4 (a0 a1 a2 a3 a4 : G) (p0 p1 p2 p3 : seq G) :
  spairs (a0 :: p0 ++ a1 :: p1 ++ a2 :: p2 ++ a3 :: p3 ++ [:: a4])
  = spairs (a0 :: rcons p0 a1) ++ spairs (a1 :: rcons p1 a2)
    ++ spairs (a2 :: rcons p2 a3) ++ spairs (a3 :: rcons p3 a4).
Proof.
rewrite -cat_cons spairs_cat_mid rcons_cons.
rewrite -cat_cons spairs_cat_mid rcons_cons.
rewrite -cat_cons spairs_cat_mid rcons_cons.
by rewrite cats1.
Qed.

Lemma fch_consec_intro (x y : G) :
  [|| sd_consec (B w0) (B w1) (P w0 w1) x y, sd_consec (B w1) (B w2) (P w1 w2) x y,
      sd_consec (B w2) (B w3) (P w2 w3) x y | sd_consec (B w3) (B w0) (P w3 w0) x y] ->
  x27_consecutive_in_cycle fch_cycle x y.
Proof.
move=> H.
rewrite /fch_cycle consec_spairs -cat_cons cat4_snoc spairs_4 !mem_cat -!orbA.
move: H; rewrite !sd_consec_spairs.
by case/or4P => /orP[h|h]; rewrite h ?orTb ?orbT.
Qed.

(** The four set inequalities that a model edge outside the cycle enjoys. *)
Lemma fch_set_nel (u v : K) : u \notin [:: w0; w1; w2; w3] ->
  [&& [set u; v] != [set w0; w1], [set u; v] != [set w1; w2],
      [set u; v] != [set w2; w3] & [set u; v] != [set w3; w0]].
Proof.
rewrite !inE !negb_or => /and4P[h0 h1 h2 h3].
by rewrite (@set2_neql _ u v w0 w1 h0 h1) (@set2_neql _ u v w1 w2 h1 h2)
           (@set2_neql _ u v w2 w3 h2 h3) (@set2_neql _ u v w3 w0 h3 h0).
Qed.

Lemma fch_set_ner (u v : K) : v \notin [:: w0; w1; w2; w3] ->
  [&& [set u; v] != [set w0; w1], [set u; v] != [set w1; w2],
      [set u; v] != [set w2; w3] & [set u; v] != [set w3; w0]].
Proof.
rewrite !inE !negb_or => /and4P[h0 h1 h2 h3].
by rewrite (@set2_neqr _ u v w0 w1 h0 h1) (@set2_neqr _ u v w1 w2 h1 h2)
           (@set2_neqr _ u v w2 w3 h2 h3) (@set2_neqr _ u v w3 w0 h3 h0).
Qed.

(** The foreign case: both ends of the realising model edge are cycle vertices. *)
Lemma fch_pair_inW (u v : K) (x y : G) :
  u -- v -> sd_consec (B u) (B v) (P u v) x y ->
  x \in fch_cycle -> y \in fch_cycle -> x != y ->
  (u \in [:: w0; w1; w2; w3]) && (v \in [:: w0; w1; w2; w3]).
Proof.
move=> uv hc hx hy nxy.
apply/andP; split; apply/negPn/negP => hn.
- case/and4P: (fch_set_nel v hn) => s0 s1 s2 s3.
  have out : forall z : G, z \in (B u :: rcons (P u v) (B v)) -> z \in fch_cycle -> z = B v.
    move=> z; rewrite in_cons mem_rcons in_cons => /orP[/eqP->|].
      by move=> hb; rewrite (negbTE (fch_foreign_branch hn)) in hb.
    case/orP => [/eqP->//|hz] hzc.
    by rewrite (negbTE (fch_foreign_path uv s0 s1 s2 s3 hz)) in hzc.
  move: hc; rewrite sd_consec_spairs => /orP[] /mem_spairs /andP[h1 h2].
  + by rewrite (out x h1 hx) (out y h2 hy) eqxx in nxy.
  + by rewrite (out y h1 hy) (out x h2 hx) eqxx in nxy.
- case/and4P: (fch_set_ner u hn) => s0 s1 s2 s3.
  have out : forall z : G, z \in (B u :: rcons (P u v) (B v)) -> z \in fch_cycle -> z = B u.
    move=> z; rewrite in_cons mem_rcons in_cons => /orP[/eqP->//|].
    case/orP => [/eqP->|hz] hzc.
      by rewrite (negbTE (fch_foreign_branch hn)) in hzc.
    by rewrite (negbTE (fch_foreign_path uv s0 s1 s2 s3 hz)) in hzc.
  move: hc; rewrite sd_consec_spairs => /orP[] /mem_spairs /andP[h1 h2].
  + by rewrite (out x h1 hx) (out y h2 hy) eqxx in nxy.
  + by rewrite (out y h1 hy) (out x h2 hx) eqxx in nxy.
Qed.

Lemma fch_chordless (x y : G) :
  x \in fch_cycle -> y \in fch_cycle -> x -- y -> x != y ->
  x27_consecutive_in_cycle fch_cycle x y.
Proof.
move=> hx hy xy nxy.
have m02 : ~~ (w0 -- w2) := n02.
have m13 : ~~ (w1 -- w3) := n13.
have m20 : ~~ (w2 -- w0) by rewrite sg_sym.
have m31 : ~~ (w3 -- w1) by rewrite sg_sym.
have flip : forall (a b : K), a -- b ->
    sd_consec (B b) (B a) (P b a) x y -> sd_consec (B a) (B b) (P a b) x y.
  by move=> a b e h; rewrite sd_consec_sym -(sdm_pathC m e).
case: rep => _ /(_ x y xy) [u [v [uv hc]]].
apply: fch_consec_intro.
case/andP: (fch_pair_inW uv hc hx hy nxy) => hu hv.
move: hu hv uv hc; rewrite !inE.
case/or4P => /eqP->; case/or4P => /eqP-> uv hc;
  first [ by rewrite hc ?orTb ?orbT
        | by rewrite (flip _ _ e01 hc) ?orTb ?orbT
        | by rewrite (flip _ _ e12 hc) ?orTb ?orbT
        | by rewrite (flip _ _ e23 hc) ?orTb ?orbT
        | by rewrite (flip _ _ e30 hc) ?orTb ?orbT
        | by move: uv; rewrite sg_irrefl
        | by rewrite uv in m02
        | by rewrite uv in m20
        | by rewrite uv in m13
        | by rewrite uv in m31 ].
Qed.

Lemma fch_size : size fch_cycle =
  (size (P w0 w1) + size (P w1 w2) + size (P w2 w3) + size (P w3 w0)).+4.
Proof.
rewrite /fch_cycle /=; do 4!(rewrite ?size_cat /=).
by rewrite !addnS !addnA.
Qed.

Lemma fch_hole : x27_hole fch_cycle.
Proof.
split; first by rewrite /ucycle fch_cycleP fch_uniq.
split; last exact: fch_chordless.
by rewrite fch_size !ltnS.
Qed.

End FourCycleModel.

(** A usable form: an induced 4-cycle of the model graph whose four subdivision paths
    have an even total size gives an EVEN hole of the host. *)
Lemma fch_even_hole (K G : sgraph) (m : subdiv_model K G) (w0 w1 w2 w3 : K) :
  subdiv_rep m -> w0 -- w1 -> w1 -- w2 -> w2 -- w3 -> w3 -- w0 ->
  ~~ (w0 -- w2) -> ~~ (w1 -- w3) -> w0 != w2 -> w1 != w3 ->
  ~~ odd (size (sdm_path m w0 w1) + size (sdm_path m w1 w2)
          + size (sdm_path m w2 w3) + size (sdm_path m w3 w0)) ->
  exists c : seq G, x27_hole c /\ ~~ odd (size c).
Proof.
move=> rep e01 e12 e23 e30 n02 n13 d02 d13 par.
exists (fch_cycle m w0 w1 w2 w3); split.
  exact: (fch_hole rep e01 e12 e23 e30 n02 n13 d02 d13).
by rewrite fch_size /= !negbK.
Qed.

(** ** Every theta contains an even hole **********************************

    A THETA is a graph that IS a subdivision of ['K_2,3] ([x220_theta] of
    conjectures/X220.v is literally [is_subdivision_of H (KB 2 3)]).  Write [a0], [a1]
    for the two branch vertices of degree three (the ['I_2] side) and [b j] for the
    three of degree two.  The [j]-th of the three internally disjoint [a0]-[a1] paths
    has length [L j = |P a0 (b j)| + |P (b j) a1| + 2]; two of the three [L j] have the
    same parity, and the corresponding pair of paths is an induced 4-cycle of ['K_2,3]
    ([a0 -- b j -- a1 -- b k -- a0], with the two diagonals absent because ['K_2,3] is
    bipartite), so [fch_even_hole] turns it into an even hole. *)

Lemma subdiv_KB23_even_hole (H : sgraph) :
  is_subdivision_of H (KB 2 3) -> exists c : seq H, x27_hole c /\ ~~ odd (size c).
Proof.
case=> m rep.
pose a0 : KB 2 3 := inl (@Ordinal 2 0 isT).
pose a1 : KB 2 3 := inl (@Ordinal 2 1 isT).
pose F (j : 'I_3) :=
  odd (size (sdm_path m a0 (inr j)) + size (sdm_path m (inr j) a1)).
have Lrev : forall j : 'I_3,
    size (sdm_path m a1 (inr j)) + size (sdm_path m (inr j) a0)
    = size (sdm_path m a0 (inr j)) + size (sdm_path m (inr j) a1).
  move=> j; rewrite addnC.
  have e1 : a1 -- (inr j : KB 2 3) by [].
  have e0 : (inr j : KB 2 3) -- a0 by [].
  by rewrite (sdm_pathC m e1) (sdm_pathC m e0) !size_rev.
have main : forall j k : 'I_3, j != k -> F j = F k ->
    exists c : seq H, x27_hole c /\ ~~ odd (size c).
  move=> j k jk par; rewrite /F in par.
  have ej0 : a0 -- (inr j : KB 2 3) by [].
  have ej1 : (inr j : KB 2 3) -- a1 by [].
  have ek1 : a1 -- (inr k : KB 2 3) by [].
  have ek0 : (inr k : KB 2 3) -- a0 by [].
  have na : ~~ ((a0 : KB 2 3) -- a1) by [].
  have nb : ~~ ((inr j : KB 2 3) -- inr k) by [].
  have da : (a0 : KB 2 3) != a1 by [].
  have db : (inr j : KB 2 3) != inr k by rewrite /=.
  apply: (fch_even_hole rep ej0 ej1 ek1 ek0 na nb da db).
  by rewrite -addnA (Lrev k) oddD par addbb.
pose o0 := @Ordinal 3 0 isT; pose o1 := @Ordinal 3 1 isT; pose o2 := @Ordinal 3 2 isT.
have [p01|n01] := boolP (F o0 == F o1).
  apply: (main o0 o1); first by [].
  by apply/eqP.
have [p02|n02] := boolP (F o0 == F o2).
  apply: (main o0 o2); first by [].
  by apply/eqP.
apply: (main o1 o2); first by [].
by move: n01 n02; case: (F o0); case: (F o1); case: (F o2).
Qed.

(** ** Every prism contains an even hole **********************************

    A PRISM ([x220_prism] of conjectures/X220.v) is a subdivision of the 3-prism
    [x220_prism3] in which the six TRIANGLE edges stay unsubdivided, so only the three
    matching edges [(0,3)], [(1,4)], [(2,5)] become paths.  Two of those three paths
    have interiors of the same parity; together with the two triangle edges joining
    their ends they form an induced 4-cycle of [x220_prism3] -- e.g.
    [0 -- 3 -- 4 -- 1 -- 0], whose diagonals [0 -- 4] and [3 -- 1] are not edges of the
    3-prism -- and the resulting hole has even length. *)

Lemma prism_even_hole (H : sgraph) :
  x220_prism H -> exists c : seq H, x27_hole c /\ ~~ odd (size c).
Proof.
case=> m [rep tri].
have revs : forall u v : x220_prism3, u -- v ->
    size (sdm_path m v u) = size (sdm_path m u v).
  by move=> u v uv; rewrite (sdm_pathC m uv) size_rev.
have main : forall a b c d : x220_prism3, a -- b -> b -- c -> c -- d -> d -- a ->
    ~~ (a -- c) -> ~~ (b -- d) -> a != c -> b != d ->
    sdm_path m b c = [::] -> sdm_path m d a = [::] ->
    odd (size (sdm_path m a b)) = odd (size (sdm_path m c d)) ->
    exists q : seq H, x27_hole q /\ ~~ odd (size q).
  move=> a b c d e1 e2 e3 e4 na nb da db p1 p2 par.
  apply: (fch_even_hole rep e1 e2 e3 e4 na nb da db).
  by rewrite p1 p2 /= !addn0 oddD par addbb.
pose n0 := @Ordinal 6 0 isT; pose n1 := @Ordinal 6 1 isT.
pose n2 := @Ordinal 6 2 isT; pose n3 := @Ordinal 6 3 isT.
pose n4 := @Ordinal 6 4 isT; pose n5 := @Ordinal 6 5 isT.
pose F03 := odd (size (sdm_path m n0 n3)).
pose F14 := odd (size (sdm_path m n1 n4)).
pose F25 := odd (size (sdm_path m n2 n5)).
have [p1|q1] := boolP (F03 == F14).
  have e1 : (n0 : x220_prism3) -- n3 by [].
  have e2 : (n3 : x220_prism3) -- n4 by [].
  have e3 : (n4 : x220_prism3) -- n1 by [].
  have e4 : (n1 : x220_prism3) -- n0 by [].
  apply: (main n0 n3 n4 n1 e1 e2 e3 e4) => //.
  - exact: (tri n3 n4 e2 isT).
  - exact: (tri n1 n0 e4 isT).
  - by rewrite (revs n1 n4 e3); apply/eqP.
have [p2|q2] := boolP (F03 == F25).
  have e1 : (n0 : x220_prism3) -- n3 by [].
  have e2 : (n3 : x220_prism3) -- n5 by [].
  have e3 : (n5 : x220_prism3) -- n2 by [].
  have e4 : (n2 : x220_prism3) -- n0 by [].
  apply: (main n0 n3 n5 n2 e1 e2 e3 e4) => //.
  - exact: (tri n3 n5 e2 isT).
  - exact: (tri n2 n0 e4 isT).
  - by rewrite (revs n2 n5 e3); apply/eqP.
have e1 : (n1 : x220_prism3) -- n4 by [].
have e2 : (n4 : x220_prism3) -- n5 by [].
have e3 : (n5 : x220_prism3) -- n2 by [].
have e4 : (n2 : x220_prism3) -- n1 by [].
apply: (main n1 n4 n5 n2 e1 e2 e3 e4) => //.
- exact: (tri n4 n5 e2 isT).
- exact: (tri n2 n1 e4 isT).
- rewrite (revs n2 n5 e3) -/F14 -/F25.
  by move: q1 q2; case: F03; case: F14; case: F25.
Qed.
