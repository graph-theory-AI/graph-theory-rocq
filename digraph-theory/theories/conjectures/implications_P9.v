(** * Digraph.conjectures.implications_P9 — milestone P9 implication/refutation edges

    Machine-checked implication EDGES between the 20 P9 [_statement] nodes of
    [P9.v]. Following the convention of [implications.v]/[implications2.v], every
    scheduled edge would be a *relative* theorem [Theorem A_statement -> B_statement]
    provable WITHOUT resolving (proving/refuting) either endpoint.

    POLICY (OPG_FULL_FORMALIZATION_PLAN.md §6): schedule a [Qed]-closed
    [Theorem A_implies_B] ONLY for edges whose status is *verified-literature*; a
    *candidate* edge must first be re-derived and is recorded as an annotation only
    (the Qed gate decides whether it is promoted); a *refuted-direction* edge is
    NEVER asserted as a global negation.

    RESULT OF THE AUDIT.  The 20 P9 nodes are mutually-independent open directed
    problems (the directed gap-closure milestone).  Plan §6 lists NO verified
    directed implication edges and states "Directed edges stay inside digraph-theory
    (its existing, already Qed-closed edges); do not assert new shaky CH⟹Seymour-type
    edges".  We re-examined the closest structural pairs and confirm that NONE close
    under their exact [P9.v] formulations:

      • Row 7 [partitioning_planar_digraphs_statement] vs
        Row 20 [large_acyclic_induced_subdigraph_in_a_planar_oriente_statement].
        These share IDENTICAL hypotheses (loopless oriented digraph whose underlying
        simple graph is [planar_sg]).  A 2-partition into two acyclic induced
        subdigraphs (Row 7) yields, by pigeonhole, an acyclic induced subdigraph of
        order ≥ ⌈|V|/2⌉ — but Row 20 demands order ≥ (3/5)|V| ([5·#S ≥ 3·#V]).  Since
        1/2 < 3/5 the implication does NOT close; it is a strict weakening, not an
        edge.  (Recorded as a candidate that FAILS the gate — never scheduled.)

      • Row 14 [decomposing_k_arc_strong_tournament_into_k_spanning_statement] vs
        Row 13 [arc_disjoint_out_branching_and_in_branching_statement].
        Row 14 gives, for a [k]-arc-strong TOURNAMENT, [k] arc-disjoint spanning
        strong subdigraphs; via Edmonds' branching theorem each strong spanning
        subdigraph carries an out-branching (and one carries an in-branching), so for
        k = 2 a tournament gets arc-disjoint out-/in-branchings.  But Row 13 is
        quantified over ALL [diGraphType] with a SINGLE existential [k]; Row 14 is
        tournament-only.  The formalized edge therefore cannot close (domain +
        quantifier mismatch); the bridge (Edmonds) is external/unformalised.

      • Row 18 [oriented_trees_in_n_chromatic_digraphs_statement] (Burr) vs
        Row 5 [antidirected_trees_in_digraphs_statement].  Although every
        [antidirected_tree] is an [oriented_tree], the two hypotheses are
        incomparable: Burr's is [2k−2 ≤ χ(underlying D)] while Row 5's is the
        arc-count [(k−2)·|V| < nb_arcs D].  Neither bridge holds — a dense graph can
        have χ = 2 (complete bipartite), and a high-χ graph can have few arcs (a
        small critical subgraph).  So there is NO implication in EITHER direction;
        this is a thematic relation only and is deliberately NOT recorded as an edge.

    UPDATE (wave E3).  Two verified edges ARE now scheduled.  Hoàng-Reed implies
    Caccetta-Häggkvist (corpus e172, a row of conjectures/classic_core.v), by the
    counting step [foundations/cycles.v: laminar_sum_bound].  Bang-Jensen-Yeo SAD
    (conjectures/sad.v) implies Row 13 (corpus e103), without Edmonds (see there).  A third:
    X53's bipartite out-degree statement implies Caccetta-Haggkvist (corpus e101), by the
    bipartite double cover (see there).

    Apart from them this file schedules no verified [Qed] edge and carries only the one
    machine-readable candidate annotation below (proved=false).  Adding any of the
    above as a forced theorem would either fail to compile or smuggle in the
    conclusion as an "external" hypothesis — both are forbidden by §6.

    The file still [Require]s [P9], [sad] and [X53] so the [from]/[to] endpoint names
    resolve and the annotations are checked against real constants. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament dipath strong.
From Digraph Require Import classic_core dichromatic packing colouring_variants two_extremal.
From Digraph Require Import interop_graph_theory chi_bounded.
From Digraph Require Import cycles.
From Digraph Require Import P9.
From Digraph Require Import sad.
From Digraph Require Import X53.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Endpoint resolution check (each [from]/[to] below is a real P9 constant). *)
Check partitioning_planar_digraphs_statement : Prop.
Check large_acyclic_induced_subdigraph_in_a_planar_oriente_statement : Prop.
Check decomposing_k_arc_strong_tournament_into_k_spanning_statement : Prop.
Check arc_disjoint_out_branching_and_in_branching_statement : Prop.

(** ** Candidate edges (annotation-only; both FAIL the Qed gate as formalised).

    These are NOT scheduled as theorems: a candidate is promoted to a real
    [Theorem A_implies_B] only once it closes with [Qed], which neither does. *)

(*@EDGE from=partitioning_planar_digraphs_statement to=large_acyclic_induced_subdigraph_in_a_planar_oriente_statement kind=implies status=refuted-direction cite="Neumann-Lara 1985 (2-dicolourability of planar digraphs) vs Albertson-Berman / Borodin-type 3/5 acyclic-set bound" note="REFUTED-DIRECTION (metadata wave M, 2026-09-24): strict weakening: a 2-acyclic partition gives only >= |V|/2 < 3/5. Earlier note: Identical planar hypotheses; pigeonhole on a 2-acyclic-partition yields an acyclic induced subdigraph of order only >= |V|/2, strictly weaker than the required 3/5 (1/2 < 3/5), so the implication does not close. Strict weakening, not a valid edge." *)

(*@EDGE from=decomposing_k_arc_strong_tournament_into_k_spanning_statement to=arc_disjoint_out_branching_and_in_branching_statement kind=implies status=candidate proved=false cite="Bang-Jensen & Yeo, J. Graph Theory 2004 (k-arc-strong tournament decomposition); Edmonds 1973 (arc-disjoint branchings)" note="Row 14 (tournament, all k) gives k arc-disjoint spanning strong subdigraphs; with k=2 Edmonds' branching theorem extracts arc-disjoint out-/in-branchings. But Row 13 quantifies over ALL diGraphType with a single existential k, while Row 14 is tournament-only: domain+quantifier mismatch, and the Edmonds bridge is external/unformalised, so the edge cannot close as formalised." *)

(** ** e172: Hoàng-Reed (P9 row opg:hoand_reed_conjecture) ==> Caccetta-Häggkvist
    (conjectures/classic_core.v, P9 row opg:caccetta_haggkvist_conjecture).

    Hoàng-Reed at k = r gives r directed cycles C_0, ..., C_{r-1} such that C_j
    meets the union of the earlier ones in at most one vertex.  Adding them up
    ([laminar_sum_bound]) the total number of vertices counted with multiplicity
    is at most [#|V| + r - 1], so the shortest of the r cycles has at most
    [(#|V| + r - 1) %/ r] vertices, which is the Caccetta-Häggkvist bound
    (natural-number ceiling of n / r). *)

(*@EDGE from=hoand_reed_statement to=caccetta_haggkvist_statement kind=implies status=verified proof=hoand_reed_implies_caccetta_haggkvist cite="gc:e172" note="Counting: instantiate Hoang-Reed at k = r to get r dicycles whose j-th member meets the union of the earlier ones in at most one vertex; laminar_sum_bound (foundations/cycles.v) turns that into sum of lengths <= #|union| + r - 1 <= n + r - 1, and ltn_ceil then forces some member to have at most (n + r - 1) %/ r vertices. The looplessness hypothesis of the target is not needed; the nonemptiness guard 0 < #|D| and the pointwise delta+ >= r hypothesis are passed on verbatim." *)

Theorem hoand_reed_implies_caccetta_haggkvist :
  hoand_reed_statement -> caccetta_haggkvist_statement.
Proof.
move=> HR D r hD _ hr hdeg.
have [P [packP szP lamP]] := HR D r hD hdeg.
have uP : all uniq P by apply/allP => c /(allP packP); case/and3P => _ _ ->.
have hcard : forall m : nat, #|lam_union P m| <= #|D| by move=> m; exact: max_card.
have hsum := laminar_sum_bound uP lamP (leqnn (size P)).
have hbound : \sum_(i < size P) size (nth [::] P i) <= #|D| + r - 1.
  apply: (leq_trans hsum); rewrite szP -subn1 (addnBA _ hr).
  by apply: leq_sub2r; rewrite leq_add2r; exact: hcard.
have [i hi] : exists i : 'I_(size P),
    size (nth [::] P i) <= (#|D| + r - 1) %/ r.
  apply/existsP; apply: contraT; rewrite negb_exists => /forallP h.
  have hlow : \sum_(i < size P) ((#|D| + r - 1) %/ r).+1
              <= \sum_(i < size P) size (nth [::] P i).
    by apply: leq_sum => i _; rewrite ltnNge; exact: (h i).
  rewrite sum_nat_const card_ord szP in hlow; rewrite szP in hbound.
  move: (leq_trans hlow hbound); rewrite mulnC => hcontra.
  by move: (leq_trans (ltn_ceil (#|D| + r - 1) hr) hcontra); rewrite ltnn.
exists (nth [::] P i); split=> //.
exact: (allP packP _ (mem_nth [::] (ltn_ord i))).
Qed.

(** ** e101: bipartite digraphs with asymmetric out-degrees (X53.v, arxiv:1809.08324#01)
    ==> Caccetta-Haggkvist (classic_core.v, opg:caccetta_haggkvist_conjecture).

    For a digraph [D] with [n] vertices and minimum out-degree [r >= 1], the
    bipartite double cover [e101_dcover D] on [D * bool] has the arcs
    [(v, false) --> (v, true)] and [(u, true) --> (v, false)] for [u --> v].
    Its two sides [false] and [true] are a bipartition with [n] vertices each;
    every [false] vertex has one out-neighbour on the other side and every
    [true] vertex [(u, true)] has [outdeg u >= r].  The source at
    [alpha = r / n], [beta = 1 / n] and [k = (n + r - 1) %/ r] (its condition
    [k alpha + beta > 1] is [n <= k r]) gives a dicycle of the cover with at
    most [2 k] vertices; its [false] vertices, projected to [D], form a dicycle
    of [D] with half as many vertices. *)

Definition e101_dcover (D : diGraphType) : Type := (D * bool)%type.

Section E101Cover.
Variable D : diGraphType.
HB.instance Definition _ := Finite.on (e101_dcover D).
HB.instance Definition _ :=
  HasArc.Build (e101_dcover D)
    (fun x y : D * bool => if x.2 then ~~ y.2 && (x.1 --> y.1) else y.2 && (y.1 == x.1)).
End E101Cover.

Section E101.
Variable D : diGraphType.
Local Notation H := (e101_dcover D).

Lemma e101_arcE (x y : H) :
  (x --> y) = if x.2 then ~~ y.2 && (x.1 --> y.1) else y.2 && (y.1 == x.1).
Proof. by []. Qed.

Definition e101_A : {set H} := [set x : H | ~~ x.2].
Definition e101_B : {set H} := [set x : H | x.2].

Lemma e101_bipartition : x53_bipartition e101_A e101_B.
Proof.
split; [|split].
- by apply/pred0P => x; rewrite /= !inE andNb.
- by apply/setP => x; rewrite !inE orNb.
- move=> x y /=; rewrite /edge_rel /= e101_arcE !inE.
  by case: x.2; case: y.2 => //= /andP[].
Qed.

Lemma e101_card_side (b : bool) : #|[set x : H | x.2 == b]| = #|D|.
Proof.
have -> : [set x : H | x.2 == b] = [set ((v, b) : H) | v : D].
  apply/setP => -[v c]; rewrite !inE /=; apply/eqP/imsetP.
    by move=> <-; exists v.
  by case=> w _ [_ ->].
by rewrite card_imset ?cardsT // => v w [].
Qed.

Lemma e101_cardA : #|e101_A| = #|D|.
Proof.
rewrite -(e101_card_side false); apply: eq_card => x; by rewrite !inE eqbF_neg.
Qed.

Lemma e101_cardB : #|e101_B| = #|D|.
Proof.
rewrite -(e101_card_side true); apply: eq_card => x; by rewrite !inE eqb_id.
Qed.

Lemma e101_out_to_B (v : D) : x53_out_to e101_B ((v, false) : H) = 1.
Proof.
rewrite /x53_out_to -(cards1 ((v, true) : H)); apply: eq_card => -[w c].
rewrite !inE e101_arcE /=.
by case: c; rewrite xpair_eqE /= ?andbT ?andbF.
Qed.

Lemma e101_out_to_A (u : D) : x53_out_to e101_A ((u, true) : H) = outdeg u.
Proof.
rewrite /x53_out_to /outdeg.
have -> : [set w in e101_A | ((u, true) : H) --> w]
          = [set ((v, false) : H) | v in [set w | u --> w]].
  apply/setP => -[v c]; rewrite !inE e101_arcE /=; apply/idP/imsetP.
    by case: c => //= uv; exists v; rewrite ?inE.
  by case=> w; rewrite inE => uw [-> ->].
by rewrite card_imset // => v w [].
Qed.

(** The projection of a dicycle of the cover. *)

Definition e101_proj (s : seq H) : seq D := [seq x.1 | x <- s & ~~ x.2].

Lemma e101_path_proj (y : H) s : path arc y s -> path arc y.1 (e101_proj s).
Proof.
elim: s y => [|z s IH] y //=; rewrite e101_arcE => /andP[yz zs].
rewrite /e101_proj /= -/(e101_proj s).
move: yz; case: (y.2) => /andP[zb yz].
- by rewrite zb /= yz (IH _ zs).
- by rewrite zb /=; move/eqP: yz => <-; exact: IH.
Qed.

Lemma e101_path_count (y : H) s : path arc y s ->
  size s + ~~ (last y s).2 = (count (fun x : H => ~~ x.2) s).*2 + ~~ y.2.
Proof.
elim: s y => [|z s IH] y //=; rewrite e101_arcE => /andP[yz /IH {}IH].
move: yz; case: (y.2) => /andP[zb _].
- by move: IH; rewrite zb /= addSn => ->; rewrite doubleS addn0 addn1.
- by move: IH; rewrite zb /= addSn => ->; rewrite addn0 add0n addn1.
Qed.

(** A dicycle of the cover with a [false] vertex in front projects to a
    dicycle of [D] with half as many vertices. *)
Lemma e101_proj_cycle (u : D) (s : seq H) :
  dicycle (((u, false) : H) :: s) ->
  dicycle (e101_proj (((u, false) : H) :: s))
  /\ (size (e101_proj (((u, false) : H) :: s))).*2 = size s + 1.
Proof.
case/and3P=> _ cyc un; move: cyc; rewrite /cycle => p.
have pp := e101_path_proj p; have pc := e101_path_count p.
have projR : e101_proj (rcons s ((u, false) : H)) = rcons (e101_proj s) u.
  by rewrite /e101_proj filter_rcons /= map_rcons.
rewrite projR /= in pp; rewrite last_rcons size_rcons -cats1 count_cat /= in pc.
have -> : e101_proj (((u, false) : H) :: s) = u :: e101_proj s by [].
split.
  rewrite /dicycle /= pp /=.
  have : uniq (e101_proj (((u, false) : H) :: s)); last by [].
  rewrite /e101_proj map_inj_in_uniq ?filter_uniq // => -[a b] [c d].
  rewrite !mem_filter /= => /andP[hb _] /andP[hd _] ->.
  by move: hb hd; case: b; case: d.
rewrite /= /e101_proj size_map size_filter; move: pc.
by rewrite addn0 !addn1 => -[->].
Qed.

End E101.

(*@EDGE from=bipartite_digraph_asymmetric_outdegree_girth_statement to=caccetta_haggkvist_statement kind=implies status=verified proof=e101_bipartite_digraph_asymmetric_outdegree_girth_implies_caccetta_haggkvist cite="gc:e101" note="Bipartite double cover: H on D * bool with (v, false) --> (v, true) and (u, true) --> (v, false) for u --> v; its sides are a bipartition with n vertices each, one out-neighbour across from a false vertex and outdeg u >= r from (u, true), so the source at alpha = r / n, beta = 1 / n and k = (n + r - 1) %/ r (k alpha + beta > 1 is n <= k r, by ltn_ceil) gives a dicycle of H with at most 2 k vertices; it alternates sides, and its false vertices, projected to D, form a dicycle with half as many. The looplessness hypothesis of the target is not needed." *)

Theorem e101_bipartite_digraph_asymmetric_outdegree_girth_implies_caccetta_haggkvist :
  bipartite_digraph_asymmetric_outdegree_girth_statement -> caccetta_haggkvist_statement.
Proof.
move=> SRC D r hD _ hr hdeg.
set n := #|D|; set k := (n + r - 1) %/ r.
have nkr : n <= k * r.
  have := ltn_ceil (n + r - 1) hr; rewrite -/k mulSn.
  by rewrite ltn_subLR ?addn_gt0 ?hr ?orbT // add1n ltnS [n + r]addnC leq_add2l.
have k1 : 0 < k.
  by move: nkr hD; rewrite -/n; case: (k) => //; rewrite mul0n leqn0 => /eqP ->.
have cond : x53_k_alpha_plus_beta_gt_one k r n 1 n.
  rewrite /x53_k_alpha_plus_beta_gt_one mul1n.
  apply: (leq_ltn_trans (leq_mul nkr (leqnn n))).
  by rewrite -{1}(addn0 (k * r * n)) ltn_add2l.
have Hbeta : forall v : e101_dcover D,
    v \in e101_A D -> 1 * #|e101_B D| <= n * x53_out_to (e101_B D) v.
  move=> -[w b]; rewrite inE /=; case: b => // _.
  by rewrite e101_out_to_B e101_cardB mul1n muln1.
have Halpha : forall v : e101_dcover D,
    v \in e101_B D -> r * #|e101_A D| <= n * x53_out_to (e101_A D) v.
  move=> -[u b]; rewrite inE /=; case: b => // _.
  by rewrite e101_out_to_A e101_cardA mulnC leq_mul2l hdeg orbT.
have Hpos : 0 < #|[set: e101_dcover D]|.
  move/card_gt0P: hD => -[v _]; apply/card_gt0P.
  by exists ((v, false) : e101_dcover D); rewrite inE.
move: Hpos; rewrite cardsT => Hpos.
have [c [dc szc]] := SRC k r n 1 n k1 (conj hr hD) (conj (ltn0Sn 0) hD) cond _
  (e101_A D) (e101_B D) Hpos (e101_bipartition D) Hbeta Halpha.
have [u uc] : exists u : D, ((u, false) : e101_dcover D) \in c.
  have [x xc] : exists x, x \in c.
    by case/and3P: (dc); case: (c) => // x s _ _ _; exists x; rewrite mem_head.
  case Ex: (x.2); last by exists x.1; move: xc; case: x Ex => v [].
  have := dicycle_next dc xc; rewrite e101_arcE Ex => /andP[nb _].
  exists (next c x).1.
  by move: (mem_next c x) xc nb; case: (next c x) => v [] //= -> //.
case/rot_to: uc => i s rotE.
have dcr : dicycle (((u, false) : e101_dcover D) :: s) by rewrite -rotE dicycle_rot.
have [dp sz2] := e101_proj_cycle dcr.
exists (e101_proj (((u, false) : e101_dcover D) :: s)); split => //.
rewrite -leq_double sz2 -mul2n.
have : size (rot i c) <= 2 * k by rewrite size_rot.
by rewrite rotE /= addn1.
Qed.

(** ** e103: Bang-Jensen-Yeo SAD (conjectures/sad.v, row
    opg:arc_disjoint_strongly_connected_spanning_subdigraphs) ==> arc-disjoint
    out-branching and in-branching (P9 Row 13,
    opg:arc_disjoint_out_branching_and_in_branching).

    Take k := K, the SAD constant.  A [karcstrong D K] digraph has at least two
    vertices and every cut of [arc_strong D K], so SAD splits its arcs into disjoint
    spanning strong parts A1 and A2.  Every vertex is reachable from u inside A1: give
    each other vertex the last arc of a shortest A1-walk from u.  These arcs form an
    out-branching at u, acyclic because the walk length increases along them.
    Shortest A2-walks to v give an in-branching at v in the same way.  The
    out-branching uses arcs of A1 and the in-branching arcs of A2, so they share no
    arc.  Edmonds' branching theorem is not needed: each part carries one branching. *)

(*@EDGE from=bang_jensen_yeo_SAD_statement to=arc_disjoint_out_branching_and_in_branching_statement kind=implies status=verified proof=bang_jensen_yeo_SAD_implies_arc_disjoint_out_branching_and_in_branching cite="gc:e103" note="Rocq-only, no Edmonds: take k := K. karcstrong D K gives 0 < #|D| and arc_strong D K (the same cuts), so SAD gives disjoint spanning strong arc sets A1 and A2. Parents on shortest A1-walks from u give an out-branching and on shortest A2-walks to v an in-branching (acyclic: the walk length is strictly monotone along kept arcs). They are arc-disjoint because A1 and A2 are." *)

(** A rank that increases along every arc does not decrease along walks. *)
Lemma connect_rank_mono (T : finType) (e : rel T) (h : T -> nat) :
  (forall x y, e x y -> h x < h y) -> forall x y, connect e x y -> h x <= h y.
Proof.
move=> eh x y /connectP[s]; elim: s x => [|z s IH] x /=; first by move=> _ ->.
by case/andP=> exz pz yl; apply: leq_trans (ltnW (eh _ _ exz)) (IH z pz yl).
Qed.

(** Shortest-walk parents: if every vertex is reachable from [u], each other vertex
    [x] has a predecessor [p x] (an arc from [p x] to [x]) of smaller rank, the rank
    being the length of a shortest walk from [u]. *)
Lemma shortest_walk_parents (T : finType) (e : rel T) (u : T) :
  (forall x, connect e u x) ->
  exists (p : T -> T) (h : T -> nat), forall x, x != u -> e (p x) x /\ h (p x) < h x.
Proof.
move=> conn.
pose P x n := [exists t : n.-tuple T, path e u t && (last u t == x)].
have exP x : exists n, P x n.
  have /connectP[t pt ->] := conn x.
  by exists (size t); apply/existsP; exists (in_tuple t); rewrite /= pt eqxx.
pose h x := ex_minn (exP x).
have hle x n : P x n -> h x <= n.
  by rewrite /h; case: (ex_minnP (exP x)) => m _ /[apply].
have step x : exists y, x != u -> e y x && (h y < h x).
  case: (boolP (x == u)) => [_|xu]; first by exists u.
  rewrite {2}/h; case: (ex_minnP (exP x)) => n /existsP[t /andP[pt /eqP lt]] _.
  move: (size_tuple t) pt lt; case/lastP: (tval t) => [|s y] sz.
    by move=> _ /= lt; move: xu; rewrite -lt eqxx.
  rewrite rcons_path last_rcons => /andP[ps ey] yx.
  exists (last u s) => _; rewrite -yx ey /=.
  have Ps : P (last u s) (size s).
    by apply/existsP; exists (in_tuple s); rewrite /= ps eqxx.
  by apply: leq_ltn_trans (hle _ _ Ps) _; rewrite -sz size_rcons.
have [p hp] := fin_all_exists step.
by exists p, h => x /hp /andP[].
Qed.

(** [karcstrong] gives the hypotheses of the SAD statement: a nonempty digraph, and
    the same cut sizes. *)
Lemma karcstrong_arc_strong (D : diGraphType) (k : nat) :
  karcstrong D k -> 0 < #|D| /\ arc_strong D k.
Proof.
case/andP=> D1 /forallP hk; split; first exact: ltnW.
move=> X X0 XT; have := hk X; rewrite X0 XT /= => /leq_trans; apply.
apply: subset_leq_card; apply/subsetP=> -[a b]; rewrite in_outcutE inE /=.
by case/and3P=> aX bX ab; apply/and3P.
Qed.

(** A spanning strong arc set contains an out-branching at any root. *)
Lemma spanning_strong_out_branching (D : diGraphType) (A : {set D * D}) (u : D) :
  spanning_strong A -> exists f : D -> {set D},
    out_branching f u /\ forall a b, b \in f a -> (a, b) \in A.
Proof.
case=> Asub Aconn.
have [p [h ph]] := shortest_walk_parents (fun x => Aconn u x).
pose f a := [set b | (b != u) && (p b == a)].
have fA a b : b \in f a -> (a, b) \in A.
  by rewrite inE => /andP[bu /eqP <-]; case: (ph b bu).
have fh a b : b \in f a -> h a < h b.
  by rewrite inE => /andP[bu /eqP <-]; case: (ph b bu).
exists f; split=> //; apply/and4P; split.
- apply/forallP=> a; apply/forallP=> b; apply/implyP=> /fA.
  by move/(subsetP Asub); rewrite in_arcsetE.
- rewrite /selindeg (_ : [set a | u \in f a] = set0) ?cards0 //.
  by apply/setP=> a; rewrite !inE eqxx.
- apply/forallP=> v; apply/implyP=> vu.
  rewrite /selindeg (_ : [set a | v \in f a] = [set p v]) ?cards1 //.
  by apply/setP=> a; rewrite !inE vu eq_sym.
- apply/forallP=> a; apply/forallP=> b; apply/implyP.
  rewrite outsel_arcE => /andP[/fh ab _]; apply/negP=> ba.
  have mono (x y : outsel f) : x --> y -> h x < h y.
    by rewrite outsel_arcE => /andP[/fh].
  by have := connect_rank_mono mono ba; rewrite leqNgt ab.
Qed.

(** A spanning strong arc set contains an in-branching at any root (shortest walks
    TO the root). *)
Lemma spanning_strong_in_branching (D : diGraphType) (A : {set D * D}) (v : D) :
  spanning_strong A -> exists g : D -> {set D},
    in_branching g v /\ forall a b, b \in g a -> (a, b) \in A.
Proof.
case=> Asub Aconn.
have conn x : connect [rel a b | subrel_of A b a] v x by rewrite connect_rev; exact: Aconn.
have [p [h ph]] := shortest_walk_parents conn.
pose g a := if a == v then set0 else [set p a].
have gA a b : b \in g a -> (a, b) \in A.
  rewrite /g; case: eqP=> [_|/eqP av]; first by rewrite inE.
  by rewrite inE => /eqP ->; case: (ph a av).
have gh a b : b \in g a -> h b < h a.
  rewrite /g; case: eqP=> [_|/eqP av]; first by rewrite inE.
  by rewrite inE => /eqP ->; case: (ph a av).
exists g; split=> //; apply/and4P; split.
- apply/forallP=> a; apply/forallP=> b; apply/implyP=> /gA.
  by move/(subsetP Asub); rewrite in_arcsetE.
- by rewrite /g eqxx cards0.
- by apply/forallP=> a; apply/implyP=> av; rewrite /g (negbTE av) cards1.
- apply/forallP=> a; apply/forallP=> b; apply/implyP.
  rewrite outsel_arcE => /andP[/gh ba _]; apply/negP=> ab.
  have mono (x y : outsel g) : x --> y -> h y < h x.
    by rewrite outsel_arcE => /andP[/gh].
  have rconn : connect [rel x y | (y : outsel g) --> x] a b by rewrite connect_rev.
  have := connect_rank_mono (e := [rel x y | (y : outsel g) --> x]) (h := h) _ rconn.
  by move=> /(_ (fun x y => mono y x)); rewrite leqNgt ba.
Qed.

Theorem bang_jensen_yeo_SAD_implies_arc_disjoint_out_branching_and_in_branching :
  bang_jensen_yeo_SAD_statement -> arc_disjoint_out_branching_and_in_branching_statement.
Proof.
move=> [K HK]; exists K => D u v kD.
have [D0 DK] := karcstrong_arc_strong kD.
have [A1 [A2 [dis _ s1 s2]]] := HK D D0 DK.
have [f [fo fA]] := spanning_strong_out_branching u s1.
have [g [gi gA]] := spanning_strong_in_branching v s2.
exists f, g; split=> //.
apply/forallP=> a; apply/forallP=> b; apply/negP=> /andP[/fA h1 /gA h2].
by rewrite (disjointFr dis h1) in h2.
Qed.

(** ** Print Assumptions audit *)

Print Assumptions hoand_reed_implies_caccetta_haggkvist.
Print Assumptions bang_jensen_yeo_SAD_implies_arc_disjoint_out_branching_and_in_branching.
Print Assumptions spanning_strong_out_branching.
Print Assumptions spanning_strong_in_branching.
Print Assumptions e101_bipartite_digraph_asymmetric_outdegree_girth_implies_caccetta_haggkvist.
Print Assumptions e101_proj_cycle.
