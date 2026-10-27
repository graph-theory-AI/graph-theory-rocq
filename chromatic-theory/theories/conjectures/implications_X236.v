(** * Chromatic.conjectures.implications_X236 -- dependency-graph EDGES into wave X236.

    Machine-checked implication edges into the X236 statements.  Every SCHEDULED edge is a
    RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving either
    endpoint.  Axiom-free: no [Axiom] / [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): X236.v's Notes say that X142's
    Flandrin row (Delta + 2 for connected graphs other than C_5 with at least 3 vertices)
    implies the row arxiv:1804.06104#00 (Delta + C for every graph with no isolated edge)
    with C = 3, componentwise.  The proof is a strong induction on the number of vertices:
    - a graph with at most 2 vertices and no isolated edge has no edge;
    - a connected graph on at least 3 vertices is C_5 (an explicit colouring with 5 =
      Delta + 3 colours, transported along the isomorphism) or Flandrin's (Delta + 2 colours);
      neighbour-sum colourability with a fixed palette is decidable, which joins the two cases
      without excluded middle;
    - a disconnected graph splits into a component S and its complement, both induced
      subgraphs smaller, closed under adjacency, with no isolated edge and maximum degree at
      most Delta(G); their colourings glue.
    Colourings are transported through an injective, adjacency-reflecting map whose image is
    closed under adjacency (the incident sums are reindexed over the neighbours). *)

From GTBase Require Import base edge_colourings.
From Chromatic.conjectures Require Import X142 X236.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Incident.
Variable G : sgraph.

Lemma x236_set2_sym (a b : G) : [set a; b] = [set b; a].
Proof. by apply/setP => z; rewrite !inE orbC. Qed.

Lemma x236_incident_edgesE (x : G) :
  [set e in E(G) | x \in e] = [set [set x; y] | y in N(x)].
Proof.
apply/setP => e; rewrite inE; apply/andP/imsetP.
- case=> /edgesP[a [b [-> ab]]]; rewrite !inE => /orP[/eqP xa|/eqP xb]; subst x.
    by exists b; rewrite ?in_opn.
  by exists a; [rewrite in_opn sg_sym | exact: x236_set2_sym].
- case=> y; rewrite in_opn => xy ->; split; last by rewrite !inE eqxx.
  by apply/edgesP; exists x, y.
Qed.

Lemma x236_incident_sum (F : {set G} -> nat) (x : G) :
  \sum_(e in [set e in E(G) | x \in e]) F e = \sum_(y in N(x)) F [set x; y].
Proof.
rewrite x236_incident_edgesE big_imset //= => y y'; rewrite !in_opn => xy xy'.
move/setP/(_ y); rewrite !inE eqxx orbT => /esym/orP[/eqP yx|/eqP //].
by move: xy; rewrite yx sgP.
Qed.

End Incident.

Lemma x236_incident_sumE (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (v : G) :
  x142_incident_sum col v = \sum_(y in N(v)) (val (col [set v; y])).+1.
Proof. exact: x236_incident_sum. Qed.

Section Transport.
Variables (H G : sgraph) (k : nat) (h : H -> G).
Variable h_inj : injective h.
Variable h_adj : forall x y : H, (h x -- h y) = (x -- y).
Variable h_closed : forall (x : H) (w : G), h x -- w -> exists y : H, w = h y.
Variables (cH : {set H} -> 'I_k) (cG : {set G} -> 'I_k).
Variable agree : forall x y : H, x -- y -> cG [set h x; h y] = cH [set x; y].

Lemma x236_preim_set2 (x y : H) : h @^-1: [set h x; h y] = [set x; y].
Proof. by apply/setP => z; rewrite !inE !(inj_eq h_inj). Qed.

Lemma x236_neigh_image (x : H) : N(h x) = h @: N(x).
Proof.
apply/setP => w; apply/idP/imsetP.
- rewrite in_opn => xw; have [y ey] := h_closed xw.
  by subst w; exists y => //; rewrite in_opn -h_adj.
- by case=> y; rewrite in_opn => xy ->; rewrite in_opn h_adj.
Qed.

Lemma x236_incident_sum_transport (x : H) : x142_incident_sum cG (h x) = x142_incident_sum cH x.
Proof.
rewrite !x236_incident_sumE x236_neigh_image big_imset /=; first by move=> y y' _ _; exact: h_inj.
by apply: eq_bigr => y; rewrite in_opn => xy; rewrite agree.
Qed.

Lemma x236_proper_transport (x : H) :
  (forall y z : H, x -- y -> x -- z -> y != z -> cH [set x; y] != cH [set x; z]) ->
  forall w1 w2 : G, h x -- w1 -> h x -- w2 -> w1 != w2 -> cG [set h x; w1] != cG [set h x; w2].
Proof.
move=> P w1 w2 x1 x2 ne.
have [y1 e1] := h_closed x1; have [y2 e2] := h_closed x2; subst w1 w2.
rewrite h_adj in x1; rewrite h_adj in x2; rewrite !agree //.
by apply: P => //; apply: contra ne => /eqP ->.
Qed.

End Transport.

Section Basic.
Variable G : sgraph.

Lemma x236_colourable_widen (k k' : nat) : k <= k' -> x142_neighbour_sum_edge_colourable G k -> x142_neighbour_sum_edge_colourable G k'.
Proof.
move=> le [col [P Q]]; exists (fun e => widen_ord le (col e)); split.
- by move=> x y z xy xz yz; apply: contra (P x y z xy xz yz) => /eqP/(congr1 val) /= eq; apply/eqP/val_inj.
- by move=> x y xy; rewrite /x142_incident_sum; under eq_bigr do rewrite /=; under [X in _ != X]eq_bigr do rewrite /=; exact: Q.
Qed.

Lemma x236_colourable_edgeless (k : nat) : 0 < k -> (forall x y : G, ~~ x -- y) -> x142_neighbour_sum_edge_colourable G k.
Proof.
case: k => // k _ none; exists (fun _ => ord0); split.
- by move=> x y z xy; move: (none x y); rewrite xy.
- by move=> x y xy; move: (none x y); rewrite xy.
Qed.

Lemma x236_card_neigh_lt (x : G) : #|N(x)| < #|G|.
Proof.
rewrite -cardsT; apply: proper_card; rewrite properT; apply/eqP => NT.
by move: (in_setT x); rewrite -NT in_opn sgP.
Qed.

Lemma x236_small_no_edges : #|G| <= 2 -> x236_no_isolated_edge G -> forall x y : G, ~~ x -- y.
Proof.
move=> small noiso x y; apply/negP => xy.
have lt (v : G) : #|N(v)| <= 1 by rewrite -ltnS; apply: leq_trans (x236_card_neigh_lt v) small.
by case: (noiso x y xy); rewrite ltnNge lt.
Qed.

End Basic.

Section TransportDelta.
Variables (H G : sgraph) (h : H -> G).
Variable h_inj : injective h.
Variable h_adj : forall x y : H, (h x -- h y) = (x -- y).
Variable h_closed : forall (x : H) (w : G), h x -- w -> exists y : H, w = h y.

Lemma x236_card_neigh_transport (x : H) : #|N(h x)| = #|N(x)|.
Proof. by rewrite (x236_neigh_image h_adj h_closed) card_imset. Qed.

Lemma x236_Delta_transport : Delta H <= Delta G.
Proof.
rewrite /Delta; apply/bigmax_leqP => x _; rewrite -(x236_card_neigh_transport x).
exact: (@leq_bigmax_cond _ predT (fun v : G => #|N(v)|) (h x)).
Qed.

Lemma x236_no_isolated_edge_transport : x236_no_isolated_edge G -> x236_no_isolated_edge H.
Proof.
move=> noiso x y xy; rewrite -!x236_card_neigh_transport; apply: noiso.
by rewrite h_adj.
Qed.

End TransportDelta.

Section Glue.
Variables (G : sgraph) (S : {set G}) (k : nat).
Variable S_closed : forall x y : G, x \in S -> x -- y -> y \in S.

Lemma x236_closedC (x y : G) : x \in ~: S -> x -- y -> y \in ~: S.
Proof.
rewrite !inE => xS xy; apply: contra xS => yS.
by apply: (S_closed yS); rewrite sg_sym.
Qed.

(** The vertex projection of an induced subgraph, named so that it can instantiate [h]. *)
Definition x236_iv (A : {set G}) (x : induced A) : G := val x.

Lemma x236_iv_inj (A : {set G}) : injective (@x236_iv A).
Proof. by move=> x y; rewrite /x236_iv => /val_inj. Qed.

Lemma x236_iv_adj (A : {set G}) (x y : induced A) : (x236_iv x -- x236_iv y) = (x -- y).
Proof. by []. Qed.

Lemma x236_iv_closed (A : {set G}) :
  (forall x y : G, x \in A -> x -- y -> y \in A) ->
  forall (x : induced A) (w : G), x236_iv x -- w -> exists y : induced A, w = x236_iv y.
Proof.
move=> cl x w xw; have wA : w \in A by apply: (cl (val x)); rewrite ?(valP x).
by exists (Sub w wA); rewrite /x236_iv SubK.
Qed.

Lemma x236_iv_Sub (A : {set G}) (x : G) (xA : x \in A) : x236_iv (Sub x xA : induced A) = x.
Proof. by rewrite /x236_iv SubK. Qed.

Variables (c1 : {set induced S} -> 'I_k) (c2 : {set induced (~: S)} -> 'I_k).

Definition x236_glue (e : {set G}) : 'I_k :=
  if e \subset S then c1 (@x236_iv S @^-1: e) else c2 (@x236_iv (~: S) @^-1: e).

Lemma x236_glue1 (x y : induced S) : x -- y -> x236_glue [set x236_iv x; x236_iv y] = c1 [set x; y].
Proof.
move=> _; rewrite /x236_glue subUset !sub1set {1}/x236_iv (valP x) {1}/x236_iv (valP y) /=.
by rewrite (x236_preim_set2 (@x236_iv_inj S)).
Qed.

Lemma x236_glue2 (x y : induced (~: S)) : x -- y -> x236_glue [set x236_iv x; x236_iv y] = c2 [set x; y].
Proof.
move=> _; rewrite /x236_glue subUset !sub1set.
have /negPf -> : x236_iv x \notin S by move: (valP x); rewrite inE.
by rewrite /= (x236_preim_set2 (@x236_iv_inj (~: S))).
Qed.

Lemma x236_glue_colourable :
  proper_edge_colouring c1 -> (forall x y : induced S, x -- y -> x142_incident_sum c1 x != x142_incident_sum c1 y) ->
  proper_edge_colouring c2 -> (forall x y : induced (~: S), x -- y -> x142_incident_sum c2 x != x142_incident_sum c2 y) ->
  x142_neighbour_sum_edge_colourable G k.
Proof.
move=> P1 Q1 P2 Q2; exists x236_glue; split.
- move=> x y z xy xz yz; case: (boolP (x \in S)) => xS.
  + have := x236_proper_transport (@x236_iv_adj S) (x236_iv_closed S_closed) x236_glue1 (x := Sub x xS).
    rewrite x236_iv_Sub; apply => //; exact: P1.
  + have xS' : x \in ~: S by rewrite inE.
    have := x236_proper_transport (@x236_iv_adj (~: S)) (x236_iv_closed x236_closedC) x236_glue2 (x := Sub x xS').
    rewrite x236_iv_Sub; apply => //; exact: P2.
- move=> x y xy; case: (boolP (x \in S)) => xS.
  + have yS : y \in S by exact: S_closed xy.
    have T := x236_incident_sum_transport (@x236_iv_inj S) (@x236_iv_adj S) (x236_iv_closed S_closed) x236_glue1.
    have := T (Sub x xS); have := T (Sub y yS); rewrite !x236_iv_Sub => -> ->.
    by apply: Q1; rewrite -x236_iv_adj !x236_iv_Sub.
  + have xS' : x \in ~: S by rewrite inE.
    have yS' : y \in ~: S by exact: x236_closedC xy.
    have T := x236_incident_sum_transport (@x236_iv_inj (~: S)) (@x236_iv_adj (~: S)) (x236_iv_closed x236_closedC) x236_glue2.
    have := T (Sub x xS'); have := T (Sub y yS'); rewrite !x236_iv_Sub => -> ->.
    by apply: Q2; rewrite -x236_iv_adj !x236_iv_Sub.
Qed.

End Glue.

Section Decide.
Variables (G : sgraph) (k : nat).

Definition x236_properb (f : {set G} -> 'I_k) : bool :=
  [forall x, forall y, forall z, (x -- y) ==> (x -- z) ==> (y != z) ==> (f [set x; y] != f [set x; z])].
Definition x236_nsdb (f : {set G} -> 'I_k) : bool :=
  [forall x, forall y, (x -- y) ==> (x142_incident_sum f x != x142_incident_sum f y)].

Lemma x236_colourableP :
  reflect (x142_neighbour_sum_edge_colourable G k) [exists f : {ffun {set G} -> 'I_k}, x236_properb f && x236_nsdb f].
Proof.
apply: (iffP existsP) => [[f /andP[/forallP P /forallP Q]]|[col [P Q]]].
- exists f; split.
  + move=> x y z xy xz yz; move: (P x) => /forallP/(_ y)/forallP/(_ z).
    by rewrite xy xz yz.
  + by move=> x y xy; move: (Q x) => /forallP/(_ y); rewrite xy.
- exists [ffun e => col e]; apply/andP; split.
  + apply/forallP => x; apply/forallP => y; apply/forallP => z; rewrite !ffunE.
    by apply/implyP => xy; apply/implyP => xz; apply/implyP => yz; exact: P.
  + have E (v : G) : x142_incident_sum [ffun e => col e] v = x142_incident_sum col v.
      by apply: eq_bigr => e _; rewrite ffunE.
    by apply/forallP => x; apply/forallP => y; apply/implyP => xy; rewrite !E; exact: Q.
Qed.

End Decide.

Section DisoTransport.
Import bij.

Lemma x236_colourable_diso (G H : sgraph) (k : nat) : diso G H -> x142_neighbour_sum_edge_colourable H k -> x142_neighbour_sum_edge_colourable G k.
Proof.
move=> i [col [P Q]].
pose h := fun x : H => i^-1 x.
have h_inj : injective h by apply: (can_inj (bijK' i)).
have h_adj (x y : H) : (h x -- h y) = (x -- y) by rewrite /h -(edge_diso i) !bijK'.
have h_closed (x : H) (w : G) : h x -- w -> exists y : H, w = h y.
  by move=> _; exists (i w); rewrite /h bijK.
pose cG := fun e : {set G} => col (h @^-1: e).
have agree (x y : H) : x -- y -> cG [set h x; h y] = col [set x; y].
  by move=> _; rewrite /cG (x236_preim_set2 h_inj).
exists cG; split.
- move=> v y z; rewrite -[v](bijK i) => vy vz yz.
  by apply: (x236_proper_transport h_adj h_closed agree _ vy vz yz); exact: P.
- move=> v w; rewrite -[v](bijK i) -[w](bijK i) => vw.
  rewrite !(x236_incident_sum_transport h_inj h_adj h_closed agree); apply: Q.
  by rewrite -h_adj.
Qed.

End DisoTransport.

Section C5.

Lemma x236_sum_set2 (T : finType) (F : T -> nat) (a b : T) :
  a != b -> \sum_(w in [set a; b]) F w = F a + F b.
Proof. by move=> ab; rewrite big_setU1 ?inE // big_set1. Qed.

Definition x236_c5col (e : {set (cycle_graph 5)}) : 'I_5 := inord ((\sum_(v in e) val v) %% 5).

Lemma x236_c5col2 (x y : (cycle_graph 5)) : x != y -> x236_c5col [set x; y] = inord ((x + y) %% 5).
Proof. by move=> xy; rewrite /x236_c5col (x236_sum_set2 (fun v : (cycle_graph 5) => val v) xy). Qed.

Lemma x236_c5_neigh (v : (cycle_graph 5)) : N(v) = [set inord ((v + 1) %% 5); inord ((v + 4) %% 5)].
Proof.
apply/setP => w; rewrite in_opn !inE.
case: v => [[|[|[|[|[|v]]]]] Hv]; case: w => [[|[|[|[|[|w]]]]] Hw];
  by rewrite /= /cyc_rel /= -?val_eqE /= ?inordK.
Qed.

Definition x236_c5sum (v : (cycle_graph 5)) : nat := nth 0 [:: 7; 6; 5; 4; 8] v.

Lemma x236_c5_incident_sum (v : (cycle_graph 5)) : x142_incident_sum x236_c5col v = x236_c5sum v.
Proof.
rewrite x236_incident_sumE x236_c5_neigh.
by case: v => [[|[|[|[|[|v]]]]] Hv]; rewrite x236_sum_set2 ?x236_c5col2; rewrite /= -?val_eqE /= ?inordK.
Qed.

Lemma x236_c5_colourable : x142_neighbour_sum_edge_colourable (cycle_graph 5) 5.
Proof.
exists x236_c5col; split.
- move=> x y z xy xz yz; rewrite !x236_c5col2 ?(sg_edgeNeq xy) ?(sg_edgeNeq xz) //.
  apply: contra yz => /eqP/(congr1 (@nat_of_ord 5)); rewrite !inordK ?ltn_mod // => /eqP.
  by rewrite eqn_modDl !modn_small ?ltn_ord // => /eqP E; apply/eqP/val_inj.
- move=> x y xy; rewrite !x236_c5_incident_sum; move: (sg_edgeNeq xy); clear xy.
  by case: x => [[|[|[|[|[|x]]]]] Hx]; case: y => [[|[|[|[|[|y]]]]] Hy].
Qed.

Lemma x236_c5_degree (v : (cycle_graph 5)) : #|N(v)| = 2.
Proof.
by rewrite x236_c5_neigh cards2; case: v => [[|[|[|[|[|v]]]]] Hv]; rewrite -?val_eqE /= ?inordK.
Qed.

End C5.

Lemma x236_colourable_C5 (G : sgraph) : inhabited (G ≃ cycle_graph 5) -> x142_neighbour_sum_edge_colourable G (Delta G + 3).
Proof.
case=> i; have D : 2 <= Delta G.
  rewrite -(x236_c5_degree ord0) -(diso_degree (diso_sym i)) /Delta.
  exact: (@leq_bigmax_cond _ predT (fun v : G => #|N(v)|) _ isT).
apply: x236_colourable_widen (x236_colourable_diso i x236_c5_colourable).
by rewrite -[5]/(2 + 3) leq_add2r.
Qed.

Theorem x236_main : flandrin_neighbour_sum_distinguishing_edge_colouring_statement -> forall G : sgraph, x236_no_isolated_edge G -> x142_neighbour_sum_edge_colourable G (Delta G + 3).
Proof.
move=> FL G; move: {2}#|G| (leqnn #|G|) => n; elim: n G => [|n IH] G Gn noiso.
  apply: x236_colourable_edgeless; first by rewrite addn3.
  by apply: x236_small_no_edges => //; exact: leq_trans Gn _.
case: (boolP [forall x : G, forall y : G, connect sedge x y]) =>
  [/forallP conn|/forallPn[x /forallPn[y nxy]]].
- have Gc : connected [set: G] by apply: connectedTI => x y; exact: (forallP (conn x)) y.
  case: (leqP #|G| 2) => G2.
    apply: x236_colourable_edgeless; first by rewrite addn3.
    exact: x236_small_no_edges.
  have [//|ncol] := @x236_colourableP G (Delta G + 3).
  have nC5 : ~ inhabited (G ≃ cycle_graph 5).
    by move=> iso; apply: ncol; exact: x236_colourable_C5.
  exfalso; apply: ncol; apply: x236_colourable_widen (FL G Gc G2 nC5).
  by rewrite leq_add2l.
- pose S := [set z | connect sedge x z].
  have S_closed (a b : G) : a \in S -> a -- b -> b \in S.
    by rewrite !inE => xa ab; exact: connect_trans xa (connect1 ab).
  have xS : x \in S by rewrite inE connect0.
  have yS : y \notin S by rewrite inE.
  have cS : #|induced S| < #|G|.
    rewrite card_sig -cardsT; apply: proper_card; rewrite properT.
    by apply/eqP => ST; move: yS; rewrite ST inE.
  have cC : #|induced (~: S)| < #|G|.
    rewrite card_sig -cardsT; apply: proper_card; rewrite properT.
    by apply/eqP => ST; move: (in_setT x); rewrite -ST inE xS.
  have SC := x236_closedC S_closed.
  have [c1 [P1 Q1]] : x142_neighbour_sum_edge_colourable (induced S) (Delta G + 3).
    apply: x236_colourable_widen (IH _ _ _).
    - by rewrite leq_add2r; exact: x236_Delta_transport (@x236_iv_inj G S) (@x236_iv_adj G S) (x236_iv_closed S_closed).
    - by rewrite -ltnS; exact: leq_trans cS Gn.
    - exact: x236_no_isolated_edge_transport (@x236_iv_inj G S) (@x236_iv_adj G S) (x236_iv_closed S_closed) noiso.
  have [c2 [P2 Q2]] : x142_neighbour_sum_edge_colourable (induced (~: S)) (Delta G + 3).
    apply: x236_colourable_widen (IH _ _ _).
    - by rewrite leq_add2r; exact: x236_Delta_transport (@x236_iv_inj G (~: S)) (@x236_iv_adj G (~: S)) (x236_iv_closed SC).
    - by rewrite -ltnS; exact: leq_trans cC Gn.
    - exact: x236_no_isolated_edge_transport (@x236_iv_inj G (~: S)) (@x236_iv_adj G (~: S)) (x236_iv_closed SC) noiso.
  exact: (x236_glue_colourable S_closed P1 Q1 P2 Q2).
Qed.

(** ** Flandrin et al. (X142) ==> neighbour-sum-distinguishing Delta + C (X236, arxiv:1804.06104#00) *)

(*@EDGE from=flandrin_neighbour_sum_distinguishing_edge_colouring_statement to=nsd_delta_plus_constant_statement kind=implies status=verified proved=true proof=flandrin_neighbour_sum_distinguishing_edge_colouring_implies_nsd_delta_plus_constant note="Rocq-only edge (no corpus relation), stated in X236.v's Notes: Flandrin et al.'s Delta + 2 for connected graphs with at least 3 vertices other than C_5 gives Delta + 3 for every graph with no isolated edge (C = 3), by strong induction on the number of vertices: graphs on at most 2 vertices without an isolated edge have no edge; a connected graph on at least 3 vertices is C_5 (an explicit 5-colouring) or Flandrin's; a disconnected one splits into a component and its complement, whose colourings glue." *)
Theorem flandrin_neighbour_sum_distinguishing_edge_colouring_implies_nsd_delta_plus_constant :
  flandrin_neighbour_sum_distinguishing_edge_colouring_statement -> nsd_delta_plus_constant_statement.
Proof. by move=> FL; exists 3 => G; exact: (x236_main FL). Qed.
