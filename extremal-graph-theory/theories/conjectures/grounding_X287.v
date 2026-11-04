(** * Extremal.conjectures.grounding_X287 -- grounding certificates of wave X287.

    hyp_inhabited and not_trivially_true (the contract form: a variant obtained from the body by deleting one hypothesis
    is false and implies the row) for the one row, and helper_sanity for the wave's two helpers.
    - Helpers: the tables carry the orders 11, 14, 14, 19, 19, 22 and the edge counts 16, 21, 21, 28, 28, 33 of the
      figure files, and each graph has its table's order.
    - Hypotheses: F_11 (x287_bb_graph 0) is 2-connected, triangle-free and subcubic with alpha = 4 < 33/8, checked by
      vm_compute on explicit vertex lists (as grounding_X285's F_14^(1) and grounding_X268's Petersen graph): a
      reachability closure after deleting each vertex, and a branching search for a largest stable set with its
      soundness lemma; the statement then places F_11 among the six.
    - Without "triangle-free" the first clause fails at K_4: 2-connected, cubic, alpha = 1, 8 < 12, and four vertices,
      the order of none of the six. *)

From Extremal.conjectures Require Import X287.
From GTBase Require Import base finite_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** F_11 *)

Definition g287_f11 : sgraph := x287_bb_graph ord0.

Local Notation F := g287_f11.
Local Notation O11 i := (@Ordinal 11 i isT).

Definition g287_fv : seq F :=
  [:: O11 0; O11 1; O11 2; O11 3; O11 4; O11 5; O11 6; O11 7; O11 8; O11 9; O11 10].

Lemma g287_fv_all (x : F) : x \in g287_fv.
Proof. by case: x => -[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]] Hx //=; apply/eqP. Qed.

Lemma g287_fv_uniq : uniq g287_fv.
Proof. by vm_compute. Qed.

Arguments g287_fv : simpl never.

Lemma g287_f11_card : #|F| = 11.
Proof. exact: card_ord. Qed.

Lemma g287_f11_triangle_free : triangle_free F.
Proof.
have h : all (fun x => all (fun y => all (fun z => ~~ [&& x -- y, y -- z & z -- x]) g287_fv) g287_fv) g287_fv.
  by vm_compute.
move=> x y z xy yz zx.
move/allP: h => /(_ x (g287_fv_all x)) /allP /(_ y (g287_fv_all y)) /allP /(_ z (g287_fv_all z)).
by rewrite xy yz zx.
Qed.

Lemma g287_f11_subcubic : subcubic F.
Proof.
have h : all (fun v => size [seq u <- g287_fv | v -- u] <= 3) g287_fv by vm_compute.
move=> v; have e : N(v) =i [seq u <- g287_fv | v -- u].
  by move=> u; rewrite mem_filter g287_fv_all andbT inE.
rewrite (eq_card e) (card_uniqP (filter_uniq _ g287_fv_uniq)).
by move/allP: h => /(_ v (g287_fv_all v)).
Qed.

(* Breadth-first reachability avoiding the vertices of [rem] (as grounding_X285's g285_reach and grounding_X268's
   g268_reach). *)
Fixpoint g287_reach (rem : seq F) (n : nat) (R : seq F) : seq F :=
  if n is n'.+1 then
    g287_reach rem n'
      (R ++ [seq y <- g287_fv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel F x y) R])
  else R.

Lemma g287_reachP (S : {set F}) (rem : seq F) (r : F) :
  (forall y, (y \in S) = (y \in rem)) ->
  forall n R, (forall x, x \in R ->
      x \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: F] :\: S)) (--)) r x) ->
  forall y, y \in g287_reach rem n R ->
    y \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: F] :\: S)) (--)) r y.
Proof.
move=> hS; elim=> [|n IH] R hR y; first exact: hR.
move=> hy; apply: (IH (R ++ [seq y <- g287_fv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel F x y) R])
  _ y hy) => x.
rewrite mem_cat => /orP[/hR // |].
rewrite mem_filter => /andP[/andP[/andP[hx _] /hasP[z hz hzx]] _]; split=> //.
have [hzr hcz] := hR z hz; apply: connect_trans hcz (connect1 _).
by rewrite /preliminaries.restrict_mem /= !inE !hS hzr hx hzx.
Qed.

Definition g287_conn_ok (rem : seq F) : bool :=
  let r := head (O11 0) [seq y <- g287_fv | y \notin rem] in
  let L := g287_reach rem 11 [:: r] in
  all (fun y => (y \in rem) || (y \in L)) g287_fv.

Lemma g287_connected_of (S : {set F}) (rem : seq F) :
  (forall y, (y \in S) = (y \in rem)) -> g287_conn_ok rem -> connected ([set: F] :\: S).
Proof.
move=> hS; rewrite /g287_conn_ok; cbv zeta.
case hf: [seq y <- g287_fv | y \notin rem] => [|r f] hall.
  move=> x y hx _; exfalso; move: hx; rewrite !inE hS andbT => hx.
  by have := mem_filter (fun y => y \notin rem) x g287_fv; rewrite hf hx g287_fv_all in_nil.
have hr : r \notin rem by have := mem_head r f; rewrite -hf mem_filter => /andP[].
apply: (@connected_center _ r) => [y|]; last by rewrite !inE hS hr.
rewrite !inE hS andbT => hy.
have hreach : y \in g287_reach rem 11 [:: r].
  by move/allP: hall => /(_ y (g287_fv_all y)); rewrite (negbTE hy) orFb.
have [] // := @g287_reachP S rem r hS 11 [:: r] _ y hreach.
by move=> x; rewrite inE => /eqP ->; split=> //; exact: connect0.
Qed.

Lemma g287_conn_ok1 : all (fun a => g287_conn_ok [:: a]) g287_fv && g287_conn_ok [::].
Proof. by vm_compute. Qed.

Lemma g287_f11_two_connected : k_connected F 2.
Proof.
split; first by rewrite card_ord.
move=> S hS; have [h1 h0] := andP g287_conn_ok1.
have : #|S| = 0 \/ #|S| = 1 by move: hS; case: #|S| => [|[|n]]; auto.
case=> [/cards0_eq -> | /eqP/cards1P [a ->]].
- by apply: (@g287_connected_of _ [::] _ h0) => y; rewrite !inE.
- by apply: (@g287_connected_of _ [:: a] _ (allP h1 a (g287_fv_all a))) => y; rewrite !inE.
Qed.

Definition g287_nbrs (v : F) : seq F := [seq u <- g287_fv | v -- u].

Lemma g287_nbrsE (v x : F) : (x \in g287_nbrs v) = v -- x.
Proof. by rewrite /g287_nbrs mem_filter g287_fv_all andbT. Qed.

Arguments g287_nbrs : simpl never.

(* Largest stable subsequence of [vs] avoiding [X], by branching on the first vertex (grounding_X285's g285_mis). *)
Fixpoint g287_mis (vs X : seq F) : nat :=
  if vs is v :: r then
    if v \in X then g287_mis r X
    else maxn (g287_mis r X) (g287_mis r (g287_nbrs v ++ X)).+1
  else 0.

Lemma g287_mis_cons (v : F) (r X : seq F) :
  g287_mis (v :: r) X =
    if v \in X then g287_mis r X else maxn (g287_mis r X) (g287_mis r (g287_nbrs v ++ X)).+1.
Proof. by []. Qed.

Lemma g287_misP (vs X T : seq F) :
  uniq T -> {subset T <= vs} -> (forall x y, x \in T -> y \in T -> ~~ x -- y) ->
  (forall x, x \in T -> x \notin X) -> size T <= g287_mis vs X.
Proof.
elim: vs X T => [|v r IH] X T uT sT stT dT.
  by case: T uT sT {stT dT} => [//|t T'] _ /(_ t (mem_head _ _)).
rewrite g287_mis_cons; case vX: (v \in X).
  apply: IH => // x xT; have := sT x xT; rewrite inE => /orP[/eqP xv|//].
  by move: (dT x xT); rewrite xv vX.
rewrite leq_max; case vT: (v \in T); last first.
  apply/orP; left; apply: IH => // x xT; have := sT x xT; rewrite inE => /orP[/eqP xv|//].
  by move: xT; rewrite xv vT.
have sz : size T = (size (rem v T)).+1.
  rewrite size_rem // prednK // lt0n size_eq0; apply/eqP => T0.
  by rewrite T0 in vT.
apply/orP; right; rewrite sz ltnS; apply: IH.
- exact: rem_uniq.
- move=> x; rewrite (mem_rem_uniq _ uT) inE => /andP[xv xT].
  by have := sT x xT; rewrite inE (negbTE xv).
- by move=> x y; rewrite !(mem_rem_uniq _ uT) !inE => /andP[_ xT] /andP[_ yT]; exact: stT.
- move=> x; rewrite (mem_rem_uniq _ uT) inE => /andP[xv xT]; rewrite mem_cat negb_or (dT x xT) andbT.
  by rewrite g287_nbrsE (stT v x vT xT).
Qed.

Lemma g287_mis_f11 : g287_mis g287_fv [::] = 4.
Proof. by vm_compute. Qed.

Lemma g287_f11_alpha : α([set: F]) <= 4.
Proof.
rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ /stableP st].
rewrite cardE -g287_mis_f11; apply: g287_misP.
- exact: enum_uniq.
- by move=> x _; exact: g287_fv_all.
- by move=> x y; rewrite !mem_enum; exact: st.
- by move=> x _; rewrite in_nil.
Qed.

(** helper_sanity: the tables have the orders and edge counts of Figure 1, and each graph has its table's order. *)
Definition g287_helper_claim : Prop :=
  [/\ map (fun t => t.1) x287_bb_tables = [:: 11; 14; 14; 19; 19; 22],
      map (fun t => size t.2) x287_bb_tables = [:: 16; 21; 21; 28; 28; 33] &
      forall i : 'I_6, #|x287_bb_graph i| = nth 0 (map (fun t => t.1) x287_bb_tables) i].

Theorem g287_helper_sanity : g287_helper_claim.
Proof.
split=> //; case=> -[|[|[|[|[|[|n]]]]]] Hi //=; exact: card_ord.
Qed.

(** hyp_inhabited: F_11 meets the four hypotheses, and the statement then places it among the six. *)
Definition g287_bb_hyp_claim : Prop :=
  [/\ k_connected g287_f11 2, triangle_free g287_f11, subcubic g287_f11,
      8 * α([set: g287_f11]) < 3 * #|g287_f11| &
      (bajnok_brinkmann_six_exceptional_graphs_statement ->
         exists i : 'I_6, inhabited (g287_f11 ≃ x287_bb_graph i))].

Lemma g287_f11_sparse : 8 * α([set: g287_f11]) < 3 * #|g287_f11|.
Proof. by rewrite g287_f11_card; apply: leq_ltn_trans (leq_mul (leqnn 8) g287_f11_alpha) _. Qed.

Theorem g287_bb_hyp_inhabited : g287_bb_hyp_claim.
Proof.
split; [exact: g287_f11_two_connected | exact: g287_f11_triangle_free | exact: g287_f11_subcubic
       | exact: g287_f11_sparse |].
by case=> h _ _; apply: h; [exact: g287_f11_two_connected | exact: g287_f11_triangle_free
                            | exact: g287_f11_subcubic | exact: g287_f11_sparse].
Qed.

(** not_trivially_true: without "triangle-free" the first clause fails at K_4 (2-connected, cubic, alpha = 1,
    8 < 12, and 4 vertices, the order of none of the six), and the variant implies the statement. *)
Lemma g287_Kn_stable (N : nat) (S : {set 'K_N}) : stable S -> #|S| <= 1.
Proof.
move/stableP => st; apply/card_le1_eqP => x y xS yS; apply/eqP/negPn/negP => xy.
by move: (st x y xS yS); rewrite /edge_rel /= eq_sym xy.
Qed.

Lemma g287_K4_alpha : α([set: 'K_4]) <= 1.
Proof. by rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ st]; exact: g287_Kn_stable. Qed.

Lemma g287_K4_two_connected : k_connected 'K_4 2.
Proof.
split; first by rewrite card_ord.
move=> S _ x y; rewrite !inE => /andP [xS _] /andP [yS _].
case: (eqVneq x y) => [-> | xy]; first exact: connect0.
apply: connect1; rewrite /preliminaries.restrict_mem /= !inE xS yS /=.
by rewrite /edge_rel /= xy.
Qed.

Lemma g287_K4_subcubic : subcubic 'K_4.
Proof.
move=> v; have p : N(v) \proper [set: 'K_4].
  apply/properP; split; first exact: subsetT.
  by exists v; [rewrite inE | rewrite in_opn /edge_rel /= eqxx].
by move: (proper_card p); rewrite cardsT card_ord.
Qed.

Definition g287_bb_with_triangles : Prop :=
  [/\ forall G : sgraph, k_connected G 2 -> subcubic G -> 8 * α([set: G]) < 3 * #|G| ->
        exists i : 'I_6, inhabited (G ≃ x287_bb_graph i),
      forall i : 'I_6,
        [/\ k_connected (x287_bb_graph i) 2, triangle_free (x287_bb_graph i), subcubic (x287_bb_graph i) &
            8 * α([set: x287_bb_graph i]) < 3 * #|x287_bb_graph i|] &
      forall i j : 'I_6, i != j -> ~ inhabited (x287_bb_graph i ≃ x287_bb_graph j)].

Definition g287_bb_ntt_claim : Prop :=
  ~ g287_bb_with_triangles /\
  (g287_bb_with_triangles -> bajnok_brinkmann_six_exceptional_graphs_statement).

Theorem g287_bb_not_trivially_true : g287_bb_ntt_claim.
Proof.
split; last by case=> h1 h2 h3; split=> // G c _ s a; exact: h1.
case=> h _ _.
have a : 8 * α([set: 'K_4]) < 3 * #|'K_4|.
  by rewrite card_ord; apply: leq_ltn_trans (leq_mul (leqnn 8) g287_K4_alpha) _.
have [i [iso]] := h _ g287_K4_two_connected g287_K4_subcubic a.
have := bij.card_bij iso; rewrite card_ord.
have [_ _ /(_ i) ->] := g287_helper_sanity.
by case: i {iso} => -[|[|[|[|[|[|n]]]]]].
Qed.
